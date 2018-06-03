use coq::checker::univ::{
    Huniv,
    SubstResult,
};
use coq::kernel::esubst::{Idx, IdxError, Lift, IdxResult};
use core::convert::TryFrom;
use ocaml::de::{ORef, Array};
use ocaml::values::{
    CoFix,
    Constr,
    Cst,
    Fix,
    Fix2,
    Ind,
    Instance,
    Name,
    PRec,
    PUniverses,
    Rctxt,
    RDecl,
    Sort,
    SortContents,
    SortFam,
    Univ,
};
use std::borrow::{Borrow, Cow};
use std::cell::Cell;
use std::option::{NoneError};
use std::sync::{Arc};
use util::nonzero::{NonZero};

#[derive(Clone,Copy)]
pub enum Info {
    Closed,
    Open,
    Unknown,
}

/// Exception raised if a variable lookup is out of range.
pub enum SubstError {
    LocalOccur,
    Idx(IdxError),
}

pub enum DecomposeError {
    Anomaly(String),
}

pub enum DecomposeNError {
    UserError(String),
}

pub struct Substituend<A> {
    info: Cell<Info>,
    it: A,
}

pub type Arity = (Vec<RDecl>, ORef<Sort>);

impl<A> Substituend<A> {
    pub fn make(c: A) -> Self {
        Substituend {
            info: Cell::new(Info::Unknown),
            it: c,
        }
    }
}

impl ::std::convert::From<IdxError> for SubstError {
    fn from(e: IdxError) -> Self {
        SubstError::Idx(e)
    }
}

impl<T> Substituend<T>
    where T: Borrow<Constr>,
{
    /// 1st : general case
    pub fn lift(&self, depth: Idx) -> IdxResult<Constr> {
        match self.info.get() {
            Info::Closed => Ok(self.it.borrow().clone()),
            Info::Open => self.it.borrow().lift(depth),
            Info::Unknown => {
                self.info.set(if self.it.borrow().closed0()? { Info::Closed } else { Info::Open });
                // Recursion is okay here since it can only loop once.
                self.lift(depth)
            },
        }
    }
}

/// Sorts

impl Sort {
    pub fn family_of(&self) -> SortFam {
        match *self {
            Sort::Prop(SortContents::Null) => SortFam::InProp,
            Sort::Prop(SortContents::Pos) => SortFam::InSet,
            Sort::Type(_) => SortFam::InType,
        }
    }
}

impl Univ {
    fn sort_of(&self) -> Sort {
        if self.is_type0m() { Sort::Prop(SortContents::Null) }
        else if self.is_type0() { Sort::Prop(SortContents::Pos) }
        else { Sort::Type(self.clone()) }
    }
}

impl Constr {
    /// Constructions as implemented

    pub fn strip_outer_cast(&self) -> &Self {
        let mut c = self;
        while let Constr::Cast(ref o) = *c {
            let (ref c_, _, _) = **o;
            c = c_;
        }
        c
    }

    /// Warning: returned argument order is reversed from the OCaml implementation!
    ///
    /// We could also consider a VecDeque, but we only ever append one way so it seems like a
    /// waste...
    pub fn collapse_appl<'a>(&'a self, cl: &'a [Self]) -> (&Self, Vec<&Self>) {
        // FIXME: Consider a non-allocating version that works as an intrusive iterator, or a
        // reversed iterator; both would suffice for our purposes here.
        let mut f = self;
        // Argument order is reversed, so extending to the right is prepending.
        let mut cl2: Vec<&Self> = cl.iter().collect();
        while let Constr::App(ref o) = *f.strip_outer_cast() {
            let (ref g, ref cl1) = **o;
            f = g;
            cl2.extend(cl1.iter().rev());
        }
        (f, cl2)
    }

    /// This method has arguments in the same order as the OCaml.
    pub fn decompose_app(&self) -> (&Self, Vec<&Self>) {
        if let Constr::App(ref o) = *self {
            let (ref f, ref cl) = **o;
            let (f, mut cl) = f.collapse_appl(cl);
            cl.reverse();
            (f, cl)
        } else {
            (self, Vec::new())
        }
    }

    pub fn applist(self, l: Vec<Constr>) -> Constr {
        Constr::App(ORef(Arc::from((self, Array(Arc::from(l))))))
    }

    /// Functions for dealing with Constr terms

    /// Occurring

    pub fn iter_with_binders<T, G, F, E>(&self, g: G, f: F, l: &T) -> Result<(), E>
        where
            T: Clone,
            G: Fn(&mut T) -> Result<(), E>,
            F: Fn(&Constr, &T) -> Result<(), E>,
    {
        Ok(match *self {
            Constr::Rel(_) | Constr::Sort(_) | Constr::Const(_) | Constr::Ind(_)
            | Constr::Construct(_) => (),
            Constr::Cast(ref o) => {
                let (ref c, _, ref t) = **o;
                f(c, l)?;
                f(t, l)?;
            },
            Constr::Prod(ref o) => {
                let (_, ref t, ref c) = **o;
                f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                f(c, &l)?;
            },
            Constr::Lambda(ref o) => {
                let (_, ref t, ref c) = **o;
                f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                f(c, &l)?;
            },
            Constr::LetIn(ref o) => {
                let (_, ref b, ref t, ref c) = **o;
                f(b, l)?;
                f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                f(c, &l)?;
            },
            Constr::App(ref o) => {
                let (ref c, ref al) = **o;
                f(c, l)?;
                for x in al.iter() {
                    f(x, l)?;
                }
            },
            // | Evar (e,al) -> Array.iter (f n) l,
            Constr::Case(ref o) => {
                let (_, ref p, ref c, ref bl) = **o;
                f(p, l)?;
                f(c, l)?;
                for x in bl.iter() {
                    f(x, l)?;
                }
            },
            Constr::Fix(ref o) => {
                let Fix(_, PRec(_, ref tl, ref bl)) = **o;
                let len = tl.len();
                for x in tl.iter() {
                    f(x, l)?;
                }
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                for x in bl.iter() {
                    f(x, &l)?;
                }
            },
            Constr::CoFix(ref o) => {
                let CoFix(_, PRec(_, ref tl, ref bl)) = **o;
                let len = tl.len();
                for x in tl.iter() {
                    f(x, l)?;
                }
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                for x in bl.iter() {
                    f(x, &l)?;
                }
            },
            Constr::Proj(ref o) => {
                let (_, ref c) = **o;
                f(c, l)?;
            },
            // Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) => unreachable!("")
        })
    }


    fn closed_rec(&self, n: &i64) -> Result<(), SubstError> {
        match *self {
            Constr::Rel(m) => if m > *n { Err(SubstError::LocalOccur) } else { Ok(()) },
            _ => self.iter_with_binders(|i| {
                *i = i.checked_add(1).ok_or(SubstError::Idx(IdxError::from(NoneError)))?;
                return Ok(())
            }, Self::closed_rec, n),
        }
    }

    /// (closedn n M) raises LocalOccur if a variable of height greater than n
    /// occurs in M, returns () otherwise
    pub fn closedn(&self, n: i64) -> IdxResult<bool> {
        match self.closed_rec(&n) {
            Ok(()) => Ok(true),
            Err(SubstError::LocalOccur) => Ok(false),
            Err(SubstError::Idx(e)) => Err(e),
        }
    }

    /// [closed0 M] is true iff [M] is a (deBruijn) closed term
    pub fn closed0(&self) -> IdxResult<bool> {
        self.closedn(0)
    }

    fn occur_rec(&self, n: &i64) -> Result<(), SubstError> {
        match *self {
            Constr::Rel(m) => if m == *n { Err(SubstError::LocalOccur) } else { Ok(()) },
            _ => self.iter_with_binders(|i| {
                *i = i.checked_add(1).ok_or(SubstError::Idx(IdxError::from(NoneError)))?;
                return Ok(())
            }, Self::occur_rec, n),
        }
    }

    /// (noccurn n M) returns true iff (Rel n) does NOT occur in term M
    pub fn noccurn(&self, n: i64) -> IdxResult<bool> {
        match self.occur_rec(&n) {
            Ok(()) => Ok(true),
            Err(SubstError::LocalOccur) => Ok(false),
            Err(SubstError::Idx(e)) => Err(e),
        }
    }

    fn occur_between_rec(&self, n: &i64, m: i64) -> Result<(), SubstError> {
        match *self {
            Constr::Rel(p) =>
                // p - *n is safe because *n ≤ p.
                if *n <= p && p - *n < m { Err(SubstError::LocalOccur) } else { Ok(()) },
            _ => self.iter_with_binders(|i| {
                *i = i.checked_add(1).ok_or(SubstError::Idx(IdxError::from(NoneError)))?;
                return Ok(())
            }, |c, n| c.occur_between_rec(n, m), n),
        }
    }

    /// (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
    /// for n <= p < n+m
    pub fn noccur_between(&self, n: i64, m: i64) -> IdxResult<bool> {
        match self.occur_between_rec(&n, m) {
            Ok(()) => Ok(true),
            Err(SubstError::LocalOccur) => Ok(false),
            Err(SubstError::Idx(e)) => Err(e),
        }
    }

    /* (* Checking function for terms containing existential variables.
     The function [noccur_with_meta] considers the fact that
     each existential variable (as well as each isevar)
     in the term appears applied to its local context,
     which may contain the CoFix variables. These occurrences of CoFix variables
     are not considered *)

    let noccur_with_meta n m term =
      let rec occur_rec n c = match c with
        | Rel p -> if n<=p && p<n+m then raise LocalOccur
        | App(f,cl) ->
        (match f with
               | (Cast (Meta _,_,_)| Meta _) -> ()
           | _ -> iter_constr_with_binders succ occur_rec n c)
        | Evar (_, _) -> ()
        | _ -> iter_constr_with_binders succ occur_rec n c
      in
      try (occur_rec n term; true) with LocalOccur -> false */

    /// Lifting
    pub fn map_constr_with_binders<T, G, F, E>(&self, g: G, f: F, l: &T) -> Result<Constr, E>
        where
            T: Clone,
            G: Fn(&mut T) -> Result<(), E>,
            F: Fn(&Constr, &T) -> Result<Constr, E>,
    {
        Ok(match *self {
            Constr::Rel(_) | Constr::Sort(_) | Constr::Const(_) | Constr::Ind(_)
            | Constr::Construct(_) => self.clone(),
            Constr::Cast(ref o) => {
                let (ref c, k, ref t) = **o;
                let c = f(c, l)?;
                let t = f(t, l)?;
                Constr::Cast(ORef(Arc::from((c, k, t))))
            },
            Constr::Prod(ref o) => {
                let (ref na, ref t, ref c) = **o;
                let t = f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                let c = f(c, &l)?;
                Constr::Prod(ORef(Arc::from((na.clone(), t, c))))
            },
            Constr::Lambda(ref o) => {
                let (ref na, ref t, ref c) = **o;
                let t = f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                let c = f(c, &l)?;
                Constr::Lambda(ORef(Arc::from((na.clone(), t, c))))
            },
            Constr::LetIn(ref o) => {
                let (ref na, ref b, ref t, ref c) = **o;
                let b = f(b, l)?;
                let t = f(t, l)?;
                let mut l = l.clone(); // expensive
                g(&mut l)?;
                let c = f(c, &l)?;
                Constr::LetIn(ORef(Arc::from((na.clone(), b, t, c))))
            },
            Constr::App(ref o) => {
                let (ref c, ref al) = **o;
                let c = f(c, l)?;
                // expensive -- allocates a Vec
                let al: Result<Vec<_>, _> = al.iter().map( |x| f(x, l) ).collect();
                Constr::App(ORef(Arc::from((c, Array(Arc::from(al?))))))
            },
            // | Evar (e,al) -> Evar (e, Array.map (f l) al)
            Constr::Case(ref o) => {
                let (ref ci, ref p, ref c, ref bl) = **o;
                let p = f(p, l)?;
                let c = f(c, l)?;
                // expensive -- allocates a Vec
                let bl: Result<Vec<_>, _> = bl.iter().map( |x| f(x, l) ).collect();
                Constr::Case(ORef(Arc::from((ci.clone(), p, c, Array(Arc::from(bl?))))))
            },
            Constr::Fix(ref o) => {
                let Fix(ref ln, PRec(ref lna, ref tl, ref bl)) = **o;
                let len = tl.len();
                // expensive -- allocates a Vec
                let tl: Result<Vec<_>, _> = tl.iter().map( |x| f(x, l) ).collect();
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                // expensive -- allocates a Vec
                let bl: Result<Vec<_>, _> = bl.iter().map( |x| f(x, &l) ).collect();
                Constr::Fix(ORef(Arc::from(Fix(ln.clone(),
                                              PRec(lna.clone(),
                                                   Array(Arc::from(tl?)),
                                                   Array(Arc::from(bl?)))))))
            },
            Constr::CoFix(ref o) => {
                let CoFix(ln, PRec(ref lna, ref tl, ref bl)) = **o;
                let len = tl.len();
                // expensive -- allocates a Vec
                let tl: Result<Vec<_>, _> = tl.iter().map( |x| f(x, l) ).collect();
                let mut l = l.clone(); // expensive
                for _ in 0..len {
                    g(&mut l)?;
                }
                // expensive -- allocates a Vec
                let bl: Result<Vec<_>, _> = bl.iter().map( |x| f(x, &l) ).collect();
                Constr::CoFix(ORef(Arc::from(CoFix(ln.clone(),
                                                  PRec(lna.clone(),
                                                       Array(Arc::from(tl?)),
                                                       Array(Arc::from(bl?)))))))
            },
            Constr::Proj(ref o) => {
                let (ref p, ref c) = **o;
                let c = f(c, l)?;
                Constr::Proj(ORef(Arc::from((p.clone(), c))))
            },
            // Constr::Meta(_) | Constr::Var(_) | Constr::Evar(_) => unreachable!("")
        })
    }

    /// The generic lifting function
    pub fn exliftn(&self, el: &Lift) -> IdxResult<Constr> {
        match *self {
            Constr::Rel(i) =>
                Ok(Constr::Rel(i32::from(el.reloc_rel(Idx::try_new(NonZero::new(i)?)?)?) as i64)),
            _ => self.map_constr_with_binders(Lift::lift, Self::exliftn, el)
        }
    }

    /// Lifting the binding depth across k bindings

    pub fn liftn(&self, k: Idx, n: Idx) -> IdxResult<Constr> {
        let mut el = Lift::id();
        el.shift(k)?;
        if let Some(n) = n.checked_sub(Idx::ONE).expect("n > 0 - 1 ≥ 0") {
            el.liftn(n)?;
        }
        if el.is_id() {
            Ok(self.clone())
        } else {
            self.exliftn(&el)
        }
    }

    pub fn lift(&self, k: Idx) -> IdxResult<Constr> {
        self.liftn(k, Idx::ONE)
    }

    /// Substituting

    fn substrec<T>(&self,
                   &(depth, ref lamv): &(Option<Idx>, &[Substituend<T>])) -> IdxResult<Constr>
        where
            T: Borrow<Constr>,
    {
        match *self {
            Constr::Rel(k_) => {
                // FIXME: For below, ensure u32 to usize is always a valid cast.
                let d = depth.map(u32::from).unwrap_or(0) as usize;
                // NOTE: This can only fail if we compile with addresses under 64 bits.
                let k = usize::try_from(k_)?;
                // After the above, we know k is a valid non-negative i64.
                if k <= d {
                    Ok(self.clone())
                } else if let Some(sub) = lamv.get(k - d - 1) {
                    // Note that k - d above is valid (and > 0) because 0 ≤ d < k;
                    // therefore, 0 ≤ k - depth - 1, so that is valid.
                    // Also, the unwrap() below is granted because 0 < k.
                    // FIXME: There is a better way of dealing with this.
                    sub.borrow().lift(depth.unwrap())
                } else {
                    // k - lamv.len() is valid (and > 0) because if lamv.get(k - d - 1) = None,
                    // lamv.len() ≤ k - d - 1 < k - d ≤ k (i.e. lamv.len() < k), so
                    // 0 < k - lamv.len() (k - lamv.len() is positive).
                    // Additionally, since we know 0 < lamv.len() < k, and k is a valid positive
                    // i64, lamv.len() is also a valid positive i64.
                    // So the cast is valid.
                    Ok(Constr::Rel(k_ - lamv.len() as i64))
                }
            },
            _ => self.map_constr_with_binders(
                |&mut (ref mut depth, _)| {
                    *depth = match *depth {
                        None => Some(Idx::ONE),
                        Some(depth) => Some(depth.checked_add(Idx::ONE)?),
                    };
                    Ok(())
                },
                Self::substrec,
                &(depth, lamv)
            )
        }
    }

    /// (subst1 M c) substitutes M for Rel(1) in c
    /// we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
    /// M1,...,Mn for respectively Rel(1),...,Rel(n) in c
    pub fn substn_many<T>(&self, lamv: &[Substituend<T>], n: Option<Idx>) -> IdxResult<Constr>
        where
            T: Borrow<Constr>,
    {
        let lv = lamv.len();
        if lv == 0 { return Ok(self.clone()) }
        else { self.substrec(&(n, lamv)) }
    }

    pub fn substnl<T, C>(&self, laml: C, n: Option<Idx>) -> IdxResult<Constr>
        where
            C: IntoIterator<Item=T>,
            T: Borrow<Constr>,
    {
        let lamv: Vec<_> = laml.into_iter().map( |i| Substituend::make(i) ).collect();
        self.substn_many(&lamv, n)
    }

    pub fn substl<T, C>(&self, laml: C) -> IdxResult<Constr>
        where
            C: IntoIterator<Item=T>,
            T: Borrow<Constr>,
    {
        self.substnl(laml, None)
    }

    pub fn subst1(&self, lam: &Constr) -> IdxResult<Constr> {
        let lamv = [Substituend::make(lam)];
        self.substn_many(&lamv, None)
    }

    /// Iterate lambda abstractions

    /* /// compose_lam [x1:T1;..;xn:Tn] b = [x1:T1]..[xn:Tn]b
    pub fn compose_lam<I>(&self, l: I)
        where I: Iterator<Elem=&ORef<(Name, Constr, Constr)>> {
    } */
    /* val decompose_lam : constr -> (name * constr) list * constr */
    /*
    let compose_lam l b =
      let rec lamrec = function
        | ([], b)       -> b
        | ((v,t)::l, b) -> lamrec (l, Lambda (v,t,b))
      in
      lamrec (l,b) */

    /// Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
    /// ([(x1,T1);...;(xn,Tn)],T), where T is not a lambda
    ///
    /// (For technical reasons, we carry around the nested constructor as well, but we never need
    /// it).
    pub fn decompose_lam(&self) -> (Vec<&ORef<(Name, Constr, Constr)>>, &Constr) {
        let mut l = Vec::new();
        let mut c = self;
        loop {
            match *c {
                Constr::Lambda(ref o) => {
                    let (/*ref x, ref t*/_, _, ref c_) = **o;
                    /* l.push((x, t)); */
                    l.push(o);
                    c = c_;
                },
                Constr::Cast(ref o) => {
                    let (ref c_, _, _) = **o;
                    c = c_;
                },
                _ => {
                    return (l, c)
                }
            }
        }
    }

    /// Iterate products, with or without lets

    /// Constructs either [(x:t)c] or [[x=b:t]c]
    pub fn mk_prod_or_let_in(self, decl: RDecl) -> Constr {
        match decl {
            RDecl::LocalAssum(na, t) => Constr::Prod(ORef(Arc::from((na, t, self)))),
            RDecl::LocalDef(na, b, t) =>
                Constr::LetIn(ORef(Arc::from((na, b, (*t).clone(), self)))),
        }
    }

    pub fn it_mk_prod_or_let_in<I, F, T, E>(self, ctx: I, mut to_owned: F) -> Result<Constr, E>
        where
            I: Iterator<Item=Result<T, E>>,
            F: FnMut(T) -> RDecl,
    {
        let mut c = self;
        for d in ctx {
            c = c.mk_prod_or_let_in(to_owned(d?));
        }
        Ok(c)
    }

    /// NOTE: The Vec<RDecl> is reversed from the Rctxt that would have been returned
    /// by OCaml.
    pub fn decompose_prod_assum(&self) -> (Vec<RDecl>, &Constr) {
        // TODO: For these sorts of generated definition sets, we don't
        // really need to perform clone() on the Constrs, since they can
        // be used by reference.
        let mut l = Vec::new();
        let mut c = self;
        loop {
            match *c {
                Constr::Prod(ref o) => {
                    let (ref x, ref t, ref c_) = **o;
                    l.push(RDecl::LocalAssum(x.clone(), t.clone()));
                    c = c_;
                },
                Constr::LetIn(ref o) => {
                    let (ref x, ref b, ref t, ref c_) = **o;
                    l.push(RDecl::LocalDef(x.clone(), b.clone(), ORef(Arc::from(t.clone()))));
                    c = c_;
                },
                Constr::Cast(ref o) => {
                    let (ref c_, _, _) = **o;
                    c = c_;
                },
                _ => return (l, c),
            }
        }
    }

    /// NOTE: The Vec<RDecl> is reversed from the Rctxt that would have been returned by OCaml.
    pub fn decompose_prod_n_assum(&self,
                                  n: usize) -> Result<(Vec<RDecl>, &Constr), DecomposeNError> {
        // TODO: For these sorts of generated definition sets, we don't
        // really need to perform clone() on the Constrs, since they can
        // be used by reference.
        let mut l = Vec::new();
        let mut c = self;
        for _ in 0..n {
            match *c {
                Constr::Prod(ref o) => {
                    let (ref x, ref t, ref c_) = **o;
                    l.push(RDecl::LocalAssum(x.clone(), t.clone()));
                    c = c_;
                },
                Constr::LetIn(ref o) => {
                    let (ref x, ref b, ref t, ref c_) = **o;
                    l.push(RDecl::LocalDef(x.clone(), b.clone(), ORef(Arc::from(t.clone()))));
                    c = c_;
                },
                Constr::Cast(ref o) => {
                    let (ref c_, _, _) = **o;
                    c = c_;
                },
                _ => {
                    const ERR : &'static str = "decompose_prod_n_assum: not enough assumptions";
                    return Err(DecomposeNError::UserError(ERR.into()))
                },
            }
        }
        Ok((l, c))
    }

    /// Other term constructors

    pub fn mk_arity<'a, I, F, T, E>(sign: I, s: Sort, to_owned: F) -> Result<Constr, E>
        where
            I: Iterator<Item=Result<T, E>>,
            F: FnMut(T) -> RDecl,
    {
        // FIXME: It seems silly to allocate this here...
        Constr::Sort(ORef(Arc::from(s))).it_mk_prod_or_let_in(sign, to_owned)
    }

    /// NOTE: The Vec<RDecl> is reversed from the Rctxt that would have been returned
    /// by OCaml.
    pub fn dest_arity(&self) -> Result<(Vec<RDecl>, &Sort), DecomposeError> {
        let (l, c) = self.decompose_prod_assum();
        if let Constr::Sort(ref s) = *c { Ok((l, s)) }
        else { Err(DecomposeError::Anomaly("destArity: not an arity".into())) }
    }

    /// Alpha conversion functions

    /// alpha conversion : ignore print names and casts
    pub fn compare<F>(&self, t2: &Self, f: F) -> bool
        where F: Fn(&Self, &Self) -> bool,
    {
        // FIXME: This is (in some cases) unnecessarily tail recursive.  We could reduce the amount
        // of recursion required (and the likelihood that we'll get a stack overflow) by making the
        // function slightly less generic.
        match (self, t2) {
            (&Constr::Rel(n1), &Constr::Rel(n2)) => n1 == n2,
            // | Meta m1, Meta m2 -> Int.equal m1 m2
            // | Var id1, Var id2 -> Id.equal id1 id2
            (&Constr::Sort(ref s1), &Constr::Sort(ref s2)) => s1.compare(s2),
            (&Constr::Cast(ref o1), _) => {
                let (ref c1, _, _) = **o1;
                f(c1, t2)
            },
            (_, &Constr::Cast(ref o2)) => {
                let (ref c2, _, _) = **o2;
                f(self, c2)
            },
            (&Constr::Prod(ref o1), &Constr::Prod(ref o2)) => {
                let (_, ref t1, ref c1) = **o1;
                let (_, ref t2, ref c2) = **o2;
                f(t1, t2) && f(c1, c2)
            },
            (&Constr::Lambda(ref o1), &Constr::Lambda(ref o2)) => {
                let (_, ref t1, ref c1) = **o1;
                let (_, ref t2, ref c2) = **o2;
                f(t1, t2) && f(c1, c2)
            },
            (&Constr::LetIn(ref o1), &Constr::LetIn(ref o2)) => {
                let (_, ref b1, ref t1, ref c1) = **o1;
                let (_, ref b2, ref t2, ref c2) = **o2;
                f(b1, b2) && f(t1, t2) && f(c1, c2)
            },
            (&Constr::App(ref o1), &Constr::App(ref o2)) => {
                let (ref c1, ref l1) = **o1;
                let (ref c2, ref l2) = **o2;
                if l1.len() == l2.len() {
                    f(c1, c2) && l1.iter().zip(l2.iter()).all( |(x, y)| f(x, y) )
                } else {
                    // It's really sad that we have to allocate to perform this equality check in
                    // linear time...
                    // (we actually shouldn't, since we should be able to modify the nodes in-place
                    // in order to reuse the existing memory, but fixing this might be more trouble
                    // than it's worth).
                    // FIXME: Alternative: a reversed iterator may be doable quite efficiently
                    // (without allocating), especially since we don't really need to go in forward
                    // order to do equality checks...
                    let (h1, l1) = c1.collapse_appl(&***l1);
                    let (h2, l2) = c2.collapse_appl(&***l2);
                    // We currently check in the opposite order from the OCaml, since we use the
                    // reversed method.  This shouldn't matter in terms of results, but it might
                    // affect performance... we could also iterate in reverse.
                    if l1.len() == l2.len() {
                        f(h1, h2) && l1.iter().zip(l2.iter()).all( |(x, y)| f(x, y) )
                    } else { false }
                }
            },
            // | Evar (e1,l1), Evar (e2,l2) -> Int.equal e1 e2 && Array.equal f l1 l2
            (&Constr::Const(ref o1), &Constr::Const(ref o2)) => {
                let ref c1 = **o1;
                let ref c2 = **o2;
                c1.eq(c2, Cst::eq_con_chk)
            },
            (&Constr::Ind(ref c1), &Constr::Ind(ref c2)) => c1.eq(c2, Ind::eq_chk),
            (&Constr::Construct(ref o1), &Constr::Construct(ref o2)) => {
                let PUniverses(ref i1, ref u1) = **o1;
                let PUniverses(ref i2, ref u2) = **o2;
                i1.idx == i2.idx && i1.ind.eq_chk(&i2.ind) && u1.equal(u2)
            },
            (&Constr::Case(ref o1), &Constr::Case(ref o2)) => {
                let (_, ref p1, ref c1, ref bl1) = **o1;
                let (_, ref p2, ref c2, ref bl2) = **o2;
                f(p1, p2) && f(c1, c2) &&
                bl1.len() == bl2.len() && bl1.iter().zip(bl2.iter()).all( |(x, y)| f(x, y))
            },
            (&Constr::Fix(ref o1), &Constr::Fix(ref o2)) => {
                let Fix(Fix2(ref ln1, i1), PRec(_, ref tl1, ref bl1)) = **o1;
                let Fix(Fix2(ref ln2, i2), PRec(_, ref tl2, ref bl2)) = **o2;
                i1 == i2 &&
                ln1.len() == ln2.len() && ln1.iter().zip(ln2.iter()).all( |(x, y)| x == y) &&
                tl1.len() == tl2.len() && tl1.iter().zip(tl2.iter()).all( |(x, y)| f(x, y) ) &&
                bl1.len() == bl2.len() && bl1.iter().zip(bl2.iter()).all( |(x, y)| f(x, y) )
            },
            (&Constr::CoFix(ref o1), &Constr::CoFix(ref o2)) => {
                let CoFix(ln1, PRec(_, ref tl1, ref bl1)) = **o1;
                let CoFix(ln2, PRec(_, ref tl2, ref bl2)) = **o2;
                ln1 == ln2 &&
                tl1.len() == tl2.len() && tl1.iter().zip(tl2.iter()).all( |(x, y)| f(x, y) ) &&
                bl1.len() == bl2.len() && bl1.iter().zip(bl2.iter()).all( |(x, y)| f(x, y) )
            },
            (&Constr::Proj(ref o1), &Constr::Proj(ref o2)) => {
                let (ref p1, ref c1) = **o1;
                let (ref p2, ref c2) = **o2;
                p1.equal(p2) && f(c1, c2)
            },
            (_, _) => false,
        }
    }

    pub fn eq(&self, n: &Self) -> bool {
        self as *const _ == n as *const _ ||
        self.compare(n, Self::eq)
    }

    /// Universe substitutions
    pub fn subst_instance(&self, subst: &Instance, tbl: &Huniv) -> SubstResult<Cow<Constr>>
    {
        if subst.is_empty() { Ok(Cow::Borrowed(self)) }
        else {
            // FIXME: We needlessly allocate in this function even if there were no changes,
            // due to the signature of map_constr_with_binders (and then waste time deallocating
            // all the stuff we just built after it's done).  We could get away with not
            // performing any cloning etc. until we actually change something.
            fn aux(t: &Constr, env: &(&Instance, &Huniv, &Cell<bool>)) -> SubstResult<Constr> {
                let (subst, tbl, ref changed) = *env;
                let f = |u: &Instance| u.subst_instance(subst);
                match *t {
                    Constr::Const(ref o) => {
                        let PUniverses(ref c, ref u) = **o;
                        return Ok(
                            if u.is_empty() { t.clone() }
                            else {
                                let u_ = f(u)?;
                                if &**u_ as *const _ == &***u as *const _ { t.clone() }
                                else {
                                    changed.set(true);
                                    Constr::Const(ORef(Arc::from(PUniverses(c.clone(),
                                                                            u_))))
                                }
                            }
                        )
                    },
                    Constr::Ind(ref o) => {
                        let PUniverses(ref i, ref u) = **o;
                        return Ok(
                            if u.is_empty() { t.clone() }
                            else {
                                let u_ = f(u)?;
                                if &**u_ as *const _ == &***u as *const _ { t.clone() }
                                else {
                                    changed.set(true);
                                    Constr::Ind(ORef(Arc::from(PUniverses(i.clone(),
                                                                          u_))))
                                }
                            }
                        )
                    },
                    Constr::Construct(ref o) => {
                        let PUniverses(ref c, ref u) = **o;
                        return Ok(
                            if u.is_empty() { t.clone() }
                            else {
                                let u_ = f(u)?;
                                if &**u_ as *const _ == &***u as *const _ { t.clone() }
                                else {
                                    changed.set(true);
                                    Constr::Construct(ORef(Arc::from(PUniverses(c.clone(),
                                                                                u_))))
                                }
                            }
                        )
                    },
                    Constr::Sort(ref o) => {
                        if let Sort::Type(ref u) = **o {
                            return Ok({
                                let u_ = u.subst_instance(subst, tbl)?;
                                if u_.hequal(u) { t.clone() }
                                else {
                                    changed.set(true);
                                    Constr::Sort(ORef(Arc::new(u_.sort_of())))
                                }
                            })
                        }
                    },
                    _ => {}
                }
                t.map_constr_with_binders( |_| Ok(()), aux, env)
            }
            let changed = Cell::new(false);
            let c_ = aux(self, &(subst, tbl, &changed))?;
            Ok(if changed.get() { Cow::Owned(c_) } else { Cow::Borrowed(self) })
        }
    }
}

/// Type of assumptions and contexts

impl RDecl {
    pub fn map<F, E>(&self, f: F) -> Result<Cow<RDecl>, E>
        where
            F: for <'a> Fn(&'a Constr) -> Result<Cow<'a, Constr>, E>,
    {
        Ok(match *self {
            RDecl::LocalAssum(ref n, ref typ) => match f(typ)? {
                Cow::Borrowed(typ_) if typ as *const _ == typ_ as *const _ => Cow::Borrowed(self),
                typ_ => Cow::Owned(RDecl::LocalAssum(n.clone(), typ_.into_owned())),
            },
            RDecl::LocalDef(ref n, ref body, ref typ) => match (f(body)?, f(typ)?) {
                (Cow::Borrowed(body_), Cow::Borrowed(typ_))
                if body as *const _ == body_ as *const _ && &**typ as *const _ == typ_ as *const _
                    => Cow::Borrowed(self),
                (body_, typ_) => Cow::Owned(RDecl::LocalDef(n.clone(),
                                            body_.into_owned(),
                                            ORef(Arc::from(typ_.into_owned())))),
            },
        })
    }
}

impl Rctxt {
    /// Differs from the OCaml implementation because it also returns the length.
    pub fn nhyps(&self) -> (usize, usize) {
        let mut nhyps = 0;
        let mut len = 0;
        // NOTE: All additions are in-bounds because (provided the list is not recursive,
        // in which case this function will never terminate), each element of the list
        // takes up at least a byte (actually, a word or more), so the total length of
        // all of the elements cannot exceed usize.
        for hyp in self.iter() {
            if let RDecl::LocalAssum(_, _) = *hyp { nhyps += 1; }
            len += 1;
        }
        (len, nhyps)
    }

    /// NOTE: We change the definition compared to OCaml; instead of a SmartMap,
    /// this just returns an iterator.
    ///
    /// NOTE: This will return RDecls in the usual Rctxt order, *not* reversed order.
    pub fn subst_instance<'a, 'b>(&'a self, s: &'a Instance, tbl: &'a Huniv) ->
        impl Iterator<Item=SubstResult<Cow<'a, RDecl>>>
    {
        self.iter().map( move |d| d.map( |x| x.subst_instance(s, tbl) ) )
    }
}

/// NOTE: Differs from the OCaml implementation because it returns the
/// total number of hypotheses.
pub fn extended_rel_list<'a, I>(hyps: I) -> IdxResult<(Vec<Constr>, Option<Idx>)>
    where
        I: Iterator<Item=&'a RDecl>
{
    let mut l = Vec::new();
    // All the ids we generate here will be valid Idxs (though this alone doesn't ensure that
    // during reduction we don't generate invalid Idxs, it's at least a nice sanity check).
    // TODO: We can skip most of the checks here since we know the maximum length of hyps ahead
    // of time.
    let mut p = Idx::ONE;
    for h in hyps {
        if let RDecl::LocalAssum(_, _) = *h {
           // i32 is always valid to cast to i64
           l.push(Constr::Rel(i32::from(p) as i64));
        }
        p = p.checked_add(Idx::ONE)?;
    }
    // TODO: Figure out whether reversing here is really necessary, or we can do something else
    // (like iterate in reverse order in the loop).
    l.reverse();
    // Subtracting 1 from p always returns either a positive (valid) Some(Idx) or None, because
    // a positive i32 (a valid Idx) - 1 is always a non-negative i32 (a valid non-negative Idx).
    // Therefore, the expect() is safe.
    Ok((l, p.checked_sub(Idx::ONE).expect("positive i32 - 1 = non-negative i32")))
}

impl Sort {
    fn compare(&self, s2: &Self) -> bool {
        match (self, s2) {
            (&Sort::Prop(c1), &Sort::Prop(c2)) => {
                match (c1, c2) {
                    (SortContents::Pos, SortContents::Pos) |
                    (SortContents::Null, SortContents::Null) => true,
                    (SortContents::Pos, SortContents::Null) => false,
                    (SortContents::Null, SortContents::Pos) => false,
                }
            },
            (&Sort::Type(ref u1), &Sort::Type(ref u2)) => u1.equal(u2),
            (&Sort::Prop(_), &Sort::Type(_)) => false,
            (&Sort::Type(_), &Sort::Prop(_)) => false,
        }
    }
}

impl<T> PUniverses<T> {
    fn eq<F>(&self, &PUniverses(ref c2, ref u2): &Self, f: F) -> bool
        where F: Fn(&T, &T) -> bool,
    {
        let PUniverses(ref c1, ref u1) = *self;
        u1.equal(u2) && f(c1, c2)
    }
}
