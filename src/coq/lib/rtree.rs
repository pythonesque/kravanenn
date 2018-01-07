use bit_set::BitSet;
use coq::kernel::esubst::{
    IdxError,
    IdxResult,
};
use core::convert::{TryFrom};
use ocaml::values::{
    Int,
    RTree,
};
use std::cmp::{Ord, Ordering};
use std::option::{NoneError};

pub enum RTreeError {
    Idx(IdxError),
    Failure(String),
    OutOfBounds,
}

/// Immutable, singly linked, non-owning list.
/// TODO: Figure out why I can't find this on crates.io... this is a really basic abstraction.
#[derive(Debug)]
enum List<'a, T> where T: 'a {
    Nil,
    Cons(&'a (T, List<'a, T>)),
}

impl<'a, T> Copy for List<'a, T> {}

impl<'a, T> Clone for List<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T> Iterator for List<'a, T> {
    type Item = &'a T;

    // Note: if there were a cycle (which there shouldn't be) in the original List,
    // this could loop forever.  But if used as intended (from a DeserializeSeed), this is unlikely
    // to happen, since DeserializeSeed will already loop forever in that case...
    fn next(&mut self) -> Option<&'a T> {
        match *self {
            List::Cons(&(ref v, next)) => {
                *self = next;
                Some(v)
            },
            List::Nil => None,
        }
    }
}

pub type RTreeResult<T> = Result<T, RTreeError>;

impl ::std::convert::From<IdxError> for RTreeError {
    fn from(e: IdxError) -> Self {
        RTreeError::Idx(e)
    }
}

impl<T> RTree<T> {
    /// Building trees

    /// Build mutually recursive trees:
    ///
    /// ```
    /// X_1 = f_1(X_1,..,X_n) ... X_n = f_n(X_1,..,X_n)
    /// ```
    ///
    /// is obtained by the following pseudo-code
    ///
    /// ```
    /// let vx = mk_rec_calls n in
    ///  let [|x_1;..;x_n|] =
    ///     mk_rec[|f_1(vx.(0),..,vx.(n-1);..;f_n(vx.(0),..,vx.(n-1))|]
    /// ```
    ///
    /// First example: build  rec X = a(X,Y) and Y = b(X,Y,Y)
    ///
    /// ```
    /// let [|vx;vy|] = mk_rec_calls 2 in
    /// let [|x;y|] = mk_rec [|mk_node a [|vx;vy|]; mk_node b [|vx;vy;vy|]|]
    /// ```
    ///
    /// Another example: nested recursive trees rec Y = b(rec X = a(X,Y),Y,Y)
    ///
    /// ```let [|vy|] = mk_rec_calls 1 in
    /// let [|vx|] = mk_rec_calls 1 in
    /// let [|x|] = mk_rec[|mk_node a vx;lift 1 vy|]
    /// let [|y|] = mk_rec[|mk_node b x;vy;vy|]```
    ///
    /// (note the lift to avoid)
    pub fn mk_rec_calls(i: Int) -> Vec<RTree<T>> {
        (0..i).map( |j| RTree::Param(0, j) ).collect()
    }

    pub fn mk_node(lab: T, sons: Vec<Self>) -> Self {
        RTree::Node(lab, sons)
    }

    /// The usual lift operation
    fn lift_rec(&mut self, depth: Int, n: Int) -> IdxResult<()> {
        Ok(match *self {
            RTree::Param(ref mut i, _) =>
                if depth < *i { *i = i.checked_add(n).ok_or(IdxError::from(NoneError))?; },
            RTree::Node(_, ref mut sons) => for son in sons { son.lift_rec(depth, n)? },
            RTree::Rec(_, ref mut defs) => {
                let depth = depth.checked_add(1).ok_or(IdxError::from(NoneError))?;
                for def in defs { def.lift_rec(depth, n)? }
            },
        })
    }

    /// [lift k t] increases of [k] the free parameters of [t]. Needed
    /// to avoid captures when a tree appears under [mk_rec]
    pub fn lift(&mut self, n: Int) -> IdxResult<()> {
        if n == 0 { Ok(()) } else { self.lift_rec(0, n) }
    }

    /// The usual subst operation
    ///
    /// NOTE: This isn't a very efficient implementation (it uses ownership instead of GC).  Needs
    /// benchmarking, it might be better to just go with the original implementation (there may be
    /// a clever hybrid that is better than either, but then we'd have to convert over from the
    /// OCaml structure).
    fn subst_rec(&mut self, depth: Int, sub: &[Self]) -> IdxResult<()> where T: Clone {
        let j = match *self {
            RTree::Param(ref mut i, j) => match (*i).cmp(&depth) {
                Ordering::Less => return Ok(()),
                Ordering::Equal => j,
                Ordering::Greater => {
                    *i = i.checked_sub(1).ok_or(IdxError::from(NoneError))?; return Ok(())
                },
            },
            RTree::Node(_, ref mut sons) => {
                for son in sons { son.subst_rec(depth, sub)? }; return Ok(())
            },
            RTree::Rec(_, ref mut defs) => {
                let depth = depth.checked_add(1).ok_or(IdxError::from(NoneError))?;
                for def in defs { def.subst_rec(depth, sub)? };
                return Ok(())
            },
        };
        // FIXME: expensive
        *self = RTree::Rec(j, sub.to_vec());
        self.lift(depth)
    }

    fn subst_rtree(&mut self, sub: &[Self]) -> IdxResult<()> where T: Clone {
        self.subst_rec(0, sub)
    }

    /// To avoid looping, we must check that every body introduces a node
    /// or a parameter.
    ///
    /// If the expansion does not succeed, returns Ok(None) (strictly speaking it would be a more
    /// accurate signature if it returned Option<Result<_, _>> instead of Result<Option<_>, _>,
    /// but that makes error handling more annoying inside the function).
    fn expand(&self) -> RTreeResult<Option<Self>> where T: Clone {
        if let RTree::Rec(j, ref defs) = *self {
            // FIXME: Differentiate between negative vs. positive overflow.
            let j = usize::try_from(j).map_err(IdxError::from)?;
            // FIXME: expensive
            let mut def = defs.get(j).ok_or(RTreeError::OutOfBounds)?.clone();
            def.subst_rtree(defs)?;
            loop {
                def = if let RTree::Rec(j, ref defs) = def {
                    // FIXME: Differentiate between negative vs. positive overflow.
                    let j = usize::try_from(j).map_err(IdxError::from)?;
                    // FIXME: expensive
                    let mut def = defs.get(j).ok_or(RTreeError::OutOfBounds)?.clone();
                    def.subst_rtree(defs)?;
                    def
                } else { break }
            }
            Ok(Some(def))
        } else { Ok(None) }
    }


    /// Given a vector of n bodies, builds the n mutual recursive trees.
    /// Recursive calls are made with parameters (0,0) to (0,n-1). We check
    /// the bodies actually build something by checking it is not
    /// directly one of the parameters of depth 0. Some care is taken to
    /// accept definitions like  rec X=Y and Y=f(X,Y)
    pub fn mk_rec(defs: &[Self]) -> RTreeResult<Vec<Self>> where T: Clone {
        let mut new_defs = Vec::with_capacity(defs.len());
        for (i, mut d) in defs.into_iter().enumerate() {
            let mut histo = BitSet::new();
            histo.insert(i);
            loop {
                let d_ = d.expand()?;
                if let RTree::Param(0, j) = *d_.as_ref().unwrap_or(&d) {
                    // FIXME: Differentiate between negative vs. positive overflow.
                    let j = usize::try_from(j).map_err(IdxError::from)?;
                    if !histo.insert(j) { // returns false if j was *already* in histo
                        return Err(RTreeError::Failure("invalid rec call".into()))
                    }
                    d = defs.get(j).ok_or(RTreeError::OutOfBounds)?;
                } else { break }
            }
            // NOTE: This cast is valid because vectors always take up at most isize::MAX bytes,
            // and Self has size ≥ 1 byte.  So i as isize is valid.  isize to i64 is always valid,
            // so we are done.
            // FIXME: Verify that isize to i64 is always a valid cast.
            // FIXME: expensive
            new_defs.push(RTree::Rec(i as i64, defs.to_vec()))
        }
        Ok(new_defs)
    }

    /// Structural equality test, parametrized by an equality on elements
    fn raw_eq<F>(&self, t_: &Self, cmp: &mut F) -> bool
        where
            F: FnMut(&T, &T) -> bool,
    {
        match (self, t_) {
            (&RTree::Param(i, j), &RTree::Param(i_, j_)) => i == i_ && j == j_,
            (&RTree::Node(ref x, ref a), &RTree::Node(ref x_, ref a_)) =>
                cmp(x, x_) && a.len() == a_.len() &&
                a.into_iter().zip(a_).all( |(t, t_)| t.raw_eq(t_, cmp)),
            (&RTree::Rec(i, ref a), &RTree::Rec(i_, ref a_)) =>
                i == i_ && a.len() == a_.len() &&
                a.into_iter().zip(a_).all( |(t, t_)| t.raw_eq(t_, cmp)),
            (_, _) => false,
        }
    }

    fn raw_eq2<F>((t, u): (&Self, &Self), (t_, u_): (&Self, &Self), cmp: &mut F) -> bool
        where
             F: FnMut(&T, &T) -> bool,
    {
        t.raw_eq(t_, cmp) && u.raw_eq(u_, cmp)
    }

    /// Equivalence test on expanded trees. It is parametrized by two
    /// equalities on elements:
    ///
    /// *  `cmp` is used when checking for already seen trees
    /// *  `cmp_` is used when comparing node labels.
    pub fn equiv<F, F_>(&self, t_: &Self, mut cmp: F, mut cmp_: F_) -> RTreeResult<bool>
        where
            T: Clone,
            F: FnMut(&T, &T) -> bool,
            F_: FnMut(&T, &T) -> bool,
    {
        fn compare<'a, T, F, F_>(histo: List<(&'a RTree<T>, &'a RTree<T>)>,
                                 t: &'a RTree<T>, t_: &'a RTree<T>,
                                 cmp: &mut F, cmp_: &mut F_) -> RTreeResult<bool>
            where
                T: Clone,
                F: FnMut(&T, &T) -> bool,
                F_: FnMut(&T, &T) -> bool,
        {
            let histo_ = &((t, t_), histo);
            // NOTE: A linked list shouln't really be necessary here, but we really want covariant
            // lifetimes and we can't get them with a vector (since we can't prove to Rust that
            // it's safe, and indeed making it safe in the presence of panics could be tricky).
            // Another (attractive) option would be to do all our allocation here in an arena
            // instead of by making new owned stuff, though it would require reworking the data
            // structure.  FIXME: Try this.
            Ok(histo.into_iter().any( |&u2| RTree::raw_eq2((t, t_), u2, cmp)) || {
                let d = t.expand()?;
                let d_ = t_.expand()?;
                if let (&RTree::Node(ref x, ref v), &RTree::Node(ref x_, ref v_)) =
                     (d.as_ref().unwrap_or(t), d_.as_ref().unwrap_or(t_)) {
                    let histo = List::Cons(histo_);
                    cmp_(x, x_) && v.len() == v_.len() &&
                        v.into_iter().zip(v_).try_fold(true, |acc, (u, u_)|
                            Ok::<_, RTreeError>(acc && compare(histo, u, u_, cmp, cmp_)?))?
                } else { false }
            })
        }
        compare(List::Nil, self, t_, &mut cmp, &mut cmp_)
    }

    /// The main comparison on rtree tries first physical equality, then
    /// the structural one, then the logical equivalence
    pub fn equal<F>(&self, t_: &Self, mut cmp: F) -> RTreeResult<bool>
        where
            T: Clone,
            F: Fn(&T, &T) -> bool,
    {
        // FIXME: Figure out whether it's worth doing physical equality with the Rust
        // implementation.
        // t as *const == t_ as *const _ ||
        Ok(self.raw_eq(t_, &mut cmp) || self.equiv(t_, |x, x_| cmp(x, x_), |x, x_| cmp(x, x_))?)
    }
}
