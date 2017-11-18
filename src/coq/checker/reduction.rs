use coq::checker::closure::{
    Context,
    FConstr,
    Infos,
    MRef,
    RedResult,
    Reds,
    Stack,
    StackMember,
};
use coq::checker::environ::{
    Env,
    Globals,
};
use coq::checker::univ::{
    UnivError,
    Universes,
};
use coq::kernel::esubst::{
    Idx,
    IdxError,
    IdxResult,
    Lift,
};
use ocaml::de::{
    Array,
};
use ocaml::values::{
    CaseInfo,
    Constr,
    Cst,
    Ind,
    Instance,
};
use std::iter;
use std::mem;

/// lft_constr_stack_elt
enum ZL<'a, 'b> where 'b: 'a {
    App(Vec<(Lift, FConstr<'a, 'b>)>),
    Proj(&'b Cst, bool, Lift),
    Fix(Lift, FConstr<'a, 'b>, LftConstrStack<'a, 'b>),
    Case(MRef<'b, (CaseInfo, Constr, Constr, Array<Constr>)>, Lift,
         FConstr<'a, 'b>, Vec<FConstr<'a, 'b>>),
}

struct LftConstrStack<'a, 'b>(Vec<ZL<'a, 'b>>) where 'b: 'a;

pub enum ConvError {
    Idx(IdxError),
    Univ(UnivError),
    NotConvertible,
    NotConvertibleVect(usize),
}

pub type ConvResult<T> = Result<T, ConvError>;

impl<'a, 'b> ::std::ops::Deref for LftConstrStack<'a, 'b> {
    type Target = Vec<ZL<'a, 'b>>;
    fn deref(&self) -> &Vec<ZL<'a, 'b>> {
        &self.0
    }
}

impl<'a, 'b> ::std::ops::DerefMut for LftConstrStack<'a, 'b> {
    fn deref_mut(&mut self) -> &mut Vec<ZL<'a, 'b>> {
        &mut self.0
    }
}

impl ::std::convert::From<IdxError> for ConvError {
    fn from(e: IdxError) -> Self {
        ConvError::Idx(e)
    }
}

impl ::std::convert::From<UnivError> for ConvError {
    fn from(e: UnivError) -> Self {
        ConvError::Univ(e)
    }
}

impl<'a, 'b> LftConstrStack<'a, 'b> {
    pub fn append(&mut self, mut v: Vec<(Lift, FConstr<'a, 'b>)>) {
        // TODO: Work out why we don't do this here?
        // if v.len() == 0 { return }
        if let Some(&mut ZL::App(ref mut l)) = self.last_mut() {
            mem::swap(&mut v, l);
            l.extend(v.into_iter());
            return
        }
        self.push(ZL::App(v))
    }
}

impl<'a, 'b, Inst, Shft> Stack<'a, 'b, Inst, Shft> {
    fn is_empty(&self) -> bool {
        self.iter().all( |x| match *x {
            StackMember::Update(_, _) => true,
            StackMember::Shift(_, _) => true,
            _ => false,
        })
    }

    /// Compute the lift to be performed on a term placed in a given stack
    fn el(&self, el: &mut Lift) -> IdxResult<()> {
        let mut i = None::<Idx>;
        for z in self.iter() {
            if let StackMember::Shift(n, _) = *z {
                match i {
                    Some(ref mut i) => { *i = i.checked_add(n)? },
                    None => { i = Some(n) },
                };
            }
        }
        if let Some(i) = i {
            el.shift(i)
        } else { Ok(()) }
    }

    fn compare_shape(&self, stk: &Self) -> IdxResult<bool> {
        let mut bal = 0isize;
        let mut stk1 = self.iter();
        let mut stk2 = stk.iter();
        let mut s1 = stk1.next();
        let mut s2 = stk2.next();
        loop {
            match (s1, s2) {
                (None, None) => { return Ok(bal == 0) },
                (Some(&StackMember::Update(_, _)), _) | (Some(&StackMember::Shift(_, _)), _) => {
                    s1 = stk1.next();
                },
                (_, Some(&StackMember::Update(_, _))) | (_, Some(&StackMember::Shift(_, _))) => {
                    s2 = stk2.next();
                },
                (Some(&StackMember::App(ref l1)), _) => {
                    // Safe because length of l1 in bytes must not exceed isize::MAX.
                    bal = bal.checked_add(l1.len() as isize)?;
                    s1 = stk1.next();
                },
                (_, Some(&StackMember::App(ref l2))) => {
                    // Safe because length of l1 in bytes must not exceed isize::MAX.
                    bal = bal.checked_sub(l2.len() as isize)?;
                    s2 = stk2.next();
                },
                (Some(&StackMember::Proj(_,_,_,_,_)), Some(&StackMember::Proj(_,_,_,_,_))) => {
                    if bal != 0 { return Ok(false) };
                    s1 = stk1.next();
                    s2 = stk2.next();
                },
                (Some(&StackMember::Case(_,_,_,_)), Some(&StackMember::Case(_,_,_,_))) |
                (Some(&StackMember::Case(_,_,_,_)), Some(&StackMember::CaseT(_,_,_))) |
                (Some(&StackMember::CaseT(_,_,_)), Some(&StackMember::Case(_,_,_,_))) |
                (Some(&StackMember::CaseT(_,_,_)), Some(&StackMember::CaseT(_,_,_))) => {
                    // TODO: Work out why c1.ci_ind  = c2.ci_ind was commented out in the first
                    // place, in Coq commit 7c290a484d4167d91fbe2de84bba6931e2e2dd8f.
                    if bal != 0 { return Ok(false) };
                    s1 = stk1.next();
                    s2 = stk2.next();
                },
                (Some(&StackMember::Fix(_, ref a1, _)), Some(&StackMember::Fix(_, ref a2, _))) => {
                    // Maybe there's a way not to recurse here?
                    if bal != 0 || !a1.compare_shape(a2)? { return Ok(false) }
                    s1 = stk1.next();
                    s2 = stk2.next();
                },
                (_, _) => return Ok(false),
            }
        }
    }

    /// pure_stack
    fn to_pure(&self, l: &mut Lift,
               ctx: &'a Context<'a, 'b>) -> IdxResult<LftConstrStack<'a, 'b>> {
        // NB: This function seemed *very* susceptible to stack overflow, so it's been changed
        // significantly from its OCaml implementation to be more amenable to loops (the version in
        // OCaml is very obviously not tail recursive).  As a result, it is not obviously correct;
        // however, I believe the reason the OCaml implementation is not written this way is mostly
        // that its stacks are linked lists, and therefore can't be efficiently iterated in
        // reverse.  Since we are using vectors in Rust, we don't have this issue.
        // TODO: If it weren't for coalescing Apps together, can this be replaced with a
        // filter_map?
        let mut stk = LftConstrStack(Vec::with_capacity(self.len()));
        for s in self.iter().rev() {
            match *s {
                StackMember::Update(_, _) => {},
                StackMember::Shift(n, _) => {
                    l.shift(n)?;
                },
                StackMember::App(ref a) => {
                    // expensive, makes a Vec
                    stk.append(a.iter().map( |t| (l.clone() /* expensive */, t.clone()))
                                       .collect());
                },
                StackMember::Proj(_, _, p, b, _) => {
                    stk.push(ZL::Proj(p, b, l.clone() /* expensive */ ));
                },
                StackMember::Fix(ref fx, ref a, _) => {
                    let mut lfx = l.clone(); // expensive
                    let pa = a.to_pure(&mut lfx, ctx)?;
                    stk.push(ZL::Fix(lfx, fx.clone(), pa));
                },
                StackMember::CaseT(o, ref env, _) => {
                    let (_, ref p, _, ref br) = **o;
                    stk.push(ZL::Case(o, l.clone() /* expensive */,
                                      env.mk_clos(p, ctx)?, env.mk_clos_vect(br, ctx)?));
                },
                StackMember::Case(o, ref p, ref br, _) => {
                    stk.push(ZL::Case(o, l.clone() /* expensive */, p.clone(), br.clone()));
                },
            }
        }
        return Ok(stk)
    }

    /// Prerequisite: call with stacks of the same shape.
    fn cmp_rec<T, F, FMind>
        (f: &mut F, fmind: &mut FMind,
         pstk1: LftConstrStack<'a, 'b>,
         pstk2: LftConstrStack<'a, 'b>,
         env: &mut T) -> ConvResult<()>
        where
            F: FnMut((&Lift, FConstr<'a, 'b>), (&Lift, FConstr<'a, 'b>), &mut T) -> ConvResult<()>,
            FMind: FnMut(&Ind, &Ind, &mut T) -> bool,
    {
        // The stacks have the same shape, so we don't need to worry about these mismatching.
        for (z1, z2) in pstk1.0.into_iter().zip(pstk2.0.into_iter()) {
            // Not sure why the loop doesn't tail recurse on the first element in OCaml.
            // Presumably, changing the order in which we check these doesn't ruin everything...
            match (z1, z2) {
                (ZL::App(a1), ZL::App(a2)) => {
                    for ((l1, c1), (l2, c2)) in a1.into_iter().zip(a2.into_iter()) {
                        f((&l1, c1), (&l2, c2), env)?;
                    }
                },
                (ZL::Fix(lfx1, fx1, a1), ZL::Fix(lfx2, fx2, a2)) => {
                    f((&lfx1, fx1), (&lfx2, fx2), env)?;
                    Self::cmp_rec(f, fmind, a1, a2, env)?;
                },
                (ZL::Proj(_, c1, _), ZL::Proj(_, c2, _)) => {
                    if c1 != c2 { return Err(ConvError::NotConvertible) }
                    // TODO: Figure out why we don't compare lifts here?
                },
                (ZL::Case(o1, l1, p1, br1),
                 ZL::Case(o2, l2, p2, br2)) => {
                    let (ref ci1, _, _, _) = **o1;
                    let (ref ci2, _, _, _) = **o2;
                    if !fmind(&ci1.ind, &ci2.ind, env) {
                        return Err(ConvError::NotConvertible)
                    }
                    f((&l1, p1), (&l2, p2), env)?;
                    for (c1, c2) in br1.into_iter().zip(br2.into_iter()) {
                        f((&l1, c1), (&l2, c2), env)?;
                    }
                },
                _ => unreachable!("Stacks should have the same shape."),
            }
        }
        return Ok(())
    }

    pub fn compare_stacks<T, F, FMind>
        (f: &mut F, fmind: &mut FMind,
         lft1: &mut Lift, stk1: &Self,
         lft2: &mut Lift, stk2: &Self,
         ctx: &'a Context<'a, 'b>,
         env: &mut T) -> ConvResult<()>
        where
            F: FnMut((&Lift, FConstr<'a, 'b>), (&Lift, FConstr<'a, 'b>), &mut T) -> ConvResult<()>,
            FMind: FnMut(&Ind, &Ind, &mut T) -> bool,
    {
        if stk1.compare_shape(stk2)? {
            Self::cmp_rec(f, fmind, stk1.to_pure(lft1, ctx)?, stk2.to_pure(lft2, ctx)?, env)
        } else {
            Err(ConvError::NotConvertible)
        }
    }
}

impl Constr {
    /// Reduction functions

    /// Note: self must be type-checked beforehand!
    pub fn whd_betaiotazeta(self) -> RedResult<Constr> {
        match self {
            Constr::Sort(_) | /* Constr::Var(_) | Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Const(_) | Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) |
            Constr::Lambda(_) | Constr::Fix(_) | Constr::CoFix(_) => Ok(self),
            _ => {
                let mut globals = Globals::default();
                let ref ctx = Context::new();
                let mut infos = Infos::create(Reds::BETAIOTAZETA, &mut globals, iter::empty())?;
                let v = self.inject(ctx)?;
                v.whd_val(&mut infos, ctx)
            }
        }
    }

    /// Note: self must be type-checked beforehand!
    pub fn whd_all<'b, 'g>(self, env: &mut Env<'b, 'g>) -> RedResult<Constr>
        where 'g: 'b,
    {
        match self {
            Constr::Sort(_) | /* Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) | Constr::Lambda(_) |
            Constr::Fix(_) | Constr::CoFix(_) => Ok(self),
            _ => {
                let Env { ref mut globals, ref mut rel_context } = *env;
                let ref ctx = Context::new();
                let mut infos = Infos::create(Reds::BETADELTAIOTA, globals,
                                              rel_context.iter_mut())?;
                let v = self.inject(ctx)?;
                v.whd_val(&mut infos, ctx)
            }
        }
    }

    /// Note: self must be type-checked beforehand!
    pub fn whd_allnolet<'b, 'g>(self, env: &mut Env<'b, 'g>) -> RedResult<Constr>
        where 'g: 'b,
    {
        match self {
            Constr::Sort(_) | /* Constr::Meta(_) | Constr::Evar(_) |*/
            Constr::Ind(_) | Constr::Construct(_) | Constr::Prod(_) | Constr::Lambda(_) |
            Constr::Fix(_) | Constr::CoFix(_) | Constr::LetIn(_) => Ok(self),
            _ => {
                let Env { ref mut globals, ref mut rel_context } = *env;
                let ref ctx = Context::new();
                let mut infos = Infos::create(Reds::BETADELTAIOTANOLET, globals,
                                              rel_context.iter_mut())?;
                let v = self.inject(ctx)?;
                v.whd_val(&mut infos, ctx)
            }
        }
    }

    /// Builds an application node, reducing beta redexes it may produce.
    /// Note: self must be type-checked beforehand!
    pub fn beta_appvect(&self, stack: &mut [Constr]) -> IdxResult<Constr> {
        let mut t = self;
        // Invariant: i ≤ stack.len()
        let mut i = 0;
        while let Constr::Lambda(ref o) = *t {
            if i < stack.len() {
                let (_, _, ref c) = **o;
                t = c;
                // i < stack.len() →
                // i + 1 ≤ stack.len()
                i += 1;
                // i ≤ stack.len()
            } else {
                // Correct environment is the entire stack, with an empty argument list; however,
                // the environment needs to be reversed, since in the OCaml implementation it was
                // generated by recursively consing entries onto the head of a list, and in our
                // setting we just take slices into a Vec.
                // FIXME: If we just write substl to operate on reversed stacks, we don't need
                // mutability here.
                stack.reverse();
                let t = t.substl(stack)?;
                stack.reverse();
                return Ok(t.applist(Vec::new()))
            }
        }
        // split_at_mut cannot panic because i ≤ stack.len();
        // correct environment is part through i, and correct stack is part after i.
        // However, the environment needs to be reversed, for the same reason given above (the
        // FIXME from above still applies here, too).
        let (env, stack) = stack.split_at_mut(i);
        env.reverse();
        let t = t.substl(env)?;
        env.reverse();
        Ok(t.applist(stack.to_vec()))
    }

    /// Conversion

    /// Conversion utility functions
    pub fn convert_universes(univ: &Universes, u: &Instance, u_: &Instance) -> ConvResult<()> {
        if univ.check_eq(u, u_)? { Ok(()) }
        else { Err(ConvError::NotConvertible) }
    }
}
