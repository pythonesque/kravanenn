use coq::checker::closure::{
    RedError,
};
use coq::checker::environ::{
    Env,
    EnvError,
    Globals,
};
use coq::checker::reduction::{
    ConvError,
    ConvResult,
};
use coq::checker::term::{
    DecomposeError,
};
use coq::checker::type_errors::{
    ArityError,
    error_elim_arity,
    TypeError,
    TypeErrorKind,
};
use coq::checker::univ::{
    Huniv,
    LMap,
    SubstError,
    SubstResult,
    UnivError,
};
use coq::kernel::esubst::{
    Idx,
    IdxError,
    IdxResult,
};
use coq::kernel::names::{
    MutInd,
};
use core::convert::{TryFrom};
use core::nonzero::{NonZero};
use ocaml::de::{
    Array,
    ORef,
};
use ocaml::values::{
    CaseInfo,
    CoFix,
    Cons,
    Constr,
    // Finite,
    Fix,
    List,
    Ind,
    IndArity,
    IndPack,
    Instance,
    Level,
    OneInd,
    Opt,
    PolArity,
    PUniverses,
    Rctxt,
    RDecl,
    Sort,
    SortContents,
    SortFam,
    Univ,
};
use std::borrow::{Cow};
use std::collections::hash_map;
use std::sync::{Arc};

/// Extracting an inductive type from a construction

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndError {
    Error(String),
    Idx(IdxError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndEvaluationError {
    Subst(SubstError),
    Conv(Box<ConvError>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConsError {
    Error(String),
    Subst(SubstError),
    Idx(IdxError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParamError {
    Anomaly(String),
    Subst(SubstError),
}

#[derive(Debug)]
pub enum CaseError<'e, 'b, 'g> where 'b: 'e, 'g: 'b, {
    Anomaly(String),
    Env(EnvError),
    Idx(IdxError),
    Univ(UnivError),
    Red(Box<RedError>),
    NotFound,
    UserError(String),
    Subst(SubstError),
    Type(Box<TypeError<'e, 'b, 'g>>),
    Error(String),
}

pub type IndResult<T> = Result<T, IndError>;

pub type IndEvaluationResult<T> = Result<T, IndEvaluationError>;

pub type ConsResult<T> = Result<T, ConsError>;

pub type ParamResult<T> = Result<T, ParamError>;

pub type CaseResult<'e, 'g, 'b, T> = Result<T, Box<CaseError<'e, 'g, 'b>>>;

pub type MindSpecif<'b> = (&'b IndPack, &'b OneInd);

/// This error is local.

struct LocalArity(Option<(SortFam, SortFam, ArityError)>);

impl ::std::convert::From<IdxError> for IndError {
    fn from(e: IdxError) -> Self {
        IndError::Idx(e)
    }
}

impl ::std::convert::From<Box<ConvError>> for IndEvaluationError {
    fn from(e: Box<ConvError>) -> Self {
        IndEvaluationError::Conv(e)
    }
}

impl ::std::convert::From<SubstError> for IndEvaluationError {
    fn from(e: SubstError) -> Self {
        IndEvaluationError::Subst(e)
    }
}

impl ::std::convert::From<IdxError> for ConsError {
    fn from(e: IdxError) -> Self {
        ConsError::Idx(e)
    }
}

impl ::std::convert::From<SubstError> for ConsError {
    fn from(e: SubstError) -> Self {
        ConsError::Subst(e)
    }
}

impl ::std::convert::From<SubstError> for ParamError {
    fn from(e: SubstError) -> Self {
        ParamError::Subst(e)
    }
}

impl ::std::convert::From<IdxError> for ParamError {
    fn from(e: IdxError) -> Self {
        ParamError::Subst(SubstError::Idx(e))
    }
}

impl ::std::convert::From<DecomposeError> for ParamError {
    fn from(e: DecomposeError) -> Self {
        let DecomposeError::Anomaly(e) = e;
        ParamError::Anomaly(e)
    }
}

impl<'e, 'b, 'g> ::std::convert::From<IdxError> for Box<CaseError<'e, 'b, 'g>> {
    fn from(e: IdxError) -> Self {
        Box::new(CaseError::Idx(e))
    }
}

impl<'e, 'b, 'g> ::std::convert::From<ParamError> for Box<CaseError<'e, 'b, 'g>> {
    fn from(e: ParamError) -> Self {
        Box::new(match e {
            ParamError::Anomaly(s) => CaseError::Anomaly(s),
            ParamError::Subst(e) => CaseError::Subst(e),
        })
    }
}

impl<'e, 'b, 'g> ::std::convert::From<IndError> for Box<CaseError<'e, 'b, 'g>> {
    fn from(e: IndError) -> Self {
        Box::new(match e {
            IndError::Error(s) => CaseError::Error(s),
            IndError::Idx(e) => CaseError::Idx(e),
        })
    }
}

impl<'e, 'b, 'g> ::std::convert::From<Box<RedError>> for Box<CaseError<'e, 'b, 'g>> {
    fn from(e: Box<RedError>) -> Self {
        Box::new(CaseError::Red(e))
    }
}

impl<'e, 'b, 'g> ::std::convert::From<UnivError> for Box<CaseError<'e, 'b, 'g>> {
    fn from(e: UnivError) -> Self {
        Box::new(CaseError::Univ(e))
    }
}

impl<'e, 'b, 'g> CaseError<'e, 'b, 'g> {
    fn from_conv<F>(e: Box<ConvError>, make_type_error: F) -> Box<Self>
        where F: FnOnce() -> Box<TypeError<'e, 'b, 'g>>,
    {
        Box::new(match *e {
            ConvError::Anomaly(ref s) => CaseError::Anomaly(s.clone()),
            ConvError::Env(ref e) => CaseError::Env(e.clone()),
            ConvError::Idx(ref e) => CaseError::Idx(e.clone()),
            ConvError::Univ(ref e) => CaseError::Univ(e.clone()),
            ConvError::Red(ref e) => CaseError::Red(e.clone()),
            ConvError::NotFound => CaseError::NotFound,
            ConvError::UserError(ref s) => CaseError::UserError(s.clone()),
            ConvError::NotConvertible => CaseError::Type(make_type_error()),
            // NOTE: Should not actually happen, but seems harmless enough.
            ConvError::NotConvertibleVect(_) => CaseError::Type(make_type_error()),
        })
    }
}

impl Constr {
    /// This API is weird; it mutates self in place.  This is done in order to allow the argument
    /// vector returned by find_rectype to point inside of self.  We could avoid this in various
    /// ways (including not allocating a vector at all) but the best solutions probably look more
    /// like this, so we just bite the bullet.
    ///
    /// Returns None if this does not reduce to an application of an inductive type.
    ///
    /// self should be typechecked beforehand!
    pub fn find_rectype(&mut self, env: &mut Env) ->
        ConvResult<Option<(&PUniverses<Ind>, Vec<&Constr>)>>
    {
        // TODO: If everything applied to reverse-order arg lists, we could use a more efficient
        // method here and use an iterator instead of allocating a Vec.
        self.whd_all(env)?;
        let (t, l) = self.decompose_app();
        Ok(match *t {
            Constr::Ind(ref o) => Some((&**o, l)),
            _ => None
        })
    }

    /* /// This API is similar to find_rectype, but the returned inductive must not be CoFinite.
    ///
    /// NOTE: self should be typechecked beforehand!
    fn find_inductive(&mut self, env: &mut Env) -> ConvResult<Option<(&Ind, Vec<&Constr>)>> {
        match self.find_rectype(env)? {
            Some((&(ref ind, _), l)) =>
                env.globals.lookup_mind_specif(ind)?
                           .and_then( |mind| if mind.0.finite != Finite::CoFinite { Some(ind) }
                                             else { None }),
            None => Ok(None),
        }
    }

    /// This API is similar to find_rectype, but the returned inductive must be CoFinite.
    ///
    /// NOTE: self should be typechecked beforehand!
    fn find_coinductive(&mut self, env: &mut Env) -> ConvResult<Option<(&Ind, Vec<&Constr>)>> {
        match self.find_rectype(env)? {
            Some((&(ref ind, _), l)) =>
                env.globals.lookup_mind_specif(ind)?
                           .and_then( |mind| if mind.0.finite == Finite::CoFinite { Some(ind) }
                                             else { None }),
            None => Ok(None),
        }
    } */

    /// NOTE: sign should be iterated in reverse order from what it would be in the OCaml
    /// implementation.
    fn instantiate_params<'a, I>(&self, full: bool, u: &Instance,
                                 mut largs: &[Constr], sign: I, tbl: &Huniv) -> ParamResult<Constr>
        where
            I: Iterator<Item=&'a RDecl>, {
        let mut ty = self;
        let mut subs = Vec::new();
        const ERR : &'static str = "instantiate_params: type, ctxt, and args mismatch";
        let fail = || Err(ParamError::Anomaly(ERR.into()));
        // NOTE: In the OCaml implementation we use fold_rel_context, which uses fold_right and
        // hence goes from right to left.  But since we were passed sign in reverse order, we
        // can just iterate the usual way.
        for decl in sign {
            match (decl, largs, ty) {
                (&RDecl::LocalAssum(_, _), &[ref a, ref args..], &Constr::Prod(ref o)) => {
                    let (_, _, ref t) = **o;
                    largs = args;
                    subs.push(Cow::Borrowed(a));
                    ty = t;
                },
                (&RDecl::LocalDef(_, ref b, _), _, &Constr::LetIn(ref o)) => {
                    let (_, _, _, ref t) = **o;
                    let s = b.subst_instance(u, tbl)?.substl(&*subs)?;
                    subs.push(Cow::Owned(s));
                    ty = t;
                },
                (_, &[], _) => if full { return fail() },
                _ => return fail(),
            }
        }
        // TODO: If we just write substl to operate on reversed stacks, we don't need
        // to reverse here.
        if largs.len() == 0 { Ok(ty.substl(subs.iter().rev())?) }
        else { fail() }
    }

    /// [p] is the predicate, [c] is the match object, [realargs] is the
    /// list of real args of the inductive type.
    fn build_case_type(&self, dep: bool, p: &Constr, realargs: &[Constr]) -> IdxResult<Constr> {
        if dep {
            // Expensive; allocates a Vec.  The allocation could probably be removed at the cost of
            // interleaving this code more with type_case_branches and having that take a Vec.
            let mut args = realargs.to_vec();
            args.push(self.clone());
            p.beta_appvect(&args)
        } else {
            p.beta_appvect(realargs)
        }
    }
}

impl<'g> Globals<'g> {
    /// Raise Not_Found if not an inductive type.
    pub fn lookup_mind_specif(&self, ind: &Ind) -> IndResult<Option<MindSpecif<'g>>> {
        let Ind { name: ref kn, pos } = *ind;
        // TODO: Check to see if pos being a legal usize is guaranteed elsewhere.
        let tyi = usize::try_from(pos).map_err(IdxError::from)?;

        match self.lookup_mind(kn) {
            None => Ok(None),
            Some(mib) => {
                match mib.packets.get(tyi) {
                    Some(ind) => Ok(Some((mib, ind))),
                    None => {
                       const ERR : &'static str =
                           "Inductive.lookup_mind_specif: invalid inductive index";
                       Err(IndError::Error(ERR.into()))
                   }
                }
            }
        }
    }
}

impl IndPack {
    /// This differs from the OCaml API in that it returns None instead of an empty Instance
    /// if the type is not polymorphic.  This turns out to be fine in practice, because we only
    /// ever use the result of this function to perform instance substitution, which does nothing
    /// if the instance is empty.
    pub fn inductive_instance(&self) -> Option<&Instance> {
        if self.polymorphic {
            Some(&self.universes.0)
        } else {
            None
        }
    }

    /// Build the substitution that replaces Rels by the appropriate
    /// inductives
    pub fn ind_subst(&self, kn: &MutInd, u: &Instance) -> Vec<Constr> {
        let ntypes = self.ntypes;
        // Note that ntypes - k - 1 is guaranteed to be in-bounds (both ≥ 0 and < n) since k
        // ranges from 0 to ntypes - 1.
        (0..ntypes).map( |k| Constr::Ind(ORef(Arc::from(PUniverses(Ind { name: kn.clone(),
                                                                         pos: ntypes - k - 1, },
                                                                   u.clone())))) )
                   .collect()
    }

    /// Instantiate inductives in constructor type
    fn constructor_instantiate(&self, kn: &MutInd, u: &Instance,
                               c: &Constr, tbl: &Huniv) -> SubstResult<Constr> {
        let s = self.ind_subst(kn, u);
        Ok(c.subst_instance(u, tbl)?.substl(&s)?)
    }

    /// NOTE: The Vec<RDecl> is reversed from the Rctxt that would have been returned
    /// by OCaml.
    ///
    /// NOTE: Returned Constr may include Constrs from sign, self.params_ctxt, and params.
    fn full_inductive_instantiate(&self, u: &Instance, params: &[Constr], sign: &Rctxt,
                                  tbl: &Huniv) -> ParamResult<Vec<RDecl>> {
        const DUMMY : Sort = Sort::Prop(SortContents::Null);
        let t = Constr::mk_arity(sign.subst_instance(u, tbl), DUMMY, Cow::into_owned)?;
        // FIXME: Seems a bit silly that we need to reverse this here to use it...
        // can't we just do it at parse time?  Or, process the rest of the lists in
        // reversed order as well?  Probably not re: the latter...
        // FIXME: expensive
        let ctx: Vec<_> = self.params_ctxt.iter().collect();
        Ok(t.instantiate_params(true, u, params, ctx.into_iter().rev(), tbl)?.dest_arity()?.0)
    }
}

impl Ind {
    /// Instantiate inductives and parameters in constructor type.
    fn full_constructor_instantiate(&self, u: &Instance,
                                    (mib, _): MindSpecif,
                                    params: &[Constr],
                                    t: &Constr,
                                    tbl: &Huniv) -> ParamResult<Constr> {
        let mind = &self.name;
        let inst_ind = mib.constructor_instantiate(mind, u, t, tbl)?;
        // FIXME: Seems a bit silly that we need to reverse this here to use it...
        // can't we just do it at parse time?  Or, process the rest of the lists in
        // reversed order as well?  Probably not re: the latter...
        // FIXME: expensive
        let ctx: Vec<_> = mib.params_ctxt.iter().collect();
        inst_ind.instantiate_params(true, u, params, ctx.into_iter().rev(), tbl)
    }
}

/// Functions to build standard types related to inductive

impl Sort {
    /// Computing the actual sort of an applied or partially applied inductive type:
    ///
    /// I_i: forall uniformparams:utyps, forall otherparams:otyps, Type(a)
    /// uniformargs : utyps
    /// otherargs : otyps
    /// I_1:forall ...,s_1;...I_n:forall ...,s_n |- sort(C_kj(uniformargs)) = s_kj
    /// s'_k = max(..s_kj..)
    /// merge(..s'_k..) = ..s''_k..
    /// --------------------------------------------------------------------
    /// Gamma |- I_i uniformargs otherargs : phi(s''_i)
    ///
    /// where
    ///
    /// - if p=0, phi() = Prop
    /// - if p=1, phi(s) = s
    /// - if p<>1, phi(s) = sup(Set,s)
    ///
    /// Remark: Set (predicative) is encoded as Type(0)
    fn as_univ(&self, tbl: &Huniv) -> Univ {
        // FIXME: It would be much better to just remember Prop and Set; in the
        // OCaml this is a nonissue because they are values (which works because of
        // implicit global state that isn't available in Rust).
        match *self {
            Sort::Type(ref u) => u.clone(),
            Sort::Prop(SortContents::Null) => Univ::type0m(tbl),
            Sort::Prop(SortContents::Pos) => Univ::type0(tbl),
        }
    }
}

/// cons_subst adds the mapping [u |-> su] in subst if [u] is not
/// in the domain or adds [u |-> sup x su] if [u] is already mapped
/// to [x].
fn cons_subst(u: Level, su: Univ, subst: &mut LMap<Univ>, tbl: &Huniv) -> IdxResult<()> {
    match subst.entry(u) {
        hash_map::Entry::Occupied(o) => o.into_mut().sup(&su, tbl),
        hash_map::Entry::Vacant(v) => { v.insert(su); Ok(()) },
    }
}

/// remember_subst updates the mapping [u |-> x] by [u |-> sup x u]
/// if it is presents and leaves the substitution unchanged if not.
fn remember_subst(u: Level, subst: &mut LMap<Univ>, tbl: &Huniv) -> IdxResult<()> {
    // FIXME: We create this even if we don't need it.
    let su = Univ::make(u.clone(), tbl)?;
    if let hash_map::Entry::Occupied(o) = subst.entry(u) {
        o.into_mut().sup(&su, tbl)
    } else { Ok(()) }
}

impl<'b, 'g> Env<'b, 'g> {
    /// Bind expected levels of parameters to actual levels
    /// Propagate the new levels in the signature
    ///
    /// NOTE: Panics if theere are more uniform parameters than RDecls.
    ///
    /// NOTE: All args must be typechecked beforehand!
    fn make_subst<'a,I>(&mut self, ctx: I, mut exp: &List<Opt<Level>>,
                        mut args: &[Constr]) -> ConvResult<LMap<Univ>>
        where
            I: Iterator<Item=&'a RDecl>, {
        let mut subst = LMap::new();
        for d in ctx {
            if let RDecl::LocalDef(_, _, _) = *d { continue }
            // FIXME: Figure out why it's okay to just eat arguments if there are no
            // more exps; shouldn't it be an error to pass too many arguments in?
            if let List::Cons(ref o) = *exp {
                let (ref u, ref exp_) = **o;
                exp = exp_;
                if let &[ref a, ref args_..] = args {
                    args = args_;
                    if let Some(ref u) = *u {
                        // We recover the level of the argument, but we don't change the
                        // level in the corresponding type in the arity; this level in the
                        // arity is a global level which, at typing time, will be enforce
                        // to be greater than the level of the argument; this is probably
                        // a useless extra constraint
                        let a = a.clone();
                        let s = self.dest_arity(a)?.1.as_univ(&self.globals.univ_hcons_tbl);
                        cons_subst(u.clone(), s, &mut subst, &self.globals.univ_hcons_tbl)?;
                    }
                } else if let Some(ref u) = *u {
                    // No more arguments here: we add the remaining universes to the
                    // substitution (when [u] is distinct from all other universes in the
                    // template, it is identity substitution; otherwise [ie. when u is
                    // already in the domain of the substitution], [remember_subst] will
                    // update its image [x] by [sup x u] in order not to forget the
                    // dependency in [u] that remains to be fullfilled).
                    remember_subst(u.clone(), &mut subst, &self.globals.univ_hcons_tbl)?;
                }
            } else {
                // Uniform parameters are exhausted
                return Ok(subst);
            }
        }
        if let List::Nil = *exp {
            // Uniform parameters are exhausted
            return Ok(subst);
        } else {
            // FIXME: Ensure that this condition is actually checked somewhere before the
            // function is called.
            panic!("There should not be more uniform parameters than RDecls.");
        }
    }

    /// NOTE: Panics if theere are more uniform parameters than RDecls.
    ///
    /// NOTE: All argsorts must be typechecked beforehand!
    pub fn instantiate_universes<'a, I>(&mut self, ctx: I, ar: &PolArity,
                                        argsorts: &[Constr]) -> ConvResult<Sort>
        where
            I: Iterator<Item=&'a RDecl>,
    {
        let subst = self.make_subst(ctx, &ar.param_levels, argsorts)?;
        let level = ar.level.subst_universe(&self.globals.univ_hcons_tbl, |l| subst.get(l))?;
        // FIXME: We should be able to spend slightly less redundant work here checking
        // equivalence to Set and Prop.  But LLVM may be able to optimize it away.
        Ok(// Singleton type not containing types are interpretable in Prop
           if level.is_type0m() { Sort::Prop(SortContents::Null) }
           // Non singleton type not containing types are interpretable in Set
           else if level.is_type0() { Sort::Prop(SortContents::Pos) }
           // This is a Type with constraints
           else { Sort::Type(level) })
    }

    /// Type of an inductive type
    ///
    /// NOTE: Panics if the mip arity_ctxt has length less than the number of uniform parameters
    ///       for mip.
    ///
    /// NOTE: All paramtyps must be typechecked beforehand!
    fn type_of_inductive_gen(&mut self, mip: &PUniverses<MindSpecif<'g>>,
                             paramtyps: &[Constr]) -> IndEvaluationResult<Cow<'g, Constr>> {
        let PUniverses((mib, mip), ref u) = *mip;
        match mip.arity {
            IndArity::RegularArity(ref a) => {
                if mib.polymorphic {
                    Ok(a.user_arity.subst_instance(u, &self.globals.univ_hcons_tbl)?)
                } else {
                    Ok(Cow::Borrowed(&a.user_arity))
                }
            },
            IndArity::TemplateArity(ref ar) => {
                // FIXME: Seems a bit silly that we need to reverse this here to use it...
                // can't we just do it at parse time?  Or, process the rest of the lists in
                // reversed order as well?  Probably not re: the latter...
                // FIXME: expensive
                let ctx: Vec<_> = mip.arity_ctxt.iter().collect();
                let s = self.instantiate_universes(ctx.into_iter().rev(), ar, paramtyps)?;
                let Ok(c) = Constr::mk_arity(mip.arity_ctxt.iter().map(Ok::<_, !>), s,
                                             RDecl::clone);
                Ok(Cow::Owned(c))
            },
        }
    }

    /// NOTE: Panics if the mip arity_ctxt has length less than the number of uniform parameters
    ///       for mip.
    ///
    /// NOTE: All args must be typechecked beforehand!
    pub fn type_of_inductive_knowing_parameters(&mut self, mip: &PUniverses<MindSpecif<'g>>,
                                                args: &[Constr]) ->
                                                IndEvaluationResult<Cow<'g, Constr>> {
        self.type_of_inductive_gen(mip, args)
    }

    /// Type of a (non applied) inductive type
    ///
    /// NOTE: Panics if the mip arity_ctxt has length less than the number of uniform parameters
    ///       for mip.
    pub fn type_of_inductive(&mut self,
                             mip: &PUniverses<MindSpecif<'g>>) ->
                             IndEvaluationResult<Cow<'g, Constr>> {
        self.type_of_inductive_knowing_parameters(mip, &[])
    }
}

impl Cons {
    /// Type of a constructor.
    fn type_of_constructor_subst<'g>(&self, u: &Instance,
                                     (mib, mip): MindSpecif<'g>,
                                     tbl: &Huniv) -> ConsResult<Constr> {
        let ind = &self.ind;
        let specif = &mip.user_lc;
        let i = self.idx;
        // TODO: We take a liberty compared to the OCaml implementation and look directly at
        // the length of specif, rather than looking at the length of consnames.  If the fact
        // that i < mip.user_lc is checked elsewhere, and this is a check designed to ensure
        // that all the constructors have names, this should of course be fixed.
        // TODO: Check to see if i being a positive usize is guaranteed elsewhere.
        match usize::try_from(i).map_err(IdxError::from)?.checked_sub(1) {
            Some(i) => match specif.get(i) {
                Some(c) => Ok(mib.constructor_instantiate(&ind.name, u, c, tbl)?),
                None => Err(ConsError::Error("Not enough constructors in the type.".into())),
            },
            // TODO: Check to see if this is already checked elsewhere.
            None => Err(ConsError::Error("Constructor index must be nonzero".into())),
        }
    }
}

impl PUniverses<Cons> {
    fn type_of_constructor_gen<'g>(&self, mspec: MindSpecif<'g>,
                                   tbl: &Huniv) -> ConsResult<Constr> {
        let PUniverses(ref cstr, ref u) = *self;
        cstr.type_of_constructor_subst(u, mspec, tbl)
    }

    /// Return type as quoted by the user
    pub fn type_of_constructor<'g>(&self, mspec: MindSpecif<'g>,
                                   tbl: &Huniv) -> ConsResult<Constr> {
        self.type_of_constructor_gen(mspec, tbl)
    }
}

impl PUniverses<MutInd> {
    pub fn arities_of_specif<'g>(&self, (mib, mip): MindSpecif<'g>,
                                 tbl: &Huniv) -> SubstResult<Vec<Constr>> {
        let PUniverses(ref kn, ref u) = *self;
        let specif = &mip.nf_lc;
        specif.iter().map( |c| mib.constructor_instantiate(kn, u, c, tbl) ).collect()
    }
}

impl SortFam {
    fn error_elim_expln(self, ki: Self) -> ArityError {
        match (self, ki) {
            (SortFam::InType, SortFam::InProp) | (SortFam::InSet, SortFam::InProp) =>
                ArityError::NonInformativeToInformative,
            // if Set impredicative
            (SortFam::InType, SortFam::InSet) => ArityError::StrongEliminationOnNonSmallType,
            _ => ArityError::WrongArity,
        }
    }

    fn check_allowed_sort(self, specif: MindSpecif) -> Result<(), LocalArity> {
        if !elim_sorts(specif).iter().any( |&sort| self == sort ) {
            let s = specif.1.inductive_sort_family();
            return Err(LocalArity(Some((self, s, self.error_elim_expln(s)))));
        } else { Ok(()) }
    }
}

impl OneInd {
    /// Type of case predicates

    /// Get type of inductive, with parameters instantiated
    fn inductive_sort_family(&self) -> SortFam {
        match self.arity {
            IndArity::RegularArity(ref s) => s.sort.family_of(),
            IndArity::TemplateArity(_) => SortFam::InType,
        }
    }

    fn arity(&self) -> (&Rctxt, SortFam) {
        (&self.arity_ctxt, self.inductive_sort_family())
    }
}

impl PUniverses<Ind> {
    /// NOTE: The Vec<RDecl> is reversed from the Rctxt that would have been returned
    /// by OCaml.
    ///
    /// NOTE: Returned Constr may include Constrs from mip.arity_ctxt, mib.params_ctxt, and params.
    fn get_instantiated_arity(&self, (mib, mip): MindSpecif, params: &[Constr],
                              tbl: &Huniv) -> ParamResult<(Vec<RDecl>, SortFam)> {
        let PUniverses(_, ref u) = *self;
        let (sign, s) = mip.arity();
        // FIXME: Figure out why we bother to return s if we never use it.
        mib.full_inductive_instantiate(u, params, sign, tbl).map( move |ctx| (ctx, s) )
    }

    /// NOTE: Panics if mip.arity_ctxt does not have at least mip.nrealdecls entries.
    fn build_dependent_inductive(self, (_, mip): MindSpecif,
                                 params: &[Constr]) -> IdxResult<Constr> {
        // TODO: Check to see if nrealdecls being a legal usize is guaranteed elsewhere.
        let nrealdecls = usize::try_from(mip.nrealdecls).map_err(IdxError::from)?;
        let realargs = mip.arity_ctxt.iter().take(nrealdecls);
        Ok(if let (realargs, Some(nrealdecls_)) = extended_rel_list(realargs)? {
            // We have a nonzero lift.
            // Casting a u32 to a usize is always valid (FIXME: verify this).
            if u32::from(nrealdecls_) as usize != nrealdecls {
                // TODO: Check whether we actually check this ahead of time; if not, we should
                // probably return an error here instead of throwing.
                panic!("mip.arity_ctxt should have at least mip.nrealdecls entries.");
            }
            // TODO: Utilize size hint from nrealdecls.
            let lparams: Result<Vec<_>, _> = params.into_iter().map( |p| p.lift(nrealdecls_) )
                                                   .collect();
            let mut lparams = lparams?;
            // TODO: Seems sort of a shame to allocate two vectors... but if we have to
            // reverse the realargs list it seems hard to avoid.
            lparams.extend(realargs.into_iter());
            let ind = Constr::Ind(ORef(Arc::from(self)));
            ind.applist(lparams)
        } else if nrealdecls != 0 {
            // TODO: Check whether we actually check this ahead of time; if not, we should
            // probably return an error here instead of throwing.
            panic!("mip.arity_ctxt should have at least mip.nrealdecls entries.");
        } else {
            // There were no decls and there's nothing to lift by, so we just use params.
            // TODO: Ascertain whether this can actually happen.
            // TODO: Check to see whether we can avoid cloning the slice (seems
            //       unlikely since we need an Arc<Vec<_>>).
            let ind = Constr::Ind(ORef(Arc::from(self)));
            Constr::App(ORef(Arc::from((ind, Array(Arc::from(params.to_vec()))))))
        })
    }

    /// NOTE: Panics if specif.1.arity_ctxt does not have at least specif.1.nrealdecls entries.
    ///
    /// NOTE: pj, specif.0.params_ctxt, specif.1.arity_ctxt, and params should be typechecked
    /// beforehand!
    ///
    /// NOTE: The environment is not necessarily left unaltered on error.  This is something
    /// that can be fixed, if need be, but for now we only make sure to truncate the environment
    /// down to its original rdecls if we succeed or fail with a type error.
    ///
    /// FIXME: Is the return value here reversed from its intuitive meaning?  That is, does
    /// true mean "does not have matching arity" and false mean "does have matching arity"?
    fn is_correct_arity<'e, 'b, 'g>(&self, env: &'e mut Env<'b, 'g>, c: &Constr,
                                    p: &Constr, pj: &Constr, specif: MindSpecif<'g>,
                                    params: &[Constr]
                                   ) -> CaseResult<'e, 'b, 'g, (&'e mut Env<'b, 'g>, bool)> {
        let (arsign, _) = self.get_instantiated_arity(specif, params,
                                                      &env.globals.univ_hcons_tbl)?;
        // We remember the old pj for error-checking purposes.
        let mut pt = pj.clone();

        let rdecl_orig_len = env.rel_context.len();
        // NOTE: In the OCaml implementation, we must reverse arsign.  We don't have to do that
        // here, though, because arsign is already reversed from the OCaml implementation.
        for a in arsign {
            pt.whd_all(env)?; // Mutates in-place
            match (pt, a) {
                (Constr::Prod(o), RDecl::LocalAssum(_, a1_)) => {
                    let (ref na1, ref a1, ref t) = *o;
                    if let Err(e) = env.conv(a1, &a1_) {
                        return Err(CaseError::from_conv(e, move || {
                            env.rel_context.truncate(rdecl_orig_len);
                            error_elim_arity(env, self.clone(),
                                             elim_sorts(specif).iter().map(Clone::clone).collect(),
                                             c.clone(), (p.clone(), pj.clone()), None)
                        }))
                    }
                    env.push_rel(RDecl::LocalAssum(na1.clone(), a1.clone()));
                    pt = t.clone();
                },
                (pt_, a @ RDecl::LocalDef(_, _, _)) => {
                    env.push_rel(a);
                    pt = pt_.lift(Idx::ONE)?;
                },
                _ => {
                    env.rel_context.truncate(rdecl_orig_len);
                    return Err(Box::new(CaseError::Type(
                                   error_elim_arity(env, self.clone(),
                                                    elim_sorts(specif).iter().map(Clone::clone)
                                                                      .collect(),
                                                    c.clone(), (p.clone(), pj.clone()), None))));
                },
            }
        }
        Ok(match pt {
            Constr::Prod(o) => { // whnf of t was not needed here!
                let (ref na1, ref a1, ref a2) = *o;
                env.push_rel(RDecl::LocalAssum(na1.clone(), a1.clone()));
                let mut a2 = a2.clone();
                a2.whd_all(env)?; // Mutates in-place
                env.rel_context.pop(); // Always yields an element, but we don't need it anyway.
                let ksort = if let Constr::Sort(s) = a2 { s.family_of() } else {
                    env.rel_context.truncate(rdecl_orig_len);
                    return Err(Box::new(CaseError::Type(
                                   error_elim_arity(env, self.clone(),
                                                    elim_sorts(specif).iter().map(Clone::clone)
                                                                      .collect(),
                                                    c.clone(), (p.clone(), pj.clone()), None))));
                };
                let dep_ind = self.clone().build_dependent_inductive(specif, params)?;
                let res = env.conv(a1, &dep_ind);
                env.rel_context.truncate(rdecl_orig_len);
                if let Err(e) = res {
                    return Err(CaseError::from_conv(e, move || {
                        error_elim_arity(env, self.clone(),
                                         elim_sorts(specif).iter().map(Clone::clone).collect(),
                                         c.clone(), (p.clone(), pj.clone()), None)
                    }))
                }
                if let Err(LocalArity(e)) = ksort.check_allowed_sort(specif) {
                    return Err(Box::new(CaseError::Type(
                                   error_elim_arity(env, self.clone(),
                                                    elim_sorts(specif).iter().map(Clone::clone)
                                                                      .collect(),
                                                    c.clone(), (p.clone(), pj.clone()), e))));
                }
                (env, true)
            },
            Constr::Sort(s_) => {
                env.rel_context.truncate(rdecl_orig_len);
                if let Err(LocalArity(e)) = s_.family_of().check_allowed_sort(specif) {
                    return Err(Box::new(CaseError::Type(
                                   error_elim_arity(env, self.clone(),
                                                    elim_sorts(specif).iter().map(Clone::clone)
                                                                      .collect(),
                                                    c.clone(), (p.clone(), pj.clone()), e))));
                }
                (env, false)
            },
            _ => {
                env.rel_context.truncate(rdecl_orig_len);
                return Err(Box::new(CaseError::Type(
                               error_elim_arity(env, self.clone(),
                                                elim_sorts(specif).iter().map(Clone::clone)
                                                                  .collect(),
                                                c.clone(), (p.clone(), pj.clone()), None))));
            },
        })
    }

    /// Type of case branches

    /// [p] is the predicate, [i] is the constructor number (starting from 0),
    /// and [cty] is the type of the constructor (params not instantiated)
    ///
    /// NOTE: nparams must be the same as specif.0.nparams, cast to usize.
    ///
    /// NOTE: Panics if ccl.decompose_app() has fewer than nparams arguments for any of the Constrs
    /// in specif.1.nf_lc (call each one cty), where ccl is the result of calling
    /// decompose_prod_assum() on full_constructor_instantiate for the given self.0, specif,
    /// params, and cty.  That is: after taking each constructor type, instantiating it with its
    /// inductives and parameters, and splitting out any foralls or letins, the number of
    /// arguments to which it is applied should be at least nparams for all constructor types for
    /// this inductive.  A simpler way to state this might be: the return type of each constructor
    /// should always be (modulo foralls, letins, and casts) the inductive type applied to at least
    /// nparams arguments.  TODO: confirm that this is what it means, and that this is actually
    /// checked somewhere else (otherwise, we should return an error here).
    fn build_branches_type(&self, specif: MindSpecif, params: &[Constr],
                           dep: bool, p: &Constr, tbl: &Huniv,
                           nparams: usize) -> ParamResult<Vec<Constr>> {
        let PUniverses(ref ind, ref u) = *self;
        let (_, mip) = specif;
        mip.nf_lc.iter().enumerate().map(|(i, cty)| {
            let typi = ind.full_constructor_instantiate(u, specif, params, cty, tbl)?;
            // NOTE: If the explanation above is correct, args represents all parameters and
            // constructor arguments, and ccl represents the final return type of the constructor.
            let (args, ccl) = typi.decompose_prod_assum();
            // NOTE: args is reversed from the OCaml implementation.
            let nargs = args.len();
            let (_, allargs) = ccl.decompose_app();
            let dep_cstr;
            let mut cargs;
            // NOTE: allargs is in the same order as the OCaml implementation.
            let (lparams, mut vargs) = allargs.split_at(nparams);
            // NOTE: If the explanation above is correct, vargs likely represent the indices for
            // this constructor, and lparams the parameters.
            if dep {
                cargs = vargs.to_vec();
                let idx = if let Some(i) = NonZero::new(i) { Idx::new(i)?.checked_add(Idx::ONE)? }
                          else { Idx::ONE };
                // Cast is legal since i32 to i64 is always valid.
                let cstr = Cons { ind: ind.clone(), idx: i32::from(idx) as i64, };
                let mut lparams: Vec<_> = lparams.into_iter().map( |&lp| lp.clone() ).collect();
                // NOTE: We reverse args here because it's returned reversed from
                // decompose_prod_assum.
                // TODO: Seems sort of a shame to allocate two vectors... but if we have to
                // reverse the extended_rel_list of args it seems hard to avoid.
                lparams.extend(extended_rel_list(args.iter().rev())?.0);
                // NOTE: If the explanation above is correct, lparams is now extended with any
                // non-let-in arguments... not clear what is going on here.
                dep_cstr = Constr::Construct(ORef(Arc::from(PUniverses(cstr, u.clone()))))
                               .applist(lparams);
                cargs.push(&dep_cstr);
                vargs = &cargs;
            }
            // NOTE: This will sometimes return an application to an empty args list; this might be
            //       undesirable in some cases (notably, some places in closure seem to work more
            //       nicely if arg lists are nonempty).  This is a general problem with
            //       beta_appvect, though (or really applist).
            let base = if let Some(nargs) = NonZero::new(nargs) {
                p.lift(Idx::new(nargs)?)?.beta_appvect(&vargs)?
            } else { p.beta_appvect(&vargs)? };
            // NOTE: We reverse args here because it's returned reversed from decompose_prod_assum.
            let Ok(bty_) = base.it_mk_prod_or_let_in(args.iter().rev().map(Ok::<_, !>),
                                                     RDecl::clone);
            Ok(bty_)
        }).collect()
    }

    /// [type_case_branches env (I,args) (p:A) c] computes useful types
    /// about the following Cases expression:
    ///
    /// ```
    ///    <p>Cases (c :: (I args)) of b1..bn end
    /// ```
    ///
    /// It computes the type of every branch (pattern variables are
    /// introduced by products) and the type for the whole expression.
    ///
    /// It does this by first looking up the inductive type in the context (specif), then
    /// typing the branches, and then typing the full match expression.
    ///
    /// NOTE: Panics if there are fewer largs than specif.0.nparams.
    ///
    /// NOTE: Panics if specif.1.arity_ctxt does not have at least specif.1.nrealdecls entries.
    ///
    /// NOTE: pj, specif.0.params_ctxt, specif.1.arity_ctxt, and largs should be typechecked
    /// beforehand!
    ///
    /// NOTE: the return type of each constructor in specif.1.nf_lc should always be (modulo
    /// foralls, letins, and casts) the inductive type applied to at least specif.0.nparams
    /// arguments.
    ///
    /// NOTE: The environment is not necessarily left unaltered on error.  This is something
    /// that can be fixed, if need be, but for now we only make sure to truncate the environment
    /// down to its original rdecls if we succeed or fail with a type error.
    pub fn type_case_branches<'e, 'b, 'g>(&self, env: &'e mut Env<'b, 'g>, largs: &[Constr],
                                          p: &Constr, pj: &Constr, c: &Constr) ->
            CaseResult<'e, 'b, 'g, (&'e mut Env<'b, 'g>, Vec<Constr>, Constr)> {
        let specif = if let Some(specif) = env.globals.lookup_mind_specif(&self.0)? { specif }
                     else { return Err(Box::new(CaseError::NotFound)) };
        let nparams = usize::try_from(specif.0.nparams).map_err(IdxError::from)?;
        // TODO: Figure out whether we actually check this ahead of time; if not, we should
        // probably return an error here instead of throwing.
        let (params, realargs) = largs.split_at(nparams);
        let (env, dep) = self.is_correct_arity(env, c, p, pj, specif, params)?;
        let lc = self.build_branches_type(specif, params, dep, p, &env.globals.univ_hcons_tbl,
                                          nparams)?;
        let ty = c.build_case_type(dep, p, realargs)?;
        Ok((env, lc, ty))
    }
}

impl CaseInfo {
    /// Checking the case case annotation is relevant
    pub fn check_case_info<'e, 'b, 'g>(&self, env: &'e mut Env<'b, 'g>, indsp: &Ind
                                      ) -> CaseResult<'e, 'b, 'g, &'e mut Env<'b, 'g>> {
        let (mib, mip) = if let Some(specif) = env.globals.lookup_mind_specif(indsp)? { specif }
                         else { return Err(Box::new(CaseError::NotFound)) };
        if !indsp.eq(&self.ind) ||
           mib.nparams != self.npar ||
           mip.consnrealdecls != self.cstr_ndecls ||
           mip.consnrealargs != self.cstr_nargs {
            return Err(Box::new(CaseError::Type(Box::new(
                    TypeError(env, TypeErrorKind::WrongCaseInfo(indsp.clone(), self.clone()))))))
        }
        Ok(env)
    }
}

fn elim_sorts<'b>((_, mip): MindSpecif<'b>) -> &'b List<SortFam> {
    &mip.kelim
}

/// NOTE: Differs from the OCaml implementation because it returns the
/// total number of hypotheses.
fn extended_rel_list<'a, I>(hyps: I) -> IdxResult<(Vec<Constr>, Option<Idx>)>
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

/// Guard conditions for fix and cofix-points.

impl Fix {
    /// NOTE: All Constrs in self should be typechecked beforehand!
    /// (or, to put it another way, the only part of typechecking left should be to ensure that the
    /// guard condition holds on all the fixpoint bodies in the block).
    pub fn check<'e, 'b, 'g>(&self, env: &'e mut Env<'b, 'g>
                            ) -> CaseResult<'e, 'b, 'g, &'e mut Env<'b, 'g>> {
        // FIXME: Implement properly (stubbing for now at the recommendation of ppedrot).
        Ok(env)
    }
}

impl CoFix {
    /// The function which checks that the whole block of definitions satisfies the guarded
    /// condition.
    ///
    /// NOTE: All Constrs in self should be typechecked beforehand!
    /// (or, to put it another way, the only part of typechecking left should be to ensure that the
    /// guard condition holds on all the cofixpoint bodies in the block).
    pub fn check<'e, 'b, 'g>(&self, env: &'e mut Env<'b, 'g>
                            ) -> CaseResult<'e, 'b, 'g, &'e mut Env<'b, 'g>> {
        // FIXME: Implement properly (stubbing for now at the recommendation of ppedrot).
        Ok(env)
    }
}
