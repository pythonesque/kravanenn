use coq::checker::environ::{
    Env,
    Globals,
};
use coq::checker::reduction::{
    ConvError,
    ConvResult,
};
use coq::checker::univ::{
    Huniv,
    LMap,
    SubstError,
    SubstResult,
};
use coq::kernel::esubst::{
    IdxError,
    IdxResult,
};
use coq::kernel::names::{
    MutInd,
};
use core::convert::{TryFrom};
use ocaml::de::{
    ORef,
};
use ocaml::values::{
    Cons,
    Constr,
    // Finite,
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
    RDecl,
    Sort,
    SortContents,
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

pub type IndResult<T> = Result<T, IndError>;

pub type IndEvaluationResult<T> = Result<T, IndEvaluationError>;

pub type ConsResult<T> = Result<T, ConsError>;

pub type MindSpecif<'b> = (&'b IndPack, &'b OneInd);

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
}

impl<'g> Globals<'g> {
    /// Raise Not_Found if not an inductive type.
    pub fn lookup_mind_specif(&self, ind: &Ind) -> IndResult<Option<MindSpecif<'g>>> {
        let Ind { name: ref kn, pos } = *ind;
        // TODO: Check to see if i being positive is guaranteed elsewhere.
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
                Ok(Cow::Owned(Constr::mk_arity(&mip.arity_ctxt, s)))
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
        // TODO: Check to see if i being positive is guaranteed elsewhere.
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
