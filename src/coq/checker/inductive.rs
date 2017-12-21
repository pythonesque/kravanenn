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
};
use coq::kernel::esubst::{
    IdxResult,
};
use coq::kernel::names::{
    MutInd,
};
use ocaml::values::{
    Constr,
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

/// Extracting an inductive type from a construction

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndError {
    Error(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndEvaluationError {
    Subst(SubstError),
    Conv(Box<ConvError>),
}

pub type IndResult<T> = Result<T, IndError>;

pub type IndEvaluationResult<T> = Result<T, IndEvaluationError>;

pub type MindSpecif<'b> = (&'b IndPack, &'b OneInd);

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
}

impl<'g> Globals<'g> {
    /// Raise Not_Found if not an inductive type.
    pub fn lookup_mind_specif(&self, kn: &MutInd,
                              tyi: usize) -> IndResult<Option<MindSpecif<'g>>> {
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
