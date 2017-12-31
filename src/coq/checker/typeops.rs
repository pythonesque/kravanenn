use coq::checker::environ::{
    Env,
};
use coq::checker::inductive::{
    CaseError,
    CaseResult,
    IndEvaluationResult,
};
use coq::checker::reduction::{
    ConvError,
    ConvPb,
    SpecialRedResult,
};
use coq::checker::type_errors::{
    error_actual_type,
    error_assumption,
    error_cant_apply_bad_type,
    error_cant_apply_not_functional,
    error_case_not_inductive,
    error_ill_formed_branch,
    error_ill_typed_rec_body,
    error_not_type,
    error_number_branches,
    error_unbound_rel,
    error_unsatisfied_constraints,
};
use coq::kernel::esubst::{
    Idx,
    IdxResult,
};
use coq::kernel::names::{
    KnCan,
};
use core::nonzero::{NonZero};
use ocaml::de::{
    ORef,
};
use ocaml::values::{
    CaseInfo,
    Cast,
    Cons,
    Constr,
    Cst,
    CstType,
    Engagement,
    Ind,
    Name,
    PUniverses,
    RDecl,
    Sort,
    SortContents,
    Univ,
    UnivConstraint,
};
use std::borrow::{Borrow, Cow};
use std::collections::{HashSet};
use std::sync::{Arc};

impl<'b, 'g> Env<'b, 'g> {
    /// NOTE: Unlike the OCaml implementation, v1 and v2 are not guaranteed to have the same length
    /// here; if you want to enforce that you must do it in the caller.
    ///
    /// NOTE: All Constrs yielded by v1 and v2 must be typechecked beforehand!
    fn conv_leq_vecti<I1, I2, T1, T2, E2>(&mut self, v1: I1,
                                          v2: I2) -> Result<(), (usize, Box<ConvError>)>
        where
            I1: Iterator<Item=T1>,
            I2: Iterator<Item=Result<T2, E2>>,
            T1: Borrow<Constr>,
            T2: Borrow<Constr>,
            E2: Into<Box<ConvError>>,
    {
        // NOTE: ExactSizeIterator would make enforcing the above a bit nicer.
        for (i, (t1, t2)) in v1.zip(v2).enumerate() {
            let t2 = match t2 { Ok(t2) => t2, Err(e) => return Err((i, e.into())), };
            if let Err(o) = self.conv_leq(t1.borrow(), t2.borrow()) { return Err((i, o)) }
        }
        Ok(())
    }

    fn check_constraints<'e>(&'e mut self,
                             cst: HashSet<UnivConstraint>) -> CaseResult<'e, 'b, 'g, &'e mut Self>
    {
        if self.stratification.universes().check_constraints(cst.iter())? { Ok(self) }
        else { Err(Box::new(CaseError::Type(error_unsatisfied_constraints(self, cst)))) }
    }

    /// This should be a type (a priori without intension to be an assumption).
    ///
    /// NOTE: ty should be a clone of ty_ when the function is called; ty_ is used for error
    /// reporting.
    ///
    /// NOTE: Mutates ty in-place, unlike the OCaml implementation.
    ///
    /// NOTE: ty must be typechecked beforehand!
    fn type_judgment<'e, 'a>(&'e mut self, c: &Constr, ty: &'a mut Constr, ty_: &Constr,
                            ) -> CaseResult<'e, 'b, 'g, (&'e mut Self, &'a Sort)> {
        ty.whd_all(self)?; // Mutates in-place.
        match *ty {
            Constr::Sort(ref s) => Ok((self, s)),
            _ => Err(Box::new(CaseError::Type(error_not_type(self, (c.clone(), ty_.clone()))))),
        }
    }

    /// This should be a type intended to be assumed.  The error message is not as useful as
    /// for `type_judgement`.
    ///
    /// NOTE: ty must be typechecked beforehand!
    fn assumption_of_judgment<'e, 'a>(&'e mut self, c: &Constr, ty: &Constr,
                                     ) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        let mut ty_ = ty.clone(); // We remember the original ty for error reporting purposes.
        ty_.whd_all(self)?; // Mutates in-place.
        match ty_ {
            Constr::Sort(_) => Ok(self),
            _ => Err(Box::new(CaseError::Type(error_assumption(self, (c.clone(), ty.clone()))))),
        }
    }

    /// Incremental typing rules: builds a typing judgement given the
    /// judgements for the subterms.

    /// Type of sorts

    /// Prop and Set
    fn judge_of_prop(&self) -> Constr {
        Constr::Sort(ORef(Arc::from(Sort::Type(Univ::type1(&self.globals.univ_hcons_tbl)))))
    }

    /// Type of Type(i)
    fn judge_of_type(&self, u: &Univ) -> IdxResult<Constr> {
        Ok(Constr::Sort(ORef(Arc::from(Sort::Type(u.super_(&self.globals.univ_hcons_tbl)?)))))
    }

    /// Type of a de Bruijn index.
    fn judge_of_relative<'e>(&'e mut self,
                             n: Idx) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        if let Some(typ) = self.lookup_rel(n).map( |decl| match *decl {
            RDecl::LocalAssum(_, ref typ) => typ.lift(n),
            RDecl::LocalDef(_, _, ref o) => o.lift(n),
        }) { Ok((self, typ?.lift(n)?)) }
        else { Err(Box::new(CaseError::Type(error_unbound_rel(self, n)))) }
    }

    /// Type of constants

    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if t = TemplateArity(sign, ar)).
    ///
    /// NOTE: All paramtyps must be typechecked beforehand!
    fn type_of_constant_type_knowing_parameters<'a>(&mut self, t: Cow<'a, CstType>,
                                                    paramtyps: &[Constr]
                                                   ) -> SpecialRedResult<Cow<'a, Constr>> {
        match t {
            Cow::Borrowed(&CstType::RegularArity(ref t)) => Ok(Cow::Borrowed(t)),
            Cow::Owned(CstType::RegularArity(t)) => Ok(Cow::Owned(t)),
            Cow::Borrowed(&CstType::TemplateArity(ref o)) |
            Cow::Owned(CstType::TemplateArity(ref o)) => {
                let (ref sign, ref ar) = **o;
                // FIXME: Seems a bit silly that we need to reverse this here to use it...
                // can't we just do it at parse time?  Or, process the rest of the lists in
                // reversed order as well?  Probably not re: the latter...
                // FIXME: expensive
                let ctx: Vec<_> = sign.iter().collect();
                let s = self.instantiate_universes(ctx.iter().map( |&x| x).rev(), ar, paramtyps)?;
                let Ok(ty) = Constr::mk_arity(ctx.into_iter().rev().map(Ok::<_, !>), s,
                                              RDecl::clone);
                Ok(Cow::Owned(ty))
            },
        }
    }

    /// NOTE: Unlike the OCaml implementation, this returns None if the constant is not found,
    /// rather than throwing Not_found.
    ///
    /// NOTE: Panics if the looked-up constant body cb for cst has cb.polymorphic true,
    ///       but cb.ty is not a RegularArity.
    ///
    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if ty = TemplateArity(sign, ar), where ty = self.globals.constant_type(cst)).
    ///
    /// NOTE: All paramtyps must be typechecked beforehand!
    fn type_of_constant_knowing_parameters(&mut self, cst: &PUniverses<Cst>,
                                           paramtyps: &[Constr]) ->
            Option<IndEvaluationResult<(Cow<'g, Constr>, HashSet<UnivConstraint>)>> {
        self.globals.constant_type(cst)
            .map( |cst_res| {
                let (ty, cu) = cst_res?;
                Ok((self.type_of_constant_type_knowing_parameters(ty, paramtyps)?, cu))
            })
    }

    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if t = TemplateArity(sign, ar)).
    pub fn type_of_constant_type<'a>(&mut self,
                                     t: &'a CstType) -> SpecialRedResult<Cow<'a, Constr>> {
        self.type_of_constant_type_knowing_parameters(Cow::Borrowed(t), &[])
    }

    /* /// NOTE: Unlike the OCaml implementation, this returns None if the constant is not found,
    /// rather than throwing Not_found.
    ///
    /// NOTE: Panics if the looked-up constant body cb for cst has cb.polymorphic true,
    ///       but cb.ty is not a RegularArity.
    ///
    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if ty = TemplateArity(sign, ar), where ty = self.globals.constant_type(cst)).
    fn type_of_constant(&mut self, cst: &Cst
                       ) -> Option<IndEvaluationResult<(Cow<'g, Constr>, HashSet<UnivConstraint>)>>
    {
        self.type_of_constant_knowing_parameters(cst, &[])
    } */

    /// NOTE: Panics if the looked-up constant body cb for cst has cb.polymorphic true,
    ///       but cb.ty is not a RegularArity.
    ///
    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if ty = TemplateArity(sign, ar), where ty = self.globals.constant_type(cst)).
    ///
    /// NOTE: All paramstyp must be typechecked beforehand!
    fn judge_of_constant_knowing_parameters<'e>(&'e mut self, cst: &PUniverses<Cst>,
                                                paramstyp: &[Constr]) ->
            CaseResult<'e, 'b, 'g, (&'e mut Self, Cow<'g, Constr>)> {
        // NOTE: In the OCaml implementation, first we try to look up the constant, to make sure it
        // exists before we continue.  In the Rust implementation, this information is propagated
        // directly by type_of_constant_knowing_parameters, so there's no need to do this twice.
        let (ty, cu) =
            if let Some(cst_res) = self.type_of_constant_knowing_parameters(cst, paramstyp) {
                cst_res?
            } else {
                return Err(Box::new(CaseError::Failure(format!("Cannot find constant: {:?}", cst.0))))
            };
        let env = self.check_constraints(cu)?;
        Ok((env, ty))
    }

    /// NOTE: Panics if the looked-up constant body cb for cst has cb.polymorphic true,
    ///       but cb.ty is not a RegularArity.
    ///
    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if ty = TemplateArity(sign, ar), where ty = self.globals.constant_type(cst)).
    fn judge_of_constant<'e>(&'e mut self, cst: &PUniverses<Cst>) ->
        CaseResult<'e, 'b, 'g, (&'e mut Self, Cow<'g, Constr>)> {
        self.judge_of_constant_knowing_parameters(cst, &[])
    }

    /// Type of an application.
    ///
    /// NOTE: funj and both sides of each judgment in argjv must be typechecked beforehand!
    fn judge_of_apply<'e>(&'e mut self, f: &Constr, funj: &Constr, argjv: &[(&Constr, &Constr)]
                         ) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        let mut typ = funj.clone(); // We remember the old funj for error reporting purposes.
        for (n, &(h, hj)) in argjv.into_iter().enumerate() {
            typ.whd_all(self)?; // Mutates in-place
            match typ {
                Constr::Prod(o) => {
                    let (_, ref c1, ref c2) = *o;
                    if let Err(e) = self.conv(hj, c1) {
                        return Err(CaseError::from_conv(e, move ||
                            // NOTE: n + 1 is always in-bounds for usize because argjv.len() must
                            // be isize::MAX or smaller (provided pointers are at least 1 byte).
                            error_cant_apply_bad_type(
                                self, (n + 1, (*c1).clone(), hj.clone()),
                                (f.clone(), funj.clone()),
                                argjv.into_iter().map( |&(h, hj)| (h.clone(), hj.clone()))
                                     .collect())))
                    }
                    typ = c2.subst1(h)?;
                },
                _ => return Err(Box::new(CaseError::Type(
                        error_cant_apply_not_functional(
                            self, (f.clone(), funj.clone()),
                            argjv.into_iter().map( |&(h, hj)| (h.clone(), hj.clone())).collect())))
                    ),
            }
        }
        return Ok((self, typ))
    }

    /// Type of product
    fn sort_of_product<'a>(&self, domsort: &Sort, rangsort: &'a Sort) -> IdxResult<Cow<'a, Sort>> {
        Ok(match (domsort, rangsort) {
            // Product rule (s, Prop, Prop)
            (_, &Sort::Prop(SortContents::Null)) => Cow::Borrowed(rangsort),
            // Product rule (Prop/Set,Set,Set)
            (&Sort::Prop(_), &Sort::Prop(SortContents::Pos)) => Cow::Borrowed(rangsort),
            // Product rule (Type,Set,?)
            (&Sort::Type(ref u1), &Sort::Prop(SortContents::Pos)) =>
                if let Engagement::ImpredicativeSet = *self.stratification.engagement() {
                    // Rule is (Type,Set,Set) in the Set-impredicative calculus
                    Cow::Borrowed(rangsort)
                } else {
                    // Rule is (Type_i,Set,Type_i) in the Set-predicative calculus
                    // FIXME: Because we mutate the first argument in-place, we swap the argument
                    // order here compared to the OCaml implementation.  Hopefully, this doesn't
                    // affect the result of sup in any significant way (it *shouldn't*, I think),
                    // but we need to double check this.
                    let mut u0 = Univ::type0(&self.globals.univ_hcons_tbl);
                    u0.sup(u1, &self.globals.univ_hcons_tbl)?;
                    Cow::Owned(Sort::Type(u0))
                },
            // Product rule (Set,Type_i,Type_i)
            (&Sort::Prop(SortContents::Pos), &Sort::Type(ref u2)) => {
                let mut u0 = Univ::type0(&self.globals.univ_hcons_tbl);
                u0.sup(u2, &self.globals.univ_hcons_tbl)?;
                Cow::Owned(Sort::Type(u0))
            },
            // Product rule (Prop,Type_i,Type_i)
            (&Sort::Prop(SortContents::Null), &Sort::Type(_)) => Cow::Borrowed(rangsort),
            // Product rule (Type_i,Type_i,Type_i)
            (&Sort::Type(ref u1), &Sort::Type(ref u2)) => {
                // NOTE: The way sup (really merge_univs) is currently written, this clone is
                // somewhat extraneous...
                // TODO: see if merge_univs can be fixed to exploit mutability of one of its
                // arguments.
                let mut u1 = u1.clone();
                u1.sup(u2, &self.globals.univ_hcons_tbl)?;
                Cow::Owned(Sort::Type(u1))
            },
        })
    }

    /// Type of a type cast
    /// `[judge_of_cast env (c,typ1) (typ2,s)]` implements the rule
    ///
    /// ```
    /// env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ///  ---------------------------------------------------------------------
    ///       env |- c:typ2
    /// ```
    ///
    /// NOTE: cj and tj must be typechecked beforehand!
    fn judge_of_cast<'e>(&'e mut self, c: &Constr, cj: &Constr, k: Cast,
                         tj: &Constr) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        let conversion = match k {
            Cast::VMCast | Cast::NATIVECast => self.vm_conv(ConvPb::Cumul, cj, tj),
            Cast::DEFAULTCast => self.conv_leq(cj, tj),
            // FIXME: Figure out why we should even have to try to handle this case;
            //        it shouldn't be possible to load this from a .vo file!
            Cast::RevertCast => panic!("This should *never* appear in a .vo file!"),
        };
        match conversion {
            Ok(()) => Ok(self),
            Err(e) => Err(CaseError::from_conv(e, move ||
                error_actual_type(self, (c.clone(), cj.clone()), tj.clone()))),
        }
    }

    /// Inductive types.

    /// The type is parametric over the uniform parameters whose conclusion
    /// is in Type; to enforce the internal constraints between the
    /// parameters and the instances of Type occurring in the type of the
    /// constructors, we use the level variables _statically_ assigned to
    /// the conclusions of the parameters as mediators: e.g. if a parameter
    /// has conclusion Type(alpha), static constraints of the form alpha<=v
    /// exist between alpha and the Type's occurring in the constructor
    /// types; when the parameters is finally instantiated by a term of
    /// conclusion Type(u), then the constraints u<=alpha is computed in
    /// the App case of execute; from this constraints, the expected
    /// dynamic constraints of the form u<=v are enforced
    ///
    /// NOTE: Panics if specif.1.arity_ctxt has length less than the number of uniform
    ///       parameters ar.param_levels (if specif.1.arity = TemplateArity(ar)),
    ///       where specif is the result of looking up ind in self.
    ///
    /// NOTE: All paramstyp must be typechecked beforehand!
    fn judge_of_inductive_knowing_parameters<'e>(&mut self,
                                                 &PUniverses(ref ind, ref u): &PUniverses<Ind>,
                                                 paramstyp: &[Constr],
                                                ) -> CaseResult<'e, 'b, 'g, Cow<'g, Constr>> {
        let specif = if let Some(specif) = self.globals.lookup_mind_specif(ind)? { specif } else {
            return Err(Box::new(CaseError::Failure(format!("Cannot find inductive: {:?}",
                                                           ind.name))))
        };
        Ok(self.type_of_inductive_knowing_parameters((specif, u), paramstyp)?)
    }

    /// NOTE: Panics if specif.1.arity_ctxt has length less than the number of uniform
    ///       parameters ar.param_levels (if specif.1.arity = TemplateArity(ar)),
    ///       where specif is the result of looking up ind.0 in self.
    fn judge_of_inductive<'e>(&mut self,
                              ind: &PUniverses<Ind>) -> CaseResult<'e, 'b, 'g, Cow<'g, Constr>> {
        self.judge_of_inductive_knowing_parameters(ind, &[])
    }

    /// Constructors.
    fn judge_of_constructor<'e>(&self,
                                cst: &PUniverses<Cons>) -> CaseResult<'e, 'b, 'g, Constr> {
        let PUniverses(ref c, _) = *cst;
        let ind = &c.ind;
        let specif = if let Some(specif) = self.globals.lookup_mind_specif(ind)? { specif } else {
            return Err(Box::new(CaseError::Failure(format!("Cannot find inductive: {:?}",
                                                           ind.name))))
        };
        Ok(cst.type_of_constructor(specif, &self.globals.univ_hcons_tbl)?)
    }

    /// Case.

    /// NOTE: All Constrs yielded by lfj and explft must be typechecked beforehand!
    fn check_branch_types<'e>(&'e mut self, c: &Constr, cj: &Constr, lfj: &[Constr],
                              explft: &[Constr]) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        if lfj.len() != explft.len() {
            return Err(Box::new(CaseError::Type(error_number_branches(self,
                                                                      (c.clone(), cj.clone()),
                                                                      explft.len()))))
        }
        if let Err((i, e)) = self.conv_leq_vecti(lfj.into_iter(),
                                                 explft.into_iter().map(Ok::<_, !>)) {
            // 0 ≤ i < lfj.len() = epxlft.len(), so lfj[i] and explft[i] are both in-bounds.
            Err(CaseError::from_conv(e, move ||
                                        error_ill_formed_branch(self, c.clone(), i, lfj[i].clone(),
                                                                explft[i].clone())))
        } else { Ok(self) }
    }

    /// For the below requirements, specif is the result of looking up ci.ind in the
    /// environment of self, and indspec is the result of calling find_rectype on cj in the
    /// environment of self.
    ///
    /// NOTE: The following must be typechecked beforehand: p, cj, pj; all entries in lfj,
    ///       specif.0.params_ctxt, specif.1.arity_ctxt, and specif.1.nf_lc;
    ///       inductive types with name ci.ind.name and positions from 0 to
    ///       specif.0.ntypes - 1; constructors with inductive type ci.ind and idx from 0 to
    ///       specif.1.nf_lc.len().
    ///
    /// NOTE: Panics if indspec.1.len() < ci.npar.
    ///
    /// NOTE: Panics if specif.1.arity_ctxt does not have at least specif.1.nrealdecls entries.
    ///
    /// NOTE: Returned Constr may include references to p, c, and parts of cj.
    ///
    /// NOTE: the return type of each constructor in specif.1.nf_lc should always be (modulo
    /// foralls, letins, and casts) the inductive type applied to at least specif.0.nparams
    /// arguments.
    ///
    /// NOTE: self is not necessarily left unaltered on error.  This is something
    /// that can be fixed, if need be, but for now we only make sure to truncate the environment
    /// down to its original rdecls if we succeed or fail with a type error.
    fn judge_of_case<'e>(&'e mut self, ci: &CaseInfo,
                         p: &Constr, pj: &Constr, c: &Constr, cj: &Constr,
                         lfj: &[Constr]) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        let mut cj_ = cj.clone(); // We remember the original cj for error reporting purposes.
        let indspec = if let Some(indspec) = cj_.find_rectype(self)? { indspec } else {
            return Err(Box::new(CaseError::Type(
                    error_case_not_inductive(self, (c.clone(), cj.clone())))))
        };
        // TODO: Below, we return NotFound if indspec isn't found in the environment, but it might
        // make more sense to fail with a "Cannot find inductive" error as we do in other
        // judgments.
        let env = ci.check_case_info(self, &(indspec.0).0)?;
        // We now know that ci.ind = indspec.0.0, specif exists,
        // specif.0.nparams == ci.npar, specif.1.consnrealdecls == ci.cstr_ndecls, and
        // specif.1.consnrealargs == ci.cstr_nargs.
        let (env, bty, rslty) = indspec.0.type_case_branches(env, &indspec.1, p, pj, c)?;
        let env = env.check_branch_types(c, cj, lfj, &bty)?;
        Ok((env, rslty))
    }

    /// Projection
    ///
    /// NOTE: ct should be typechecked beforehand!
    ///
    /// NOTE: pb.ind should be the same as indspec.0.0.name, where indspec = ct.find_rectype(self)
    ///       and pb = self.globals.lookup_projection(p) (that is, ct should be the inductive type
    ///       represented by p applied to some arguments, after reduction).
    fn judge_of_projection<'e>(&'e mut self, p: &Cst, c: &Constr,
                               ct: &Constr) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        // TODO: Below, we return NotFound if indspec isn't found in the environment, but it might
        // make more sense to fail with a "Cannot find inductive" error as we do in other
        // judgments.
        let pb = if let Some(pb) = self.globals.lookup_projection(p) { pb? }
                 else { return Err(Box::new(CaseError::NotFound)) };
        let mut ct_ = ct.clone(); // We remember the original ct for error reporting purposes.
        let ty;
        let (cst, mut args) =
            if let Some(indspec) = ct_.find_rectype(self)? { indspec }
            else { return Err(Box::new(CaseError::Type(
                           error_case_not_inductive(self, (c.clone(), ct.clone()))))) };
        let PUniverses(ref ind, ref u) = *cst;
        // NOTE: uses the default MutInd equality, which is Canonical
        assert_eq!(KnCan(&pb.ind), KnCan(&ind.name));
        ty = pb.ty.subst_instance(u, &self.globals.univ_hcons_tbl)?;
        args.push(&ty);
        // TODO: If we just write substl to operate on reversed stacks, we don't need
        // to reverse here.
        Ok((self, ty.substl(args.into_iter().rev())?))
    }

    /// Fixpoints
    ///
    /// Checks the type of a general (co)fixpoint, i.e. without checking
    /// the specific guard condition.
    ///
    /// NOTE: lar.len(), lbody.len(), and vdefj.len() must be identical!
    ///
    /// NOTE: All Constrs yielded by vdefj and lar must be typechecked beforehand!
    fn type_fixpoint<'e>(&'e mut self, lna: &[Name], lar: &[Constr], lbody: &[Constr],
                         vdefj: &[Constr]) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        let lt = vdefj.len();
        assert_eq!(lar.len(), lt);
        assert_eq!(lbody.len(), lt);
        let res = if let Some(lt) = NonZero::new(lt) {
            let lt = Idx::new(lt)?;
            self.conv_leq_vecti(vdefj.into_iter(), lar.into_iter().map( |ty| ty.lift(lt)))
        } else { self.conv_leq_vecti(vdefj.into_iter(), lar.into_iter().map(Ok::<_, !>)) };
        if let Err((i, e)) = res {
            let vdefj: Vec<_> = lbody.into_iter().zip(vdefj.into_iter())
                                     .map( |(b, ty)| (b.clone(), ty.clone())).collect();
            // 0 ≤ i < lfj.len() = epxlft.len(), so lfj[i] and explft[i] are both in-bounds.
            Err(CaseError::from_conv(e, move ||
                    error_ill_typed_rec_body(self, i, lna.into_iter().map(Clone::clone).collect(),
                                             vdefj, lar.into_iter().map(Clone::clone).collect())))
        } else { Ok(self) }
    }
}
