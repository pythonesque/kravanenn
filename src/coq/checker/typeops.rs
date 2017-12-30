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
    ConvResult,
    SpecialRedResult,
};
use coq::checker::type_errors::{
    error_assumption,
    error_cant_apply_bad_type,
    error_cant_apply_not_functional,
    error_not_type,
    error_unbound_rel,
    error_unsatisfied_constraints,
};
use coq::kernel::esubst::{
    Idx,
    IdxResult,
};
use ocaml::de::{
    ORef,
};
use ocaml::values::{
    Constr,
    Cst,
    CstType,
    PUniverses,
    RDecl,
    Sort,
    Univ,
    UnivConstraint,
};
use std::borrow::{Cow};
use std::collections::{HashSet};
use std::sync::{Arc};

impl<'b, 'g> Env<'b, 'g> {
    /// NOTE: Unlike the OCaml implementation, v1 and v2 are not guaranteed to have the same length
    /// here; if you want to enforce that you must do it in the caller.
    ///
    /// NOTE: All Constrs yielded by v1 and v2 must be typechecked beforehand!
    fn conv_leq_vecti<'a1, 'a2, I1, I2>(&mut self, v1: I1, v2: I2) -> ConvResult<()>
        where
            I1: Iterator<Item=&'a1 Constr>,
            I2: Iterator<Item=&'a2 Constr>,
    {
        // NOTE: ExactSizeIterator would make enforcing the above a bit nicer.
        for (i, (t1, t2)) in v1.zip(v2).enumerate() {
            if let Err(o) = self.conv_leq(t1, t2) {
                return Err(if *o == ConvError::NotConvertible {
                    Box::new(ConvError::NotConvertibleVect(i))
                } else { o })
            }
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
}
