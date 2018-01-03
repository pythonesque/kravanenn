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
    IdxError,
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
    CoFix,
    Cons,
    Constr,
    Cst,
    CstType,
    Engagement,
    Fix,
    Fix2,
    Ind,
    Level,
    Name,
    PolArity,
    PRec,
    Proj,
    PUniverses,
    RDecl,
    Sort,
    SortContents,
    Univ,
    UnivConstraint,
};
use std::borrow::{Borrow, Cow};
use std::collections::{HashSet};
use std::convert::{TryFrom};
use std::iter::{self};
use std::option::{NoneError};
use std::sync::{Arc};

impl<'b, 'g> Env<'b, 'g> {
    /// NOTE: Unlike the OCaml implementation, v1 and v2 are not guaranteed to have the same length
    /// here; if you want to enforce that you must do it in the caller.
    ///
    /// NOTE: Precondition: ∀ pj ∈ v1, ∃ s : sort, self ⊢ pj : s
    ///
    /// NOTE: Precondition: ∀ pj ∈ v2, ∃ s : sort, self ⊢ pj : s
    ///
    /// NOTE: Postcondition: ∀ i : nat, self ⊨ v1[i] ≡ v2[i]
    fn conv_leq_vecti<I1, I2, T1, T2, E2>(&self, v1: I1,
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
            if let Err(o) = self.conv_leq(t1.borrow(), t2.borrow(), iter::empty()) {
                return Err((i, o))
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
    /// NOTE: Precondition: ∃ s : sort, self ⊢ ty : s
    ///
    /// NOTE: Postcondition: ∃ s : sort, self ⊨ ty ≡ s
    fn type_judgment<'e, 'a>(&'e mut self, c: &Constr, ty: &'a mut Constr, ty_: &Constr,
                            ) -> CaseResult<'e, 'b, 'g, (&'e mut Self, &'a Sort)> {
        ty.whd_all(self, iter::empty())?; // Mutates in-place.
        match *ty {
            Constr::Sort(ref s) => Ok((self, s)),
            _ => Err(Box::new(CaseError::Type(error_not_type(self, (c.clone(), ty_.clone()))))),
        }
    }

    /// This should be a type intended to be assumed.  The error message is not as useful as
    /// for `type_judgement`.
    ///
    /// NOTE: Precondition: ∃ s : sort, self ⊢ ty : s
    ///
    /// NOTE: Postcondition: ∃ s : sort, self ⊨ ty ≡ s
    fn assumption_of_judgment<'e, 'a>(&'e mut self, c: &Constr, ty: &Constr,
                                     ) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        let mut ty_ = ty.clone(); // We remember the original ty for error reporting purposes.
        ty_.whd_all(self, iter::empty())?; // Mutates in-place.
        match ty_ {
            Constr::Sort(_) => Ok(self),
            _ => Err(Box::new(CaseError::Type(error_assumption(self, (c.clone(), ty.clone()))))),
        }
    }

    /// Incremental typing rules: builds a typing judgement given the
    /// judgements for the subterms.

    /// Type of sorts

    /// Prop and Set
    ///
    /// NOTE: Postcondition: ∃ s : sort, self ⊢ Prop|Set : s
    fn judge_of_prop(&self) -> Constr {
        Constr::Sort(ORef(Arc::from(Sort::Type(Univ::type1(&self.globals.univ_hcons_tbl)))))
    }

    /// Type of Type(i)
    ///
    /// NOTE: Postcondition: ∃ s : sort, self ⊢ Type u : s
    fn judge_of_type(&self, u: &Univ) -> IdxResult<Constr> {
        Ok(Constr::Sort(ORef(Arc::from(Sort::Type(u.super_(&self.globals.univ_hcons_tbl)?)))))
    }

    /// Type of a de Bruijn index.
    ///
    /// NOTE: Precondition: ∀ (n : nat) (typ : constr),
    ///       self ⊢ Rel n : typ → ∃ s : sort, self ⊢ typ : s
    ///
    /// NOTE: Postcondition: ∃ (typ : constr) (s : sort), self ⊢ Rel n : typ ∧ self ⊢ typ : s
    fn judge_of_relative<'e>(&'e mut self,
                             n: Idx) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        if let Some(typ) = self.lookup_rel(n).map( |decl| match *decl {
            RDecl::LocalAssum(_, ref typ) => typ.lift(n),
            RDecl::LocalDef(_, _, ref o) => o.lift(n),
        }) { Ok((self, typ?)) }
        else { Err(Box::new(CaseError::Type(error_unbound_rel(self, n)))) }
    }

    /// Type of constants

    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if t = TemplateArity(sign, ar)).
    ///
    /// NOTE: Precondition: ∀ pj ∈ paramtyps, ∃ s : sort, self ⊢ pj : s
    ///
    /// NOTE: Precondition (ignoring template arity): ∃ s : sort, self ⊢ t : s
    ///
    /// NOTE: Postcondition (ignoring template arity): ∃ s : sort, self ⊢ t : s
    fn type_of_constant_type_knowing_parameters<'a1, 'a2, I>(&self, t: Cow<'a1, CstType>,
                                                             paramtyps: I,
                                                            ) -> SpecialRedResult<Cow<'a1, Constr>>
        where
            I: Iterator<Item=&'a2 Constr>,
    {
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
    /// NOTE: Precondition: ∀ pj ∈ paramtyps, ∃ s : sort, self ⊢ pj : s
    ///
    /// NOTE: Precondition (ignoring template arity):
    ///
    ///       ∀ (δ,u) : pconstant, δ ∈ self → ∃ (cb : constant_body) (s : sort),
    ///       self ⊨ consistent [u]cb.universes.1 →
    ///       self ⊢ Const [u]δ : [u]cb.ty ∧ self ⊢ [u]cb.ty : s
    ///
    /// NOTE: Postcondition (ignoring template arity):
    ///
    ///       ∃ (ty : constr) (s : sort) (cu : context), self ⊨ consistent cu →
    ///                                                  self ⊢ Const [u]δ : ty ∧ self ⊢ ty : s
    fn type_of_constant_knowing_parameters<'a, I>(&self, cst: &PUniverses<Cst>,
                                                  paramtyps: I) ->
            Option<IndEvaluationResult<(Cow<'g, Constr>, HashSet<UnivConstraint>)>>
        where
            I: Iterator<Item=&'a Constr>,
    {
        self.globals.constant_type(cst)
            .map( |cst_res| {
                let (ty, cu) = cst_res?;
                Ok((self.type_of_constant_type_knowing_parameters(ty, paramtyps)?, cu))
            })
    }

    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if t = TemplateArity(sign, ar)).
    ///
    /// NOTE: Precondition (ignoring template arity): ∃ s : sort, self ⊢ t : s
    ///
    /// NOTE: Postcondition (ignoring template arity): ∃ s : sort, self ⊢ t : s
    pub fn type_of_constant_type<'a>(&self,
                                     t: &'a CstType) -> SpecialRedResult<Cow<'a, Constr>> {
        self.type_of_constant_type_knowing_parameters(Cow::Borrowed(t), iter::empty())
    }

    /* /// NOTE: Unlike the OCaml implementation, this returns None if the constant is not found,
    /// rather than throwing Not_found.
    ///
    /// NOTE: Panics if the looked-up constant body cb for cst has cb.polymorphic true,
    ///       but cb.ty is not a RegularArity.
    ///
    /// NOTE: Panics if there are more uniform parameters ar.param_levels than RDecls sign
    ///       (if ty = TemplateArity(sign, ar), where ty = self.globals.constant_type(cst)).
    fn type_of_constant(&self, cst: &Cst
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
    /// NOTE: Precondition: ∀ pj ∈ paramstyp, ∃ s : sort, self ⊢ pj : s
    ///
    /// NOTE: Precondition (ignoring template arity):
    ///
    ///       ∀ (δ,u) : pconstant, δ ∈ self → ∃ (cb : constant_body) (s : sort),
    ///       self ⊨ consistent [u]cb.universes.1 →
    ///       self ⊢ Const [u]δ : [u]cb.ty ∧ self ⊢ [u]cb.ty : s
    ///
    /// NOTE: Postcondition (ignoring template arity):
    ///
    ///       ∃ (ty : constr) (s : sort), self ⊢ Const [u]δ : ty ∧ self ⊢ ty : s
    fn judge_of_constant_knowing_parameters<'a, 'e, I>(&'e mut self, cst: &PUniverses<Cst>,
                                                       paramstyp: I) ->
            CaseResult<'e, 'b, 'g, (&'e mut Self, Cow<'g, Constr>)>
        where
            I: Iterator<Item=&'a Constr>,
    {
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
    ///
    /// NOTE: Precondition (ignoring template arity):
    ///
    ///       ∀ (δ,u) : pconstant, δ ∈ self → ∃ (cb : constant_body) (s : sort),
    ///       self ⊨ consistent [u]cb.universes.1 →
    ///       self ⊢ Const [u]δ : [u]cb.ty ∧ self ⊢ [u]cb.ty : s
    ///
    /// NOTE: Postcondition (ignoring template arity):
    ///
    ///       ∃ (ty : constr) (s : sort), self ⊢ Const [u]δ : ty ∧ self ⊢ ty : s
    fn judge_of_constant<'e>(&'e mut self, cst: &PUniverses<Cst>) ->
        CaseResult<'e, 'b, 'g, (&'e mut Self, Cow<'g, Constr>)> {
        self.judge_of_constant_knowing_parameters(cst, iter::empty())
    }

    /// Type of an application.
    ///
    /// NOTE: Precondition: argv.len() ≤ isize::MAX
    ///
    /// NOTE: Precondition: ∀ (h, hj) ∈ argjv, ∃ s : sort, self ⊢ pj : s ∧ self ⊢ h : hj
    ///
    /// NOTE: Precondition: ∃ s : sort, self ⊢ funj : s
    ///
    /// NOTE: Postcondition: ∃ (typ : constr) (s: sort), self ⊢ App f (map fst argjv) : typ ∧
    ///                                                  self ⊢ typ : s
    fn judge_of_apply<'a, 'e, I>(&'e mut self, f: &Constr, funj: &Constr, argjv: I
                                ) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)>
        where
            I: Clone + Iterator<Item=&'a (&'a Constr, Constr)>,
    {
        let mut typ = funj.clone(); // We remember the old funj for error reporting purposes.
        for (n, &(h, ref hj)) in argjv.clone().enumerate() {
            typ.whd_all(self, iter::empty())?; // Mutates in-place
            match typ {
                Constr::Prod(o) => {
                    let (_, ref c1, ref c2) = *o;
                    if let Err(e) = self.conv(hj, c1, iter::empty()) {
                        return Err(CaseError::from_conv(e, move ||
                            // NOTE: n + 1 is always in-bounds for usize because argjv.len() must
                            // be isize::MAX or smaller (provided pointers are at least 1 byte and
                            // argjv is backed by a vector, which is the case here).
                            error_cant_apply_bad_type(
                                self, (n + 1, (*c1).clone(), hj.clone()),
                                (f.clone(), funj.clone()),
                                argjv.map( |&(h, ref hj)| (h.clone(), hj.clone()))
                                     .collect())))
                    }
                    typ = c2.subst1(h)?;
                },
                _ => return Err(Box::new(CaseError::Type(
                        error_cant_apply_not_functional(
                            self, (f.clone(), funj.clone()),
                            argjv.map( |&(h, ref hj)| (h.clone(), hj.clone())).collect())))
                    ),
            }
        }
        return Ok((self, typ))
    }

    /// Type of product
    ///
    /// NOTE: Postcondition: ∃ s : sort, ∀ x : name, self ⊢ Prod (x, domsort, rangsort) : s
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
    /// NOTE: Precondition: self ⊢ c : cj
    ///
    /// NOTE: Precondition: ∃ s : sort, self ⊢ cj : s
    ///
    /// NOTE: Precondition: ∃ s : sort, self ⊢ tj : s
    ///
    /// NOTE: Postcondition: self ⊢ c : tj ∧ self ⊢ Cast c k tj : tj
    fn judge_of_cast<'e>(&'e mut self, c: &Constr, cj: &Constr, k: Cast,
                         tj: &Constr) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        let conversion = match k {
            Cast::VMCast | Cast::NATIVECast => self.vm_conv(ConvPb::Cumul, cj, tj, iter::empty()),
            Cast::DEFAULTCast => self.conv_leq(cj, tj, iter::empty()),
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
    ///       where specif is the result of looking up ind.0 in self.
    ///
    /// NOTE: Precondition: ∀ p ∈ paramstyp, ∃ s : sort, self ⊢ p : s
    ///
    /// NOTE: Precondition (ignoring template arity):
    ///
    ///       ∀ (ind, u) : pinductive, ind.0 ∈ env → ∃ (mind : IndPack), ind.1 < len mind.packets →
    ///       ∃ s : sort, env ⊢ Ind [u]ind : [u]mind.packets[ind.1].arity.user_arity ∧
    ///                   env ⊢ [u]mind.packets[ind.1].arity.user_arity : s
    ///
    /// NOTE: Postcondition (ignoring template arity):
    ///
    ///       ∃ (ty : constr) (s : sort), self ⊢ Ind [ind.1]ind.0 : ty ∧ self ⊢ ty : s
    fn judge_of_inductive_knowing_parameters<'a, 'e, I>(&self, ind: &PUniverses<Ind>,
                                                        paramstyp: I) ->
            CaseResult<'e, 'b, 'g, Cow<'g, Constr>>
        where
            I: Iterator<Item=&'a Constr>,
    {
        let PUniverses(ref ind, ref u) = *ind;
        let specif = if let Some(specif) = self.globals.lookup_mind_specif(ind)? { specif } else {
            return Err(Box::new(CaseError::Failure(format!("Cannot find inductive: {:?}",
                                                           ind.name))))
        };
        Ok(self.type_of_inductive_knowing_parameters((specif, u), paramstyp)?)
    }

    /// NOTE: Panics if specif.1.arity_ctxt has length less than the number of uniform
    ///       parameters ar.param_levels (if specif.1.arity = TemplateArity(ar)),
    ///       where specif is the result of looking up ind.0 in self.
    ///
    /// NOTE: Precondition (ignoring template arity):
    ///
    ///       ∀ ind : pinductive, ind.0.0 ∈ env → ∃ mind : IndPack, ind.0.1 < len mind.packets →
    ///       ∃ s : sort, env ⊢ Ind [ind.1]ind.0 : [ind.1]mind.packets[ind.0.1].arity.user_arity ∧
    ///                   env ⊢ [ind.1]mind.packets[ind.0.1].arity.user_arity : s
    ///
    /// NOTE: Postcondition (ignoring template arity):
    ///
    ///       ∃ (ty : constr) (s : sort), self ⊢ Ind [ind.1]ind.0 : ty ∧ self ⊢ ty : s
    fn judge_of_inductive<'e>(&self,
                              ind: &PUniverses<Ind>) -> CaseResult<'e, 'b, 'g, Cow<'g, Constr>> {
        self.judge_of_inductive_knowing_parameters(ind, iter::empty())
    }

    /// Constructors.
    ///
    /// NOTE: Precondition:
    ///
    ///       ∀ cst : pconstructor, cst.0.0.0 ∈ env → ∃ ind: IndPack, cst.0.0.1 < len ind.packets →
    ///       cst.0.1 < len ind.packets[cst.0.0.1].user_lc →
    ///       self ⊢ Construct [cst.1]cst.0 : [0/[cst.1] Ind (cst.0.0.0,ind.ntypes - 1), ...,
    ///                                        (ind.ntypes-1)/[cst.1] Ind (cst.0.0.0, 0)]
    ///                                       [cst.1]ind.packets[cst.0.0.1].user_lc[cst.0.1] ∧
    ///       self ⊢ [0/[cst.1] Ind (cst.0.0.0,ind.ntypes - 1), ...,
    ///                             (ind.ntypes-1)/[cst.1] Ind (cst.0.0.0, 0)]
    ///              [cst.1]ind.packets[cst.0.0.1].user_lc[cst.0.1] : s
    ///
    /// NOTE: Postcondition:
    ///
    ///       ∃ (ty : constr) (s : sort), self ⊢ Construct [cst.1]cst.0 : ty ∧ self ⊢ ty : s
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

    /// NOTE: Precondition: ∀ cj' ∈ lfj , ∃ s : sort, self ⊢ cj' : s
    ///
    /// NOTE: Precondition: ∀ cj' ∈ explft, ∃ s : sort, self ⊢ cj' : s
    ///
    /// NOTE: Postcondition: len lfj = len epxlft ∧ ∀ i : nat, self ⊨ lfj[i] ≡ explft[i]
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

    /// For the below requirements, specif is the result of looking up indspec.0.0 in the
    /// environment of self, and indspec is the result of calling find_rectype on cj in the
    /// environment of self.
    ///
    /// NOTE: Precondition: ∃ s : sort, self ⊢ cj : s
    ///
    /// NOTE: Precondition: ∃ s : sort, self ⊢ pj : s
    ///
    /// NOTE: Precondition: ∀ cj' ∈ lfj , ∃ s : sort, self ⊢ cj' : s
    ///
    /// NOTE: Precondition: ∀ cj' ∈ specif.1.nf_lc, ∃ s : sort, self ⊢ cj' : s
    ///
    /// NOTE: The following must be typechecked beforehand: all entries in specif.0.params_ctxt
    ///       and specif.1.arity_ctxt; inductive types with name indspec.0.0.name and positions
    ///       from 0 to specif.0.ntypes - 1; constructors with inductive type indspec.0.0 and
    ///       idx from 1 to specif.1.nf_lc.len().
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
    ///
    /// NOTE: Postcondition:
    ///
    ///       ∃ ty : constr, ∀ lf : list constr, len lf = len lfj → self ⊢ c : cj →
    ///       self ⊢ p : pj → (∀ i : nat, 0 ≤ i < len lfj → self ⊢ lf[i] : lfj[i]) →
    ///       self ⊢ match c [as c'] return p with lf end : ty
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
        // judgments... on the other hand, it might actually make sense to panic in this case if
        // that happens, since we know that all parts of indspec should have already been
        // typechecked, which means it should presumably exist in the environment (there's a
        // comment to the effect that it might be okay to panic on NotFound in closure.rs as well;
        // perhaps it's worth investigating further).
        let env = ci.check_case_info(self, &(indspec.0).0)?;
        // We now know that ci.ind = indspec.0.0, specif exists,
        // specif.0.nparams == ci.npar, specif.1.consnrealdecls == ci.cstr_ndecls, and
        // specif.1.consnrealargs == ci.cstr_nargs.
        // Note that since ∃ s : sort, self ⊢ cj : s, and find_rectype succeeded, indspec has to
        // decompose into an application of an inductive type to a series of parameters and
        // indices; partial applications of inductive types do not have sorts as types, so the
        // application must be full.  Therefore, indspec.1.len() < indspec.0.0.npar (since a full
        // application of an inductive type always includes all parameters).
        let (env, bty, rslty) = indspec.0.type_case_branches(env, &indspec.1, p, pj, c)?;
        // NOTE: We now know the postcondition of type_case_branches, and can instantiate it with
        // lfj as snd lb. We also know env ⊢ cj ≡ (Ind indspec.0) indspec.1, thanks to the
        // postcondition of find_rectype.  We thus know:
        // ∀ lf : list constr, len bty = len lf = len lfj → env ⊢ c : cj → env ⊢ p : pj →
        // (∀ i : nat, 0 ≤ i < len lfj → env ⊢ lf[i] : lfj[i] ∧ env ⊨ lfj[i] ≡ bty[i]) →
        // self ⊢ match c return p with lf end : rslty
        let env = env.check_branch_types(c, cj, lfj, &bty)?;
        // From the postcondition of check_branch_types, len lfj = len bty ∧
        // ∀ i : nat, self ⊨ lfj[i] ≡ bty[i].  So we know:
        // ∀ lf : list constr, len lf = len lfj → env ⊢ c : cj → env ⊢ p : pj →
        // (∀ i : nat, 0 ≤ i < len lfj → env ⊢ lf[i] : lfj[i]) →
        // self ⊢ match c return p with lf end : rslty
        Ok((env, rslty))
    }

    /// Projection
    ///
    /// NOTE: ct should be typechecked beforehand!
    ///
    /// NOTE: pb.ind should be the same as indspec.0.0.name, where indspec = ct.find_rectype(self)
    ///       and pb = self.globals.lookup_projection(p.0) (that is, ct should be the inductive
    ///       type represented by p applied to some arguments, after reduction).
    fn judge_of_projection<'e>(&'e mut self, p: &Proj, c: &Constr,
                               ct: &Constr) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        // TODO: Below, we return NotFound if indspec isn't found in the environment, but it might
        // make more sense to fail with a "Cannot find inductive" error as we do in other
        // judgments.
        let pb = if let Some(pb) = self.globals.lookup_projection(&p.0) { pb? }
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
    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Precondition:
    ///
    ///       ∀ ar ∈ lar, ∃ s : sort, self ⊢ lift (len lar) ar : Sort s
    ///
    /// NOTE: Precondition: ∀ i : nat, 0 ≤ i < len lar → self ⊢ vdef[i] : vdefj[i].
    ///
    /// NOTE: Postcondition:
    ///
    ///       ∀ i : nat, 0 ≤ i < len lar → self ⊨ vdefj[i] ≡ lift (len lar) lar[i]
    fn type_fixpoint<'e>(&'e mut self, lna: &[Name], lar: &[Constr], lbody: &[Constr],
                         vdefj: &[Constr]) -> CaseResult<'e, 'b, 'g, &'e mut Self> {
        let lt = vdefj.len();
        assert_eq!(lar.len(), lt);
        assert_eq!(lbody.len(), lt);
        let res = if let Some(lt) = NonZero::new(lt) {
            // NOTE: This case can presumably never happen for any fixpoint with a body...
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

    /// The typing machine.
    ///
    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition: ∃ (ty : constr) (s : sort), self ⊢ cstr : ty ∧ self ⊢ ty : s.
    fn execute<'e>(&'e mut self, cstr: &Constr) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        match *cstr {
            // Atomic terms
            Constr::Sort(ORef(ref o)) => {
                let ty = if let Sort::Type(ref u) = **o { self.judge_of_type(u)? }
                         else { self.judge_of_prop() };
                Ok((self, ty))
            },
            Constr::Rel(n) => {
                let idx = Idx::new(NonZero::new(n).ok_or(IdxError::from(NoneError))?)?;
                self.judge_of_relative(idx)
            },
            //Constr::Var(_),
            Constr::Const(ref o) => self.judge_of_constant(o)
                                        .map(|(env, ty)| (env, ty.into_owned())),
            // Lambda calculus operators
            Constr::App(ref o) => {
                let mut o = o;
                // Initialize with the arguments we know we need for sure.
                // TODO: It's possible we could avoid allocating a Vec for args *or* jl with a
                // custom iterator... as it is, we end up taking up space anyway since we remember
                // args in order to ease error reporting (though it would not be hard to fix just
                // that problem).
                let mut jl = Vec::new();
                let mut env = self;
                loop {
                    let (ref f, ref args) = **o;
                    // Take advantage of knowledge of the length to add capacity more quickly
                    // than we otherwise might.
                    jl.reserve(args.len());
                    // We process the arguments in reverse order.  This allows us to avoid
                    // allocating an intermediate vector to store appended arguments if it turns
                    // out that f is itself an application.  In theory, this should be perfectly
                    // fine, since for this part of the check all the terms in the application can
                    // be checked in parallel.  In practice, since this evaluates in a different
                    // order from the current Coq implementation, it won't always error in the same
                    // way, which might be annoying for fuzzing purposes, but since this is the
                    // checker it shouldn't normally matter for end users.
                    for arg in args.iter().rev() {
                        let env_ = env;
                        let (env_, j) = env_.execute(arg)?;
                        env = env_;
                        jl.push((arg, j));
                    }
                    // If f is an App, continue to evaluate the arguments of the application in f.
                    if let Constr::App(ref o_) = *f { o = o_ } else { break }
                }
                // Now we've evaluated all the arguments to some non-application Constr (note that
                // jl is reversed, hence the re-reversals below!) so it's time to type f.
                let f = &(**o).0;
                let j = match *f {
                    Constr::Ind(ref o) => // Sort-polymorphism of inductive types
                        env.judge_of_inductive_knowing_parameters(o, jl.iter()
                                                                       .map(|j| &j.1).rev())?,
                    Constr::Const(ref o) => { // Sort-polymorphism of constant
                        let env_ = env;
                        let (env_, j) =
                            env_.judge_of_constant_knowing_parameters(o, jl.iter().map(|j| &j.1)
                                                                                  .rev())?;
                        env = env_; j
                    },
                    _ => { // No sort-polymorphism
                        let env_ = env; let (env_, j) = env_.execute(f)?; env = env_; Cow::Owned(j)
                    },
                };
                env.judge_of_apply(f, &j, jl.iter().rev())
            },
            Constr::Proj(ref o) => {
                let (ref p, ref c) = **o;
                let (env, ct) = self.execute(c)?;
                env.judge_of_projection(p, c, &ct)
            },
            Constr::Lambda(ref o) => {
                let (ref name, ref c1, ref c2) = **o;
                let mut ty = Constr::Rel(0); // dummy
                let (env, _) = self.execute_type(c1, &mut ty)?;
                env.push_rel(RDecl::LocalAssum(name.clone(), c1.clone()));
                let (env, j_) = env.execute(c2)?;
                // Make sure to unwind the rel_context on success.
                // Note that we currently don't pop the rel if there was an error, even if it
                // wasn't a TypeError that consumed the env.
                if let Some(RDecl::LocalAssum(name, c1)) = env.rel_context.pop() {
                    Ok((env, Constr::Prod(ORef(Arc::from((name, c1, j_))))))
                } else { unreachable!("env should be unchanged if the execute was successful.") }
            },
            Constr::Prod(ref o) => {
                let (ref name, ref c1, ref c2) = **o;
                let mut ty = Constr::Rel(0); // dummy
                let (env, varj) = self.execute_type(c1, &mut ty)?;
                env.push_rel(RDecl::LocalAssum(name.clone(), c1.clone()));
                let mut ty = Constr::Rel(0); // dummy
                let (env, varj_) = env.execute_type(c2, &mut ty)?;
                // Make sure to unwind the rel_context on success.
                // Note that we currently don't pop the rel if there was an error, even if it
                // wasn't a TypeError that consumed the env.
                env.rel_context.pop();
                let sort = env.sort_of_product(varj, varj_)?.into_owned();
                Ok((env, Constr::Sort(ORef(Arc::from(sort)))))
            },
            Constr::LetIn(ref o) => {
                let (ref name, ref c1, ref c2, ref c3) = **o;
                let (env, j1) = self.execute(c1)?;
                // c2 can be an inferred type => refresh (but the pushed type is still c2)
                let mut ty = Constr::Rel(0); // dummy
                // let env',c2' = (* refresh_arity env *) env, c2
                let (env, _) = env.execute_type(c2, &mut ty)?;
                let env = env.judge_of_cast(c1, &j1, Cast::DEFAULTCast, c2)?;
                env.push_rel(RDecl::LocalDef(name.clone(), c1.clone(),
                                             ORef(Arc::from(c2.clone()))));
                let (env, j_) = env.execute(c3)?;
                // Make sure to unwind the rel_context on success.
                // Note that we currently don't pop the rel if there was an error, even if it
                // wasn't a TypeError that consumed the env.
                env.rel_context.pop();
                Ok((env, j_.subst1(c1)?))
            },
            Constr::Cast(ref o) => {
                let (ref c, k, ref t) = **o;
                let (env, cj) = self.execute(c)?;
                let mut ty = Constr::Rel(0); // dummy
                let (env, _) = env.execute_type(t, &mut ty)?;
                let env = env.judge_of_cast(c, &cj, k, t)?;
                Ok((env, t.clone()))
            },
            // Inductive types
            Constr::Ind(ref o) => {
                let ty = self.judge_of_inductive(o)?;
                Ok((self, ty.into_owned()))
            },
            Constr::Construct(ref o) => { let ty = self.judge_of_constructor(o)?; Ok((self, ty)) },
            Constr::Case(ref o) => {
                let (ref ci, ref p, ref c, ref lf) = **o;
                let (env, cj) = self.execute(c)?;
                let (env, pj) = env.execute(p)?;
                let (env, lfj) = env.execute_array(lf)?;
                env.judge_of_case(ci, p, &pj, c, &cj, &lfj)
            },
            Constr::Fix(ref o) => {
                let Fix(Fix2(_, i), ref recdef) = **o;
                let i = usize::try_from(i).map_err(IdxError::from)?;
                let (env, fix_ty) = self.execute_recdef(recdef, i)?;
                let env = o.check(env)?;
                Ok((env, fix_ty.clone()))
            },
            Constr::CoFix(ref o) => {
                let CoFix(i, ref recdef) = **o;
                let i = usize::try_from(i).map_err(IdxError::from)?;
                let (env, fix_ty) = self.execute_recdef(recdef, i)?;
                let env = o.check(env)?;
                Ok((env, fix_ty.clone()))
            },
            // Partial proofs: unsupported by the kernel.
            // Constr::Meta(_),
            // Constr::Evar(_),
        }
    }

    /// NOTE: ty_ can start with any dummy value.
    ///
    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition: ∃ (ty' : constr) (s : sort), self ⊢ constr : ty' ∧ self ⊨ ty' ≡ Sort s
    fn execute_type<'a, 'e>(&'e mut self,
                            constr: &Constr,
                            ty: &'a mut Constr,
                           ) -> CaseResult<'e, 'b, 'g, (&'e mut Self, &'a Sort)> {
        let (env, ty_) = self.execute(constr)?;
        *ty = ty_.clone();
        env.type_judgment(constr, ty, &ty_)
    }

    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition:
    ///
    ///       ∃ vdefj : list constr,
    ///       len names = len lar = len larj = len vdef = len vdefj ∧ 0 ≤ i < len lar ∧
    ///       (∀ j : nat, 0 ≤ j < len lar → ∃ s : sort,
    ///        self ⊢ lar[j] : s ∧
    ///        push_rec_types self names lar ⊢ vdef[j] : vdefj[j] ∧
    ///        push_rec_types self names lar ⊨ vdefj[j] ≡ lift (len lar) lar[j])
    fn execute_recdef<'a, 'e>(&'e mut self, &PRec(ref names, ref lar, ref vdef): &'a PRec,
                              i: usize) -> CaseResult<'e, 'b, 'g, (&'e mut Self, &'a Constr)> {
        let (mut env, larj) = self.execute_array(lar)?;
        // Note that lar and larj necessarily have the same length, so we don't need to check.
        for (c, cj) in lar.iter().zip(larj.iter()) {
            let env_ = env;
            env = env_.assumption_of_judgment(c, cj)?;
        }
        // Note that lara = lar.
        let rdecl_orig_len = env.rel_context.len();
        if lar.len() != names.len() || lar.len() != vdef.len() {
            const ERR : &'static str = "execute_recdef: names, lar, and vdef length mismatch";
            return Err(Box::new(CaseError::Failure(ERR.into())))
        }
        env.push_rec_types(names.iter().map(Clone::clone), lar.iter(), Clone::clone)?;
        let (env, vdefj) = env.execute_array(vdef)?;
        // Note that vdef and vdefj necessarily have the same length, so we don't need to check.
        let env = env.type_fixpoint(names, lar, vdef, &vdefj)?;
        // Make sure to unwind the rel_context on success.
        // Note that we currently don't unwind the rel_context if there was an error, even if it
        // wasn't a TypeError that consumed the env.
        env.rel_context.truncate(rdecl_orig_len);
        if let Some(ar) = lar.get(i) { Ok((env, ar)) } else {
            const ERR : &'static str = "execute_recdef: i ≥ lar.len()";
            Err(Box::new(CaseError::Failure(ERR.into())))
        }
    }

    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition:
    ///
    ///       ∃ lcj : list constr, len lc = len lcj ∧
    ///       ∀ i : nat, 0 ≤ i < len lc → ∃ s : sort, self ⊢ lc[i] : lcj[i] ∧ self ⊢ lcj[i] : s
    fn execute_array<'e>(&'e mut self,
                         lc: &[Constr]) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Vec<Constr>)> {
        let mut lcj = Vec::with_capacity(lc.len());
        let mut env = self;
        for c in lc {
            let env_ = env;
            let (env_, cj) = env_.execute(c)?;
            env = env_;
            lcj.push(cj);
        }
        Ok((env, lcj))
    }

    /// Derived functions

    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition: ∃ (ty : constr) (s : sort), self ⊢ cstr : ty ∧ self ⊢ ty : s.
    pub fn infer<'e>(&'e mut self,
                     constr: &Constr) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)> {
        self.execute(constr)
    }

    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition: ∃ s : sort, self ⊢ constr : Sort s
    pub fn infer_type<'e>(&'e mut self,
                          constr: &Constr) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Sort)> {
        let mut ty = Constr::Rel(0); // dummy
        self.execute_type(constr, &mut ty).map( |(env, sort)| (env, sort.clone()) )
    }

    /// Typing of several terms.
    ///
    /// NOTE: rels should be reversed compared to the order in the OCaml version.
    ///
    /// NOTE: Precondition: self is well-formed (FIXME: precise definition).
    ///
    /// NOTE: Postcondition: Loosely speaking: each local definition in rels is
    ///       well-typed in the context of all the previous definitions, and env
    ///       includes all the definitions in rels.
    pub fn check_ctxt<'e, I>(&'e mut self,
                             rels: I) -> CaseResult<'e, 'b, 'g, &'e mut Self>
        where
            I: Iterator<Item=RDecl>,
    {
        // fold_rel_context goes backwards; since rels is reversed, we go forwards on it.
        let mut env = self;
        for d in rels {
            let env_ = env;
            env = match d {
                RDecl::LocalAssum(_, ref ty) => { let (env_, _) = env_.infer_type(ty)?; env_ },
                RDecl::LocalDef(_, ref bd, ref ty) => {
                    let (env_, j1) = env_.infer(bd)?;
                    // FIXME: Why not infer_type?
                    let (env_, _) = env_.infer(ty)?;
                    // NOTE: In the OCaml, we just call conv_leq, but this gives a more consistent
                    // error message.
                    env_.judge_of_cast(bd, &j1, Cast::DEFAULTCast, ty)?
                },
            };
            env.push_rel(d)
        }
        Ok(env)
    }

    /// Polymorphic arities utils
    ///
    /// NOTE: Precondition: ∃ ty : constr, self ⊢ ar : ty
    ///
    /// NOTE: Postcondition:
    ///
    ///       ∃ (ctx : rel_context),
    ///       self ⊨ ar ≡ mk_arity ctx (Sort (Type [u]))
    fn check_kind<'a, 'e, I>(&self, ar: Constr, u: Level, prefix: I) -> CaseResult<'e, 'b, 'g, ()>
        where
            I: Iterator<Item=&'a RDecl> + Clone,
    {
        // TODO: We don't really need to allocate the vector returned by dest_prod here; we can
        // just reuse the vector in check_polymorphic_arity instead.
        if let Constr::Sort(ref o) = self.dest_prod(ar, prefix)?.1 {
            if let Sort::Type(ref u_) = **o {
                if u_.equal(&Univ::make(u, &self.globals.univ_hcons_tbl)?) { return Ok(()) }
            }
        }
        return Err(Box::new(CaseError::Failure("not the correct sort".into())))
    }

    /// NOTE: params should be reversed compared to the order in the OCaml version.
    ///
    /// NOTE: Precondition: len par.param_levels ≤ len params
    ///
    /// NOTE: Precondition:
    ///
    /// ∀ i : nat, 0 ≤ i < len par.param_levels →
    /// ∃ u : level, par.param_levels[i] = Some u →
    /// ∃ ty : constr, params[i] = LocalAssum(_, ty) →
    /// ∃ s : constr, self; params[0..i] ⊢ ty : s
    ///
    /// NOTE: Postcondition:
    ///
    /// ∀ i : nat, 0 ≤ i < len par.param_levels →
    /// ∃ u : level, par.param_levels[i] = Some u →
    /// ∃ (ty : constr) (ctx : rel_context),
    /// params[i] = LocalAssum(_, ty) ∧
    /// self; params[0..i] ⊨ ty ≡ mk_arity ctx (Sort (Type [u]))
    pub fn check_polymorphic_arity<'e, I>(&self, mut params: I,
                                          par: &PolArity) -> CaseResult<'e, 'b, 'g, ()>
        where
            I: Iterator<Item=RDecl>,
    {
        const ERR : &'static str = "check_poly: not the right number of params";
        let pl = &par.param_levels;
        let mut rels = Vec::new();
        // NOTE: In the OCaml version, params is reversed before iterating, but here the iterator
        // is already reversed so we do nothing.
        for p in pl.iter() {
            let d = params.next().ok_or_else(|| Box::new(CaseError::Failure(ERR.into())))?;
            if let Some(ref u) = *p {
                if let RDecl::LocalAssum(_, ref ty) = d {
                    self.check_kind(ty.clone(), u.clone(), rels.iter())?
                } else { return Err(Box::new(CaseError::Failure(ERR.into()))) }
            }
            rels.push(d);
        }
        Ok(())
    }
}
