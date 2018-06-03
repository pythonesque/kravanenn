use coq::checker::univ::{
    Huniv,
    SubstError,
    SubstResult,
    UConstraint,
    UContext,
    UndoLog,
    UnivConstraintResult,
    Universes,
};
use coq::kernel::esubst::{
    Idx,
    IdxResult,
};
use coq::kernel::names::{
    CMapEnv,
    KnKey,
    KnMap,
    KnUser,
    MindMapEnv,
    // MpMap,
    MutInd,
};
use ocaml::values::{
    Cb,
    Constr,
    Cst,
    CstType,
    CstDef,
    Engagement,
    Ind,
    IndPack,
    Instance,
    Kn,
    // ModType,
    // Module,
    Name,
    ProjBody,
    PUniverses,
    // Rctxt,
    RDecl,
    // VoDigest,
};
use std::borrow::{Borrow, Cow};
use std::collections::{HashSet};
use std::collections::hash_map::{self};
use std::fmt::{self};
use util::nonzero::{NonZero};

/// Environments

#[derive(Default)]
pub struct Globals<'g> {
    constants: CMapEnv<'g, &'g Cb>,
    inductives: MindMapEnv<'g, &'g IndPack>,
    inductives_eq: KnMap<'g, Kn>,
    /// Hash-consed universe table.
    pub univ_hcons_tbl: Huniv,
    // modules: MpMap<Module>,
    // modtypes: MpMap<ModType>,
}

pub struct Stratification<'g> {
    universes: Universes<'g>,
    enga: Engagement,
}

pub struct Env<'b, 'g> where 'g: 'b {
    /// Will let us easily keep the globals the same (without copying) while recreating the
    /// rel_context.  We want to divorce the rel_context lifetimes from the global lifetimes
    /// so we can drop the Env without unifying the lifetime of the globals with it.
    pub globals: &'b mut Globals<'g>,
    /// NOTE: We will probably make this something we clone somewhat regularly, since we often
    /// want to keep the rest of the Env the same but mutate the Rctxt.  So we might make this
    /// into a &'r mut Rctx<'b> or something.
    /// NOTE: We currently use Vec<RDecl> instead of RCtxt, just because it's somewhat easier
    /// to deal with.  We can always change it later.  Just keep in mind that the head of the
    /// list is the last element of the vector.
    pub rel_context: &'b mut Vec<RDecl>,
    pub stratification: Stratification<'g>,
    // imports: MpMap<VoDigest>,
}

impl<'e, 'b, 'g> fmt::Debug for Env<'b, 'g> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Env {{ rdecls: {:?}, ... }}", self.rel_context)
    }
}


#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstEvaluationResult {
    NoBody,
    Opaque,
    Subst(SubstError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EnvError {
    Anomaly(String),
    NotEvaluableConst(ConstEvaluationResult),
}

pub type EnvResult<T> = Result<T, EnvError>;

impl ::std::convert::From<SubstError> for ConstEvaluationResult {
    fn from(e: SubstError) -> Self {
        ConstEvaluationResult::Subst(e)
    }
}

impl Cb {
    fn constraints_of<'a>(&'a self, u: &'a Instance) -> SubstResult<HashSet<UConstraint<'a>>> {
        let univs = &self.universes;
        univs.1.subst_instance(u)
    }
}

impl CstType {
    /// NOTE: Panics if self is not a RegularArity.
    fn map_regular_arity<F, E>(&self, f: F) -> Result<Cow<Self>, E>
        where
            F: FnOnce(&Constr) -> Result<Cow<Constr>, E>,
    {
        match *self {
            CstType::RegularArity(ref a) => f(a).map( |a_| match a_ {
                Cow::Borrowed(a_) if a_ as *const _ == a as *const _ => Cow::Borrowed(self),
                a_ => Cow::Owned(CstType::RegularArity(a_.into_owned())),
            }),
            CstType::TemplateArity(_) => panic!("map_regular_arity: expected a RegularArity."),
        }
    }
}

impl<'g> Globals<'g> where {
    /// Constants

    /// Global constants
    pub fn lookup_constant(&self, c: &Cst) -> Option<&'g Cb> {
        self.constants.get(&KnUser(c)).map( |&cb| cb )
    }

    /// constant_type gives the type of a constant
    ///
    /// NOTE: Unlike the OCaml implementation, this returns None if the constant is not found,
    /// rather than throwing Not_found.
    ///
    /// NOTE: Panics if the looked-up constant body cb has cb.polymorphic true,
    /// but cb.ty is not a RegularArity.
    pub fn constant_type<'a>(&self, cons: &'a PUniverses<Cst>
                            ) -> Option<SubstResult<(Cow<'g, CstType>, HashSet<UConstraint<'a>>)>>
        where 'g: 'a,
    {
        let PUniverses(ref kn, ref u) = *cons;
        self.lookup_constant(kn)
            .map( |cb| {
                if cb.polymorphic {
                    let csts = cb.constraints_of(u)?;
                    cb.ty.map_regular_arity( |c| c.subst_instance(u, &self.univ_hcons_tbl) )
                      .map( |ty| (ty, csts) )
                } else { Ok((Cow::Borrowed(&cb.ty), HashSet::new())) }
            })
    }

    pub fn constant_value(&self, o: &PUniverses<Cst>) ->
        Option<Result<Cow<'g, Constr>, ConstEvaluationResult>>
    {
        let PUniverses(ref kn, ref u) = *o;
        self.lookup_constant(kn)
            .and_then( |cb| {
                Some(match cb.body {
                    CstDef::Def(ref l_body) => {
                        // l_body is lazily initialized, and this is the only place that tries to
                        // force it.
                        let b = l_body.get_or_create( |mut l_body| {
                            l_body.force_constr();
                            if cb.polymorphic {
                                // FIXME: Why do we do this twice?
                                l_body.force_constr();
                            }
                            l_body.value
                        });
                        if cb.polymorphic {
                            match b.subst_instance(u, &self.univ_hcons_tbl) {
                                Ok(b) => Ok(b),
                                Err(e) => Err(ConstEvaluationResult::Subst(e)),
                            }
                        } else {
                            Ok(Cow::Borrowed(&**b))
                        }
                    },
                    CstDef::OpaqueDef(_) =>
                        Err(ConstEvaluationResult::NoBody),
                    CstDef::Undef(_) =>
                        Err(ConstEvaluationResult::Opaque),
                })
            })
    }

    pub fn lookup_projection(&self, p: &Cst) -> Option<EnvResult<&'g ProjBody>> {
        // NOTE: Altered from OCaml implementation to not require p to be a Proj, since sometimes
        // we only have a constant (for instance, when checking a projection invented for eta
        // expansion of primitive records).
        self.lookup_constant(&p)
           .map( |p| p.proj.as_ref().ok_or_else( || {
               let e = "lookup_projection: constant is not a projection";
               EnvError::Anomaly(e.into())
           }))
    }

    /// Inductives

    /// Mutual Inductives
    fn scrape_mind<'a>(&'a self, kn: &'a Kn) -> &'a Kn {
        self.inductives_eq.get(&KnKey(kn)).unwrap_or(kn)
    }

    pub fn mind_equiv(&self, ind1: &Ind, ind2: &Ind) -> bool {
        ind1.pos == ind2.pos &&
        self.scrape_mind(ind1.name.user()).equal(self.scrape_mind(ind2.name.user()))
    }

    pub fn lookup_mind(&self, kn: &MutInd) -> Option<&'g IndPack>
    {
        self.inductives.get(&KnUser(kn)).map( |&v| v )
    }

    pub fn add_mind(&mut self, kn: &'g MutInd, mib: &'g IndPack) -> EnvResult<()> {
        let Globals { ref mut inductives, ref mut inductives_eq, .. } = *self;
        let v = if let hash_map::Entry::Vacant(v) = inductives.entry(KnUser(kn)) { v } else {
            return Err(EnvError::Anomaly(format!("Inductive {:?} is already defined", kn)))
        };
        v.insert(mib);
        let kn1 = kn.user();
        let kn2 = kn.canonical();
        if !kn1.equal(kn2) {
            inductives_eq.insert(KnKey(kn1), kn2.clone());
        }
        Ok(())
    }
}

impl<'g> Stratification<'g> {
    pub fn universes(&self) -> &Universes<'g> {
        &self.universes
    }

    pub fn engagement(&self) -> &Engagement {
        &self.enga
    }

    /* pub fn add_constraints<'a, I>(&mut self, c: I,
                                  log: &mut UndoLog<'g>) -> UnivConstraintResult<()>
        where
            I: Iterator<Item=&'a UConstraint<'a>>,
    {
        self.universes.merge_constraints(c, log)
    } */

    pub fn push_context(&mut self, strict: bool, ctx: &UContext<'g>,
                        log: &mut UndoLog<'g>) -> UnivConstraintResult<()>
    {
        self.universes.merge_context(strict, ctx, log)
    }
}

impl<'b, 'g> Env<'b, 'g> {
    /// Rel context

    pub fn lookup_rel(&self, n: Idx) -> Option<&RDecl> {
        // Casts from u32 to usize are always legal (TODO: verify this).
        let n = u32::from(n) as usize;
        // Unlike the OCaml implementation, we can just index directly into rel_context.  We
        // just have to take into account that rel_context is reversed from the OCaml
        // implementation; instead of the nth element of the list, it's the rel_context.len() - nth
        // element of the list.  If the subtraction succeeded, we know that 0 ≤ idx, and since
        // idx = self.rel_context.len() - n where n is positive, idx < self.rel_context.len(),
        // so idx is in bounds for self.rel_context; hence, the array index should always
        // succeed inside the map.
        self.rel_context.len().checked_sub(n).map( |idx| &self.rel_context[idx] )
    }

    pub fn push_rel(&mut self, d: RDecl) {
        self.rel_context.push(d);
    }

    /// NOTE: This expects ctxt to be passed in reverse order from the OCaml version.
    pub fn push_rel_context<I>(&mut self, ctxt: I)
        where
            I: Iterator<Item=RDecl>,
    {
        // The OCaml version calls fold_rel_context, which iterates ctxt in reverse; since we
        // are passed an iterator that is already in reverse order, we just iterate normally.
        for d in ctxt {
            self.push_rel(d);
        }
    }

    /// NOTE: Unlike the OCaml version, this does not check that lna and typarray have the same
    /// length; if this needs to be enforced, it should be checked by the caller.
    pub fn push_rec_types<I1, I2, T2, F2>(&mut self, lna: I1, typarray: I2,
                                          mut to_owned: F2) -> IdxResult<()>
        where
            I1: Iterator<Item=Name>,
            I2: Iterator<Item=T2>,
            T2: Borrow<Constr>,
            F2: FnMut(T2) -> Constr,
    {
        for (i, (na, t)) in lna.zip(typarray).enumerate() {
            // TODO: Should only need to check in-bounds-ness of idxs once.
            self.push_rel(RDecl::LocalAssum(na, if let Some(i) = NonZero::new(i) {
                t.borrow().lift(Idx::new(i)?)?
            } else { to_owned(t) }))
        }
        Ok(())
    }
}
