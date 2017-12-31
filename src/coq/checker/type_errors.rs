use coq::checker::environ::{
    Env,
};
use coq::kernel::esubst::{
    Idx,
};
use ocaml::values::{
    CaseInfo,
    Constr,
    Ind,
    Int,
    Name,
    PUniverses,
    RDecl,
    SortFam,
    UnivConstraint,
};
use std::collections::{HashSet};

pub type UnsafeJudgment = (Constr, Constr);

/// Type errors.

/// NOTE: NotEnoughAbstractionInFixBody should only occur with "/i" Fix
/// notation i.
#[derive(Clone, Debug)]
pub enum GuardError {
    /// Fixpoints
    NotEnoughAbstractionInFixBody,
    RecursionNotOnInductiveType(Constr),
    /// We use Vec<RDecl> instead of Env here, because it appears to be the part
    /// that actually changes during fixpoint typechecking; moreover, Env
    /// includes some components that might be expensive to copy or have too-
    /// short lifetimes for error messages.
    /// (Though it's worth noting that sometimes allocating the Vec may be
    ///  overly expensive itself, since we sometimes catch errors during
    ///  fixpoint checks and then ignore the environment... TODO: investigate).
    RecursionOnIllegalTerm(Int, (Vec<RDecl>, Constr), Vec<Int>, Vec<Int>),
    NotEnoughArgumentsForFixCall(Int),
    /// CoFixpoints
    CoDomainNotInductiveType(Constr),
    NestedRecursiveOccurrences,
    UnguardedRecursiveCall(Constr),
    RecCallInTypeOfAbstraction(Constr),
    RecCallInNonRecArgOfConstructor(Constr),
    RecCallInTypeOfDef(Constr),
    RecCallInCaseFun(Constr),
    RecCallInCaseArg(Constr),
    RecCallInCasePred(Constr),
    NotGuardedForm(Constr),
    ReturnPredicateNotCoInductive(Constr),
}

#[derive(Clone, Copy, Debug)]
pub enum ArityError {
    NonInformativeToInformative,
    StrongEliminationOnNonSmallType,
    WrongArity,
}

#[derive(Clone, Debug)]
pub enum TypeErrorKind {
    UnboundRel(Idx),
    // UnboundVar(variable),
    NotAType(UnsafeJudgment),
    BadAssumption(UnsafeJudgment),
    ReferenceVariables(Constr),
    ElimArity(PUniverses<Ind>, Vec<SortFam>, Constr, UnsafeJudgment,
              Option<(SortFam, SortFam, ArityError)>),
    CaseNotInductive(UnsafeJudgment),
    WrongCaseInfo(Ind, CaseInfo),
    NumberBranches(UnsafeJudgment, usize),
    IllFormedBranch(Constr, usize, Constr, Constr),
    Generalization((Name, Constr), UnsafeJudgment),
    ActualType(UnsafeJudgment, Constr),
    CantApplyBadType((usize, Constr, Constr), UnsafeJudgment, Vec<UnsafeJudgment>),
    CantApplyNonFunctional(UnsafeJudgment, Vec<UnsafeJudgment>),
    IllFormedRecBody(GuardError, Vec<Name>, Int),
    IllTypedRecBody(usize, Vec<Name>, Vec<UnsafeJudgment>, Vec<Constr>),
    UnsatisfiedConstraints(HashSet<UnivConstraint>),
}

#[derive(Debug)]
pub struct TypeError<'e, 'b, 'g>(pub &'e mut Env<'b, 'g>, pub TypeErrorKind) where 'b: 'e, 'g: 'b,;

pub type TypeResult<'e, 'b, 'g, T> = Result<T, Box<TypeError<'e, 'b, 'g>>>;

pub fn error_unbound_rel<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                     n: Idx) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::UnboundRel(n)))
}

pub fn error_not_type<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                  j: UnsafeJudgment) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::NotAType(j)))
}

pub fn error_assumption<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                    j: UnsafeJudgment) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::BadAssumption(j)))
}

pub fn error_elim_arity<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                    ind: PUniverses<Ind>,
                                    aritylst: Vec<SortFam>,
                                    c: Constr,
                                    pj: UnsafeJudgment,
                                    okinds: Option<(SortFam, SortFam, ArityError)>,
                                   ) -> Box<TypeError<'e, 'b, 'g>>
{
    Box::new(TypeError(env, TypeErrorKind::ElimArity(ind, aritylst, c, pj, okinds)))
}

pub fn error_case_not_inductive<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                            j: UnsafeJudgment) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::CaseNotInductive(j)))
}

pub fn error_number_branches<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                         cj: UnsafeJudgment,
                                         expn: usize) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::NumberBranches(cj, expn)))
}

pub fn error_ill_formed_branch<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>, c: Constr, i: usize,
                                           actty: Constr,
                                           expty: Constr) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::IllFormedBranch(c, i, actty, expty)))
}

pub fn error_actual_type<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>, j: UnsafeJudgment,
                                     expty: Constr) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::ActualType(j, expty)))
}

pub fn error_cant_apply_not_functional<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                                   rator: UnsafeJudgment,
                                                   randl: Vec<UnsafeJudgment>,
                                                  ) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::CantApplyNonFunctional(rator, randl)))
}

pub fn error_cant_apply_bad_type<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>, t: (usize, Constr, Constr),
                                             rator: UnsafeJudgment, randl: Vec<UnsafeJudgment>,
                                            ) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::CantApplyBadType(t, rator, randl)))
}

pub fn error_ill_typed_rec_body<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>, i: usize, lna: Vec<Name>,
                                            vdefj: Vec<UnsafeJudgment>,
                                            vargs: Vec<Constr>) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::IllTypedRecBody(i, lna, vdefj, vargs)))
}

pub fn error_unsatisfied_constraints<'e, 'b, 'g>(env: &'e mut Env<'b, 'g>,
                                                 c: HashSet<UnivConstraint>,
                                                ) -> Box<TypeError<'e, 'b, 'g>> {
    Box::new(TypeError(env, TypeErrorKind::UnsatisfiedConstraints(c)))
}
