use coq::checker::environ::{
    Env,
};
use coq::checker::inductive::{
    CaseError,
    CaseResult,
};
use coq::checker::reduction::{
    ConvError,
    ConvResult,
};
use coq::checker::type_errors::{
    error_assumption,
    error_not_type,
    error_unsatisfied_constraints,
};
use ocaml::values::{
    Constr,
    Cstrs,
    Sort,
};

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

    fn check_constraints<'e>(&'e mut self, cst: &Cstrs) -> CaseResult<'e, 'b, 'g, &'e mut Self>
    {
        if self.stratification.universes().check_constraints(cst.iter())? { Ok(self) }
        else { Err(Box::new(CaseError::Type(error_unsatisfied_constraints(self, cst.clone())))) }
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
}
