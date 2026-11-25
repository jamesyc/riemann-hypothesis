module

public import Riemann.Windows

public section

theorem riemannHypothesis : RiemannHypothesis :=
  Riemann.riemannHypothesis_of_zetaNonvanishing Riemann.zeta_and_primitive_nonvanishing.1

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine :=
  riemannHypothesis

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
  Riemann.dirichletLNonvanishing_of_primitive Riemann.zeta_and_primitive_nonvanishing.2

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  Riemann.primitiveDirichletLZerosOnLine_of_nonvanishing Riemann.zeta_and_primitive_nonvanishing.2

theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  Riemann.dirichletLZerosOnLine_of_primitive LFunction_eq_zero_re_of_isPrimitive
