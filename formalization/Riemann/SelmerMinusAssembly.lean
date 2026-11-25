module

public import Riemann.SelmerTwistBernoulliBudget
public import Riemann.SelmerStickelbergerReciprocity
import Utilities.UnramifiedIdeleArtin

@[expose] public section

namespace Riemann

/-- The arithmetic layer comparison and principal reciprocity supply
the two parts of the minus estimate in Theorem 17.12. -/
theorem numberField_selmer_minus_estimate_of_arithmeticLayers_principalReciprocity
    (hLayers : HasSelmerSharedTwistArithmeticBernoulliComparison)
    (hReciprocity : Utilities.HasTotallyComplexUnramifiedPrincipalReciprocity) :
    HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_comparison_principalReciprocity
    (selmerBernoulliValuationComparison_of_sharedTwist
      (selmerSharedTwistBernoulliComparison_of_arithmeticLayers hLayers))
    hReciprocity

/-- The minus estimate only needs the noncyclotomic arithmetic layer
comparison and principal-ideal reciprocity. -/
theorem numberField_selmer_minus_estimate_of_noncyclotomicLayers_principalReciprocity
    (hLayers : HasSelmerSharedTwistNoncyclotomicArithmeticBernoulliComparison)
    (hReciprocity : Utilities.HasTotallyComplexUnramifiedPrincipalReciprocity) : HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_arithmeticLayers_principalReciprocity
    (selmerSharedTwistArithmeticBernoulliComparison_of_noncyclotomic hLayers) hReciprocity

/-- The noncyclotomic arithmetic comparison for the prime-to-host-degree terms. -/
theorem selmer_noncyclotomic_arithmetic_bernoulli_comparison :
    HasSelmerSharedTwistNoncyclotomicArithmeticBernoulliComparison := by
  intro target ht e q d he hp i hi
  dsimp only
  intro ℓ _ hodd hdegree O _ _ _ ψ hψ hunit m
  exact selmerSharedTwistArithmeticBernoulliBound_of_frobeniusBudget target e q d ℓ i O ψ m hi hψ
    (selmer_noncyclotomic_frobeniusBudgets target ht e q d he hp i hi ℓ hodd hdegree O ψ hψ hunit m)

/-- The arithmetic minus estimate, Theorem 17.12(II). -/
theorem numberField_selmer_minus_estimate : HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_noncyclotomicLayers_principalReciprocity
    selmer_noncyclotomic_arithmetic_bernoulli_comparison
    Utilities.totallyComplex_unramified_principal_reciprocity

end Riemann
