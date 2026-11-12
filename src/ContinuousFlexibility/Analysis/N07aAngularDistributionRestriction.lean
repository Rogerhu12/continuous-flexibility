import ContinuousFlexibility.Analysis.N07aAngularIntervalRestriction
import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients
import ContinuousFlexibility.Analysis.N07aCanonicalTestOperator

/-!
# Restricting the actual coefficients and distribution equation

The smaller-strip objects are the ordinary measure restrictions of the
same L² classes. Coefficient values are unchanged, their multipliers
commute with restriction, and the actual divergence equation is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K J : CanonicalData S} {m n : ℕ}

def N07aCanonicalOpenCoefficient.restrict (χ : N07aCanonicalOpenCoefficient S K m)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m)) :
    N07aCanonicalOpenCoefficient S J n where
  value := χ.value
  smooth := χ.smooth.mono fun _ hp => ⟨hsub hp.1, mem_univ _⟩
  periodic := fun _ hp => χ.periodic _ ⟨hsub hp.1, mem_univ _⟩
  bounded := by
    intro a b
    obtain ⟨A, hA, hbound⟩ := χ.bounded a b
    exact ⟨A, hA, hbound.filter_mono (ae_mono (n07a_canonicalMeasure_mono hsub))⟩

theorem N07aCanonicalOpenCoefficient.restrict_mul
    (χ : N07aCanonicalOpenCoefficient S K m)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    (u : CanonicalL2 S K m) :
    n07aCanonicalRestrict hsub (χ.mul u) =
      (χ.restrict hsub).mul (n07aCanonicalRestrict hsub u) := by
  apply Lp.ext
  have hχ := (χ.mul_ae u).filter_mono (ae_mono (n07a_canonicalMeasure_mono hsub))
  filter_upwards [n07aCanonicalRestrict_ae hsub (χ.mul u), hχ,
    (χ.restrict hsub).mul_ae (n07aCanonicalRestrict hsub u),
    n07aCanonicalRestrict_ae hsub u] with p hleft hmul hright hvalue
  rw [hleft, hmul, hright, hvalue]
  rfl

/-- Compact tests on the smaller interval preserve the same original
symmetric divergence equation and the same restricted source. -/
theorem n07a_distribution_restrict
    (a b c : N07aCanonicalOpenCoefficient S K m)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo (K.left m) (K.right m))
    {u F : CanonicalL2 S K m}
    (heq : N07aCanonicalDistributionEquation S K m
      ⟨a.value, b.value, c.value⟩ u F) :
    N07aCanonicalDistributionEquation S J n ⟨a.value, b.value, c.value⟩
      (n07aCanonicalRestrict hsub u) (n07aCanonicalRestrict hsub F) := by
  intro φ hφ
  have htest := n07a_canonicalTest_divergence ⟨a.value, b.value, c.value⟩
    (a.restrict hsub).smooth (b.restrict hsub).smooth (c.restrict hsub).smooth
    (a.restrict hsub).periodic (b.restrict hsub).periodic (c.restrict hsub).periodic hφ
  rw [n07aCanonicalRestrict_pairing hsub u htest, n07aCanonicalRestrict_pairing hsub F hφ]
  exact heq φ (n07a_canonicalTest_mono hsub hφ)

end ContinuousFlexibility.Analysis
