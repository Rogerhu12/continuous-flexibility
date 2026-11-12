import ContinuousFlexibility.Analysis.N06CurrentNegativeTwoHalf
import ContinuousFlexibility.Analysis.N06CanonicalPotentialPeriodicity

/-!
# Negative Green for the original full-period test class

The original N03 source property and N04 operator identity imply actual
potential periodicity. Hence the genuine two-half defect vanishes, and
the finite negative Green identity and its bulk limit apply to every
original `RadialTest`, without an added operator-periodicity hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The actual original contracts force the displayed defect to vanish;
this is not an additional coefficient assumption. -/
theorem n06_negativeHalfPeriodDefect_eq_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    n06NegativeHalfPeriodDefect S K z m φ p = 0 := by
  simp only [n06NegativeHalfPeriodDefect,
    n06_canonicalPotential_periodicOn hT hS h03 h04 hz hs m hp,
    sub_self, zero_mul, zero_div]

/-- The actual negative source of the full test average equals the
source of the operator on the averaged test, on the original open piece. -/
theorem n06_negative_current_source_average
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p =
      canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p := by
  rw [n06_negative_current_twoHalf_source h04 hz hs hm hφ hp,
    n06_negativeHalfPeriodDefect_eq_zero hT hS h03 h04 hz hs hp, sub_zero]

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- Every actual finite modal reconstruction satisfies the negative
Green identity for the original full-period physical test. The source
transform contains the average of the true `L phi`, as required by the
original full physical pairing. -/
theorem N06NegativeGraphApproximation.current_fullPeriod_green
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ))
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ) (N : ℕ) :
    (∫ p, (n06NegativeFinitePrincipal P.modes N p +
        K.potential z m p * n06NegativeFiniteValue P.modes N p) *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, n06NegativeFiniteValue P.modes N p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (Q.value (K.right m, θ) *
            radialPartial (n06NegativeFiniteValue P.modes N) (K.right m, θ) -
          n06NegativeFiniteValue P.modes N (K.right m, θ) * Q.radial (K.right m, θ)) -
        (Q.value (K.left m, θ) *
            radialPartial (n06NegativeFiniteValue P.modes N) (K.left m, θ) -
          n06NegativeFiniteValue P.modes N (K.left m, θ) * Q.radial (K.left m, θ)) := by
  rw [P.current_twoHalf_green Q h04 hz hs hm hφ N]
  have hzdef : (∫ p, n06NegativeFiniteValue P.modes N p *
      n06NegativeHalfPeriodDefect S K z m φ p ∂canonicalMeasure S K m) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06_negativeHalfPeriodDefect_eq_zero hT hS h03 h04 hz hs ⟨hp.1, mem_univ _⟩,
      mul_zero]
    rfl
  rw [hzdef, add_zero]

/-- Both full-period physical bulk pairings converge before any
all-mode trace is taken. Finite actual interface cancellation can be
applied before this limit. -/
theorem N06NegativeGraphApproximation.current_fullPeriod_bulk_tendsto
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ) :
    Tendsto (fun N =>
      (∫ p, (n06NegativeFinitePrincipal P.modes N p +
          K.potential z m p * n06NegativeFiniteValue P.modes N p) *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, n06NegativeFiniteValue P.modes N p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m)) atTop
      (𝓝 ((∫ p, (G p + K.potential z m p * U p) *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      ∫ p, U p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m)) := by
  have hpair (w : PolarPoint → ℝ) :
      (∫ p, w p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ p, w p * canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p
          ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06_negative_current_source_average hT hS h03 h04 hz hs hm hφ ⟨hp.1, mem_univ _⟩]
  simp_rw [hpair]
  exact P.current_bulk_tendsto h04 hz hs hm (n06_radialTestAverage_test hφ).1

end ContinuousFlexibility.Analysis
