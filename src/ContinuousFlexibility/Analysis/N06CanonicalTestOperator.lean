import ContinuousFlexibility.Analysis.N06CanonicalTestTransport
import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities

/-!
# The actual operator on transported compact tests

The zero extension agrees with the untruncated height pullback on a
neighborhood of every interior physical point. Actual Frechet derivative
germs therefore identify their divergences. Outside the piece the zero
germ makes the divergence zero. The original canonical source and operator
definitions then give their exact signed identity on the canonical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- Actual divergence depends only on the germ of its input function,
without a regularity assumption on the coefficients. -/
theorem n06_divergenceOperator_input_congr_germ
    (A : SymmetricCoefficients) {u v : PolarPoint → ℝ} {p : PolarPoint}
    (huv : u =ᶠ[𝓝 p] v) : divergenceOperator A u p = divergenceOperator A v p := by
  have hr : radialPartial u =ᶠ[𝓝 p] radialPartial v := by
    filter_upwards [huv.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (1, 0)) hq
  have ht : angularPartial u =ᶠ[𝓝 p] angularPartial v := by
    filter_upwards [huv.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (0, 1)) hq
  have hR : (fun q => A.a q * radialPartial u q + A.b q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => A.a q * radialPartial v q + A.b q * angularPartial v q) := by
    filter_upwards [hr, ht] with q hqr hqt
    rw [hqr, hqt]
  have hT : (fun q => A.b q * radialPartial u q + A.c q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => A.b q * radialPartial v q + A.c q * angularPartial v q) := by
    filter_upwards [hr, ht] with q hqr hqt
    rw [hqr, hqt]
  exact congrArg₂ (fun x y : ℝ => x + y)
    (congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (1, 0)) (hR.fderiv_eq (𝕜 := ℝ)))
    (congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (0, 1)) (hT.fderiv_eq (𝕜 := ℝ)))

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}

theorem n06CanonicalTestPullback_divergence_eq_of_mem
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (A : SymmetricCoefficients) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    divergenceOperator A (n06CanonicalTestPullback S K z m φ) p =
      divergenceOperator A (fun q => K.height z m q * φ (K.chart z m q)) p :=
  n06_divergenceOperator_input_congr_germ A
    (n06CanonicalTestPullback_eventuallyEq_of_mem hK hz hsector hp)

theorem n06CanonicalTestPullback_divergence_zero_of_not_mem
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) (A : SymmetricCoefficients)
    {p : PolarPoint} (hp : p ∉ physicalPieceOpen S K z m) :
    divergenceOperator A (n06CanonicalTestPullback S K z m φ) p = 0 := by
  exact (n06_divergenceOperator_input_congr_germ A
    (n06CanonicalTestPullback_eventually_zero_of_not_mem hK hz hsector hφ hp)).trans
      (divergenceOperator_const A 0 p)

/-- The physical compact test has exactly the canonical test operator,
with the original sign distinguishing the two cylinder types. -/
theorem n06CanonicalTestPullback_operator
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (if K.positive m then -1 else (1 : ℝ)) *
        canonicalSource S K z m
          (divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ)) p =
      canonicalOperator S K L z m φ p := by
  have hcharts := hK.charts z hz hsector m
  simp only [canonicalOperator, canonicalSource]
  rw [n06CanonicalTestPullback_divergence_eq_of_mem hK hz hsector _ (hcharts.2.1 hp)]

/-- In source coordinates the same identity is the actual canonical
divergence plus the correctly signed potential term. -/
theorem n06CanonicalTestPullback_source_divergence
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ)) p =
      divergenceOperator (K.coefficients z m) φ p +
        (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p * φ p := by
  have he := (n06CanonicalTestPullback_operator (L := L) (φ := φ) hA hz hsector hp).trans
    (hB.2.2.1 z hz hsector m φ hφ p hp)
  cases hm : K.positive m <;>
    simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at he ⊢ <;>
    linarith only [he]

end ContinuousFlexibility.Analysis
