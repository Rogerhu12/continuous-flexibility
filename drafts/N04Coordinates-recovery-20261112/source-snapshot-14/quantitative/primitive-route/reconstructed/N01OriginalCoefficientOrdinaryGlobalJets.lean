import ContinuousFlexibility.Analysis.N01OriginalCoefficientGlobalJets
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Ordinary jets of the actual coefficients on the full annulus

The fixed polar basis converts the already uniform mixed derivative
bound into ordinary jets. The original state neighborhood and loss are
unchanged, and no component, root, or material cell has been selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem originalCoefficient_ordinary_global_bound_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ A : ℕ → ℝ, (∀ n, 1 ≤ A n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ i : Fin 3, ∀ n : ℕ, ∀ q ∈ annularOpen D,
        ‖iteratedFDeriv ℝ n (canonicalCoefficientComponent i
          (originalCoefficients D S C z)) q‖ ≤
          A n * (1 + pairGrading (stateGrading S) realGrading (n + loss)
            (z - (C.referenceState, 0))) := by
  choose Q hQ hbound using fun n => originalCoefficient_global_bound_of_n01 hS hT hN n
  let A : ℕ → ℝ := fun n => 1 + (2 : ℝ) ^ n * Q n
  refine ⟨A, ?_, ?_⟩
  · intro n
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (by norm_num) _) (hQ n).le)
  intro z hz hs i n q hq
  let w : ℝ := 1 + pairGrading (stateGrading S) realGrading (n + loss)
    (z - (C.referenceState, 0))
  have hw : 0 ≤ w := add_nonneg zero_le_one (apply_nonneg _ _)
  have hf := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs i
  have hb : ‖iteratedFDeriv ℝ n (canonicalCoefficientComponent i
      (originalCoefficients D S C z)) q‖ ≤ (2 : ℝ) ^ n * (Q n * w) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative
      (isOpen_Ioo.prod isOpen_univ) hf n hq (mul_nonneg (hQ n).le hw)
    intro a b hab
    simpa only [Real.norm_eq_abs] using
      hbound n z hz hs i a b hab.le q hq
  calc
    _ ≤ (2 : ℝ) ^ n * (Q n * w) := hb
    _ = ((2 : ℝ) ^ n * Q n) * w := by ring
    _ ≤ A n * w := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) hw

end ContinuousFlexibility.Analysis
