import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cCoefficientSampleBounds
import ContinuousFlexibility.Analysis.N01cOriginalCoefficientPowerBounds
import ContinuousFlexibility.Analysis.N01cCoefficientPointBounds
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison
import ContinuousFlexibility.Analysis.N01cWeightAbsorption
import ContinuousFlexibility.Analysis.N01cBoundsRestriction

/-!
# The actual coefficient-family tame estimate

The primitive inputs are the original N01a/N01b data, physical placement
of the controls, interior support of the fixed profile cutoff, and the
material normalization E0 ≥ 1. The conclusion is the exact coefficient
clause on one fixed smaller state neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

section FixedIndices

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
  (hB : N01PartB D S C base ε)
  (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
  (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
  (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
  (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
    ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
    pairGrading (stateGrading S) realGrading base x ≤ 1 →
    ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
      pairGrading (stateGrading S) realGrading (n + 4) x ≤
        B * R ^ ((n : ℝ) / ((s : ℝ) + 1)))

include hS hT hA hε hε2 hB hE hloc hχloc hI

/-- Pointwise weighted bounds for the actual reference-subtracted family,
including parameter order zero. -/
theorem coefficientFamily_point_bound (k s : ℕ) (i : Fin 3) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ annularOpen D,
      ∀ J : SmoothDirections (stateNeighborhood S C base ε) (coefficientFamily D S C i a b q),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → AnnularState S × ℝ,
        |J.D k z v| ≤ B * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact mixedPowerBounds_difference_point_bound
    (X := AnnularState S × ℝ)
    (p := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0)) (base := base) (loss := loss)
    (U := stateNeighborhood S C base ε) (Ω := annularOpen D)
    (H := fun q => T.H q.1 ^ (3 / 4 : ℝ)) (E := fun q => T.E0 q.1)
    (f := coefficientOriginalField D S C i) (F := coefficientFamily D S C i)
    (isOpen_Ioo.prod isOpen_univ)
    (fun z hz => contDiffOn_coefficientOriginalField hS hT hA hB i hz)
    (n01_originalCoefficientMixedSmoothDirections hS hT hA hB i)
    (originalCoefficient_mixedPowerBounds hS hT hA hε (hε2.trans (by norm_num))
      hB hE hloc hχloc hI i)
    (reference_mem_stateNeighborhood S C base hε)
    (fun z hz t ht => stateNeighborhood_reference_segment S C hz ht)
    (fun z hz => (jointStateGrading_displacement_lt_one hε2 hz).le)
    (fun q hq => Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _)
    (fun q hq => hE q.1 hq.1)
    (fun _ _ _ _ _ _ => rfl) k s

/-- The physical point estimate transfers to the prescribed cell sample,
with one common positive multiplier and exponent. -/
theorem coefficientFamilyTameBounds_of_spatialPowerInterpolation :
    CoefficientFamilyTameBounds D T S C base loss ε := by
  exact coefficientSampleBounds_of_pointBounds
    (X := AnnularState S × ℝ) hT hA.1.1 hE
    (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
    base loss (stateNeighborhood S C base ε) (coefficientFamily D S C)
    (fun i a b q hq => n01_coefficientFamilySmoothDirections hS hT hA hB hε i a b q hq)
    (coefficientFamily_point_bound hS hT hA hε hε2 hB hE hloc hχloc hI)

end FixedIndices

/-- The exact coefficient clause follows from the primitive localized
N01a/N01b data. One base, one loss and one radius precede all orders. -/
theorem n01_coefficientFamilyTameBounds_of_localization
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {originalBase : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C originalBase ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) :
    ∃ base loss : ℕ, originalBase ≤ base ∧
      CoefficientFamilyTameBounds D T S C base loss (min ε (1 / 2)) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact exists_base_ge_of_spatialPower_continuation
    (X := AnnularState S × ℝ)
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (jointStateGrading_hasInterpolation hS) originalBase 4
    (fun base loss =>
      CoefficientFamilyTameBounds D T S C base loss (min ε (1 / 2)))
    (fun base loss hb hI =>
      coefficientFamilyTameBounds_of_spatialPowerInterpolation
        hS hT hA (lt_min hε (by norm_num)) (min_le_right _ _)
        (n01PartB_mono hB hb (min_le_left ε (1 / 2))) hE hloc hχloc hI)

end ContinuousFlexibility.Statements
