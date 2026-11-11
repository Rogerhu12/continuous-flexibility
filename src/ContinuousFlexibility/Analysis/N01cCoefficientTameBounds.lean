import ContinuousFlexibility.Analysis.N01cOriginalCoefficientPowerBounds
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
  have hH (q : PolarPoint) (hq : q ∈ annularOpen D) :
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _
  have hp := originalCoefficient_mixedPowerBounds
    hS hT hA hε (by linarith) hB hE hloc hχloc hI i
  obtain ⟨B, A, hB0, hA0, hb⟩ :=
    hp.positive_oneHigh hH (fun q hq => hE q.1 hq.1) (max 1 k) s
  refine ⟨2 * B, A, mul_pos (by norm_num) (zero_lt_one.trans_le hB0), hA0, ?_⟩
  intro a b hab q hq J z hz v
  let J0 := n01_originalCoefficientMixedSmoothDirections hS hT hA hB i a b q hq
  have href := reference_mem_stateNeighborhood S C base hε
  let f : (AnnularState S × ℝ) → ℝ :=
    fun y => mixedDerivative a b (coefficientOriginalField D S C i y) q
  let JD : SmoothDirections (stateNeighborhood S C base ε)
      (fun y => f y - f (C.referenceState, 0)) :=
    J.congr (fun y hy => by
      change mixedDerivative a b (fun t =>
        coefficientOriginalField D S C i y t -
          coefficientOriginalField D S C i (C.referenceState, 0) t) q = _
      exact mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (contDiffOn_coefficientOriginalField hS hT hA hB i hy)
        (contDiffOn_coefficientOriginalField hS hT hA hB i href) a b hq)
  let M : ℝ := B * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (zero_le_one.trans hB0) (hH q hq))
    (Real.rpow_nonneg (zero_le_one.trans (hE q.1 hq.1)) _)
  have hh := smoothDirections_difference_allOrders_bound J0
    (pairGrading (stateGrading S) realGrading) base (s + loss)
    (C.referenceState, 0) z hz
    (fun t ht => stateNeighborhood_reference_segment S C hz ht)
    (jointStateGrading_displacement_lt_one hε2 hz).le hM
    (fun j hj hjpos y hy w =>
      hb j hj hjpos a b hab q hq J0 y hy
        (jointStateGrading_displacement_lt_one hε2 hy).le w) JD v
  simpa only [JD, SmoothDirections.congr, Real.norm_eq_abs, M, mul_assoc] using hh

/-- The physical point estimate transfers to the prescribed cell sample,
with one common positive multiplier and exponent. -/
theorem coefficientFamilyTameBounds_of_spatialPowerInterpolation :
    CoefficientFamilyTameBounds D T S C base loss ε := by
  classical
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  intro k s
  choose c A hc hA0 hb using
    (fun i : Fin 3 => coefficientFamily_point_bound
      hS hT hA hε hε2 hB hE hloc hχloc hI k s i)
  let C0 : ℝ := 1 + ∑ i : Fin 3, c i
  let A0 : ℝ := ∑ i : Fin 3, A i
  have hC0 : 0 < C0 := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hc i).le))
  have hcC (i : Fin 3) : c i ≤ C0 :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAA (i : Fin 3) : A i ≤ A0 :=
    Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ i)
  obtain ⟨Cs, As, hCs, hAs, hsample⟩ :=
    materialCell_weight_comparison hT hA.1.1 (3 / 4 : ℝ) A0
  obtain ⟨B, hBpos, habsorb⟩ :=
    exists_sameConstant_materialWeight_bound (C0 * Cs) As (3 / 4 : ℝ)
  refine ⟨B, hBpos, ?_⟩
  intro m i a b q hab hqm
  have hpart : RadialPartition D := hA.1.1.choose_spec.2.1
  have hq : q ∈ annularOpen D := ⟨hpart.2.2.2.1 m hqm, mem_univ _⟩
  have hsm := materialSample_mem_radialCore hT hpart m
  let J := n01_coefficientFamilySmoothDirections hS hT hA hB hε i a b q hq
  refine ⟨J, fun z hz v => ?_⟩
  let W : ℝ := oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
    base (s + loss) (z - (C.referenceState, 0)) v
  have hW : 0 ≤ W := oneHighVariationWeight_nonneg _ _ _ _ _
  have hHq : 0 ≤ T.H q.1 ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _
  have hEq : 0 ≤ T.E0 q.1 ^ A i :=
    Real.rpow_nonneg (zero_le_one.trans (hE q.1 hq.1)) _
  have henv :
      c i * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A i ≤
        C0 * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A0 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcC i) hHq)
      (Real.rpow_le_rpow_of_exponent_le (hE q.1 hq.1) (hAA i))
      hEq (mul_nonneg hC0.le hHq)
  calc
    _ ≤ c i * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A i * W :=
      hb i a b hab q hq J z hz v
    _ ≤ C0 * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A0 * W :=
      mul_le_mul_of_nonneg_right henv hW
    _ = C0 * (T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A0) * W := by ring
    _ ≤ C0 * (Cs * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ As) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsample m q.1 hqm).1 hC0.le) hW
    _ = (C0 * Cs) * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ As * W := by ring
    _ ≤ _ := habsorb (T.H (T.sample m)) (T.E0 (T.sample m)) W
      (hT.2.1 _ hsm).2.1.le (hE _ hsm) hW

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
  obtain ⟨b, loss, hIb⟩ := exists_seminorm_spatialPower_bound
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (jointStateGrading_hasInterpolation hS) 4
  let base := max originalBase b
  have hε' : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  have hB' := n01PartB_mono hB (le_max_left originalBase b) (min_le_left ε (1 / 2))
  refine ⟨base, loss, le_max_left _ _, ?_⟩
  apply coefficientFamilyTameBounds_of_spatialPowerInterpolation hS hT hA hε'
    (min_le_right _ _) hB' hE hloc hχloc
  intro s
  obtain ⟨B, hB0, hb⟩ := hIb s
  refine ⟨B, hB0, fun n hn x hx R hR hh => ?_⟩
  exact hb n hn x
    (((jointStateGrading_monotone S (le_max_right originalBase b)) x).trans hx) R hR hh

end ContinuousFlexibility.Statements
