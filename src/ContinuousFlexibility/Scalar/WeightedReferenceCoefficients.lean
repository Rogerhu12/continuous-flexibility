module

public import ContinuousFlexibility.Scalar.WeightedReferenceBounds

/-!
# Reference coefficient losses cost one material envelope

The exponent in a cell estimate may depend on the derivative order.  It is
absorbed before the Sobolev order is counted: every fixed reciprocal-profile
jet costs one power of `M`, rather than a number of powers depending on the
jet order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (materialE0 materialE0Exponent materialLogFactor)

/-- A cell index at most twice the material endpoint coordinate incurs a fixed
power of `E0`.  The power is selected before the index and coordinate. -/
theorem radialE_rpow_le_materialE0_rpow {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : ℝ), 0 ≤ x → (n : ℝ) ≤ 2 * x →
      radialE n ^ A ≤ materialE0 x ^ B := by
  let p : ℝ := 5 / 2
  let c : ℝ := (2 : ℝ) ^ p * (Real.log 2 + 1)
  have hp : 0 ≤ p := by norm_num [p]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  refine ⟨c * A, mul_nonneg hc hA, fun n x hx hn => ?_⟩
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have he : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos _) hx
  have hen : 0 < Real.exp 1 + (n : ℝ) := add_pos_of_pos_of_nonneg (Real.exp_pos _) hn0
  have hlogx : 1 ≤ Real.log (Real.exp 1 + x) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.exp 1 + x) :=
        Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_right hx)
  have hlogn : 0 ≤ Real.log (Real.exp 1 + (n : ℝ)) := by
    apply Real.log_nonneg
    have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    linarith only [hexp, hn0]
  have hlog : Real.log (Real.exp 1 + (n : ℝ)) ≤
      (Real.log 2 + 1) * Real.log (Real.exp 1 + x) := by
    calc
      _ ≤ Real.log (2 * (Real.exp 1 + x)) := Real.log_le_log hen (by
        linarith only [hn, (Real.exp_pos (1 : ℝ))])
      _ = Real.log 2 + Real.log (Real.exp 1 + x) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) he.ne']
      _ ≤ _ := by nlinarith only [mul_nonneg hlog2 (sub_nonneg.mpr hlogx)]
  have hpow : (n : ℝ) ^ p ≤ (2 : ℝ) ^ p * x ^ p := by
    calc
      _ ≤ (2 * x) ^ p := Real.rpow_le_rpow hn0 hn hp
      _ = _ := Real.mul_rpow (by norm_num) hx
  have hq : (n : ℝ) ^ p * Real.log (Real.exp 1 + (n : ℝ)) ≤
      c * (x ^ p * Real.log (Real.exp 1 + x)) := by
    calc
      _ ≤ ((2 : ℝ) ^ p * x ^ p) *
          ((Real.log 2 + 1) * Real.log (Real.exp 1 + x)) :=
        mul_le_mul hpow hlog hlogn
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hx _))
      _ = _ := by dsimp only [c]; ring
  simp only [radialE, radialQ, materialE0, materialE0Exponent, materialLogFactor,
    ← Real.exp_mul, Real.exp_le_exp]
  change ((n : ℝ) ^ p * Real.log (Real.exp 1 + (n : ℝ))) * A ≤
    (1 + x ^ p * Real.log (Real.exp 1 + x)) * (c * A)
  nlinarith only [mul_le_mul_of_nonneg_right hq hA, mul_nonneg hc hA]

/-- One material `M` absorbs any fixed power of the discrete reference
coefficient, uniformly over every actual cell. -/
theorem referenceCellCoefficient_le_materialM {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      radialE (D.cellIndex m) ^ A ≤ K * T.M r := by
  classical
  obtain ⟨C, hC⟩ := hD
  obtain ⟨B, _, hB⟩ := radialE_rpow_le_materialE0_rpow hA
  obtain ⟨δ, hδ, hcoord⟩ := material_referenceCell_endpoint_coordinate hT
  obtain ⟨L, hL, hLbound⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 B
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ radialCore D := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hfinite : {m | (D.cells m ∩ middle).Nonempty}.Finite :=
    hC.2.2.2.2.2.1 middle isCompact_Icc hmiddle
  obtain ⟨R, hR⟩ := (hfinite.image (fun m => radialE (D.cellIndex m) ^ A)).bddAbove
  refine ⟨max L (max R 1), hL.trans_le (le_max_left _ _), fun m r hrm => ?_⟩
  have hr : r ∈ Ioo D.a D.b := hC.2.1.2.2.2.1 m hrm
  have hM : 1 ≤ T.M r := (hT.2.1 r hr).2.2.2
  by_cases hn : endpointDistance D r < δ
  · obtain ⟨x, hx, hm, _, hE⟩ := hcoord m r hr hrm hn
    calc
      _ ≤ materialE0 x ^ B := hB (D.cellIndex m) x hx hm
      _ = T.E0 r ^ B := by rw [hE]
      _ ≤ L * T.M r := hLbound r hr
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hM)
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hn
    have hrmid : r ∈ middle := by
      exact ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hmR : radialE (D.cellIndex m) ^ A ≤ R :=
      hR ⟨m, ⟨r, hrm, hrmid⟩, rfl⟩
    calc
      _ ≤ max L (max R 1) := hmR.trans ((le_max_left _ _).trans (le_max_right _ _))
      _ ≤ max L (max R 1) * T.M r := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hM
          (hL.le.trans (le_max_left _ _))

/-- Uniform, order-independent envelope loss for the actual reciprocal
reference jets.  Only the multiplicative constant depends on the jet order. -/
theorem referenceInverseJet_le_materialM {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r ∈ Ioo D.a D.b,
      |radialJet n (fun t => (D.w t)⁻¹) r| ≤ K * T.M r := by
  obtain ⟨C, hC⟩ := hD
  have hCn := hC.2.2.1 n
  have hjets := hC.2.2.2.2.2.2.2.2.2.1
  obtain ⟨K, hK, hKbound⟩ := referenceCellCoefficient_le_materialM ⟨C, hC⟩ hT hCn.le
  refine ⟨C n * K, mul_pos hCn hK, fun r hr => ?_⟩
  obtain ⟨m, hrm⟩ := hC.2.1.exists_cell hr
  calc
    _ ≤ C n * radialE (D.cellIndex m) ^ (C n) := hjets m r hrm n
    _ ≤ C n * (K * T.M r) := mul_le_mul_of_nonneg_left (hKbound m r hrm) hCn.le
    _ = _ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Statements
