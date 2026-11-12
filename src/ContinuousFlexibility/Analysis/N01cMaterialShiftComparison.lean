import ContinuousFlexibility.Analysis.AffineMaterialSampling
import ContinuousFlexibility.Analysis.ControlCellEndpointBounds

/-!
# Material weight comparison preserving the height exponent

A bounded change of the endpoint coordinate changes the cubic logarithm
of `H` by a quadratic error. The coefficient envelope absorbs that error.
Thus cell-to-cell comparisons can retain the exact height exponent rather
than lose a fraction of it. The estimates below reuse the explicit scalar
bounds already proved for material sampling.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

/-- A bounded coordinate shift preserves every real power of the height
weight, with a fixed power of the coefficient envelope. -/
theorem materialH_rpow_le_of_bounded_shift (γ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |y - x| ≤ B →
      materialH y ^ γ ≤ materialH x ^ γ * materialE0 x ^ K := by
  let A : ℝ := 8 * |γ| * B * (1 + B ^ 2)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A + 1, by linarith, fun x y hx hy hxy => ?_⟩
  have hshift := log_materialH_shift_bound hB hx hy hxy
  have hquad := one_add_sq_le_materialE0Exponent hx
  have hE : 0 ≤ materialE0Exponent x := by nlinarith [sq_nonneg x]
  have hmul : |γ| * |Real.log (materialH y) - (-2 * x ^ 3 / 3)| ≤
      |γ| * (4 * B * (1 + B ^ 2) * (1 + x ^ 2)) :=
    mul_le_mul_of_nonneg_left hshift (abs_nonneg γ)
  have hscale : |γ| * (4 * B * (1 + B ^ 2) * (1 + x ^ 2)) ≤
      A * materialE0Exponent x := by
    have hh := mul_le_mul_of_nonneg_left hquad
      (show 0 ≤ |γ| * (4 * B * (1 + B ^ 2)) by positivity)
    dsimp only [A]
    convert hh using 1 <;> ring
  have hlog : γ * (Real.log (materialH y) - (-2 * x ^ 3 / 3)) ≤
      (A + 1) * materialE0Exponent x := by
    calc
      _ ≤ |γ * (Real.log (materialH y) - (-2 * x ^ 3 / 3))| := le_abs_self _
      _ = |γ| * |Real.log (materialH y) - (-2 * x ^ 3 / 3)| := abs_mul _ _
      _ ≤ A * materialE0Exponent x := hmul.trans hscale
      _ ≤ (A + 1) * materialE0Exponent x :=
        mul_le_mul_of_nonneg_right (by linarith) hE
  simp only [materialH, Real.log_exp] at hlog
  simp only [materialH, materialE0, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [hlog]

/-- Fixed powers of the coefficient envelope also transfer across a
bounded endpoint-coordinate shift. -/
theorem materialE0_rpow_le_of_bounded_shift (α : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |y - x| ≤ B →
      materialE0 y ^ α ≤ materialE0 x ^ K := by
  obtain ⟨A, hA, hbound⟩ := exists_materialE0Exponent_bound_of_shift hB
  let K : ℝ := (A + 2) * |α| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun x y hx hy hxy => ?_⟩
  have hxE := one_add_sq_le_materialE0Exponent hx
  have hyE := one_add_sq_le_materialE0Exponent hy
  have hxE₀ : 0 ≤ materialE0Exponent x := by nlinarith [sq_nonneg x]
  have hyE₀ : 0 ≤ materialE0Exponent y := by nlinarith [sq_nonneg y]
  have ht := hbound y x hy hx (by simpa only [abs_sub_comm] using hxy)
  have hEy : materialE0Exponent y ≤ (A + 2) * materialE0Exponent x := by
    dsimp only [materialE0Exponent] at ht ⊢
    dsimp only [materialE0Exponent] at hxE
    nlinarith only [ht, hxE, sq_nonneg x]
  have hlog : materialE0Exponent y * α ≤ materialE0Exponent x * K := by
    calc
      _ ≤ materialE0Exponent y * |α| :=
        mul_le_mul_of_nonneg_left (le_abs_self α) hyE₀
      _ ≤ ((A + 2) * materialE0Exponent x) * |α| :=
        mul_le_mul_of_nonneg_right hEy (abs_nonneg α)
      _ ≤ materialE0Exponent x * K := by
        dsimp only [K]
        nlinarith only [hxE₀]
  simpa only [materialE0, ← Real.exp_mul, Real.exp_le_exp] using hlog

/-- The exact `H^γ` factor is retained when amplitude and coefficient loss
are evaluated at two separately shifted locations. -/
theorem material_weights_le_of_bounded_shift (γ α : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      |y - x| ≤ B → |z - x| ≤ B →
      materialH y ^ γ * materialE0 z ^ α ≤ materialH x ^ γ * materialE0 x ^ K := by
  obtain ⟨K₁, hK₁, hH⟩ := materialH_rpow_le_of_bounded_shift γ hB
  obtain ⟨K₂, hK₂, hE⟩ := materialE0_rpow_le_of_bounded_shift α hB
  refine ⟨K₁ + K₂, add_pos hK₁ hK₂, fun x y z hx hy hz hxy hxz => ?_⟩
  calc
    _ ≤ (materialH x ^ γ * materialE0 x ^ K₁) * materialE0 x ^ K₂ :=
      mul_le_mul (hH x y hx hy hxy) (hE x z hx hz hxz)
        (Real.rpow_pos_of_pos (materialE0_pos z) α).le
        (mul_pos (Real.rpow_pos_of_pos (materialH_pos x) γ)
          (Real.rpow_pos_of_pos (materialE0_pos x) K₁)).le
    _ = materialH x ^ γ * materialE0 x ^ (K₁ + K₂) := by
      rw [Real.rpow_add (materialE0_pos x), mul_assoc]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

/-- Near either endpoint, nearby cell samples retain the exact exponent
`γ` after transfer to the actual physical radius. -/
theorem materialSample_endpoint_weight_bound_sameExponent
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ α : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ (i j : ℕ) (r : ℝ),
      r ∈ Ioo D.a D.b → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B → endpointDistance D r < δ →
      T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ α ≤ T.H r ^ γ * T.E0 r ^ K := by
  obtain ⟨d0, δ, shift, _, hδ, hshift, hcoord⟩ :=
    materialSample_endpoint_coordinate_comparison hT hRef hB
  obtain ⟨K, hK, hbound⟩ := material_weights_le_of_bounded_shift γ α hshift
  refine ⟨δ, K, hδ, hK, fun i j r hr hrj hij hrnear => ?_⟩
  obtain ⟨_, hxy, hxz, hx, hy, hz, hHi, hEj, hHr, hEr⟩ :=
    hcoord i j r hr hrj hij hrnear
  rw [hHi, hEj, hHr, hEr]
  exact hbound _ _ _ hx hy hz hxy hxz

/-- Two-sided transfer between a radius and its cell sample, preserving
the height power in both directions. -/
theorem materialCell_endpoint_weight_comparison
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) (γ α : ℝ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ),
      r ∈ Ioo D.a D.b → r ∈ D.cells m → endpointDistance D r < δ →
      (T.H r ^ γ * T.E0 r ^ α ≤ T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ K) ∧
      (T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ α ≤ T.H r ^ γ * T.E0 r ^ K) := by
  obtain ⟨d0, δ, shift, _, hδ, hshift, hcoord⟩ :=
    materialSample_endpoint_coordinate_comparison hT hRef (B := 0) le_rfl
  obtain ⟨K, hK, hbound⟩ := material_weights_le_of_bounded_shift γ α hshift
  refine ⟨δ, K, hδ, hK, fun m r hr hrm hrnear => ?_⟩
  obtain ⟨_, hxy, _, hx, hy, _, hHm, hEm, hHr, hEr⟩ :=
    hcoord m m r hr hrm (by simp only [sub_self, abs_zero, le_refl]) hrnear
  rw [hHm, hEm, hHr, hEr]
  constructor
  · exact hbound _ _ _ hy hx hx
      (by simpa only [abs_sub_comm] using hxy)
      (by simpa only [abs_sub_comm] using hxy)
  · exact hbound _ _ _ hx hy hy hxy hxy

/-- Global two-sided comparison uses the endpoint calculation and only
finitely many cells meeting the compact middle of the annulus. The height
exponent is unchanged throughout. -/
theorem materialCell_weight_comparison
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) (γ α : ℝ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (m : ℕ) (r : ℝ), r ∈ D.cells m →
      (T.H r ^ γ * T.E0 r ^ α ≤ C * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ K) ∧
      (T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ α ≤ C * T.H r ^ γ * T.E0 r ^ K) := by
  classical
  obtain ⟨δ, K, hδ, hK, hnear⟩ := materialCell_endpoint_weight_comparison hT hRef γ α
  obtain ⟨_, hbounds⟩ := hRef
  have hpart : RadialPartition D := hbounds.2.1
  have hcore (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) : r ∈ Ioo D.a D.b :=
    hpart.2.2.2.1 m hr
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hpart m
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : IsCompact middle := isCompact_Icc
  have hmiddleCore : middle ⊆ Ioo D.a D.b :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfinite : {m : ℕ | (D.cells m ∩ middle).Nonempty}.Finite :=
    hbounds.2.2.2.2.2.1 middle hmiddle hmiddleCore
  let indices := hfinite.toFinset
  let U : ℝ → ℝ := fun r => T.H r ^ γ * T.E0 r ^ α
  let V : ℝ → ℝ := fun r => T.H r ^ γ * T.E0 r ^ K
  have hUpos (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < U r :=
    mul_pos (Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ)
      (Real.rpow_pos_of_pos (hT.2.1 r hr).2.2.1 α)
  have hVpos (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < V r :=
    mul_pos (Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ)
      (Real.rpow_pos_of_pos (hT.2.1 r hr).2.2.1 K)
  have hH := (hT.1 T.H (by simp)).rpow_const_of_ne
    (fun r hr => (hT.2.1 r hr).2.1.ne') (p := γ)
  have hE (t : ℝ) := (hT.1 T.E0 (by simp)).rpow_const_of_ne
    (fun r hr => (hT.2.1 r hr).2.2.1.ne') (p := t)
  have hUc : ContinuousOn U (Ioo D.a D.b) := (hH.mul (hE α)).continuousOn
  have hVc : ContinuousOn V (Ioo D.a D.b) := (hH.mul (hE K)).continuousOn
  have hVinv : ContinuousOn (fun r => (V r)⁻¹) (Ioo D.a D.b) :=
    hVc.inv₀ (fun r hr => (hVpos r hr).ne')
  obtain ⟨B₀, hB₀⟩ := hmiddle.bddAbove_image (hUc.mono hmiddleCore)
  obtain ⟨Q₀, hQ₀⟩ := hmiddle.bddAbove_image (hVinv.mono hmiddleCore)
  let B : ℝ := max 1 B₀
  let Q : ℝ := max 1 Q₀
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := zero_le_one.trans (le_max_left _ _)
  have hUb (r : ℝ) (hr : r ∈ middle) : U r ≤ B :=
    (hB₀ ⟨r, hr, rfl⟩).trans (le_max_right _ _)
  have hVb (r : ℝ) (hr : r ∈ middle) : (V r)⁻¹ ≤ Q :=
    (hQ₀ ⟨r, hr, rfl⟩).trans (le_max_right _ _)
  let S : ℝ := ∑ m ∈ indices, (V (T.sample m))⁻¹
  let R : ℝ := ∑ m ∈ indices, U (T.sample m)
  have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => (inv_pos.mpr (hVpos _ (hsample m))).le
  have hR : 0 ≤ R := Finset.sum_nonneg fun m _ => (hUpos _ (hsample m)).le
  let C : ℝ := 1 + B * S + Q * R
  have hC₁ : 1 ≤ C := by
    dsimp only [C]
    linarith [mul_nonneg hB hS, mul_nonneg hQ hR]
  have hC : 0 < C := zero_lt_one.trans_le hC₁
  refine ⟨C, K, hC, hK, fun m r hr => ?_⟩
  have hrCore := hcore m r hr
  have hmV := hVpos (T.sample m) (hsample m)
  have hrV := hVpos r hrCore
  suffices h : U r ≤ C * V (T.sample m) ∧ U (T.sample m) ≤ C * V r by
    simpa only [U, V, mul_assoc] using h
  by_cases hcollar : endpointDistance D r < δ
  · obtain ⟨hleft, hright⟩ := hnear m r hrCore hr hcollar
    exact ⟨hleft.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hC₁ hmV.le),
      hright.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hC₁ hrV.le)⟩
  · have hd : δ ≤ endpointDistance D r := le_of_not_gt hcollar
    have hrMiddle : r ∈ middle := by
      have hh := le_min_iff.mp hd
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have hm : m ∈ indices := hfinite.mem_toFinset.mpr ⟨r, hr, hrMiddle⟩
    have hmS : (V (T.sample m))⁻¹ ≤ S :=
      Finset.single_le_sum (fun j _ => (inv_pos.mpr (hVpos _ (hsample j))).le) hm
    have hmR : U (T.sample m) ≤ R :=
      Finset.single_le_sum (fun j _ => (hUpos _ (hsample j)).le) hm
    constructor
    · apply (div_le_iff₀ hmV).mp
      calc
        U r / V (T.sample m) = U r * (V (T.sample m))⁻¹ := div_eq_mul_inv _ _
        _ ≤ B * (V (T.sample m))⁻¹ :=
          mul_le_mul_of_nonneg_right (hUb r hrMiddle) (inv_pos.mpr hmV).le
        _ ≤ B * S := mul_le_mul_of_nonneg_left hmS hB
        _ ≤ C := by dsimp only [C]; linarith [mul_nonneg hQ hR]
    · apply (div_le_iff₀ hrV).mp
      calc
        U (T.sample m) / V r = U (T.sample m) * (V r)⁻¹ := div_eq_mul_inv _ _
        _ ≤ R * Q := mul_le_mul hmR (hVb r hrMiddle) (inv_pos.mpr hrV).le hR
        _ ≤ C := by dsimp only [C]; nlinarith only [mul_nonneg hB hS]

end ContinuousFlexibility.Statements
