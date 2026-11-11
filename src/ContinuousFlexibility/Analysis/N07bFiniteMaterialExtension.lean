import ContinuousFlexibility.Analysis.N07bFiniteFlatExtension
import ContinuousFlexibility.Analysis.MaterialEndpointDecay

/-!
# Finite-order flat extension from actual material decay

The transport's finite Fréchet jets may grow by arbitrary fixed powers of
the material envelope. Any positive height exponent absorbs that growth
and gives quadratic endpoint decay. Only the finitely many jets needed
for the chosen extension order are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- A pointwise bound by a positive height weight supplies quadratic
decay at both actual physical endpoints. -/
theorem n07b_frechetJet_quadratic_decay
    {D : ReferenceData} {T : MaterialData} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) (n : ℕ)
    (hbound : ∃ K A : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n f p‖ ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : PolarPoint, p.1 ∈ Ioo D.a D.b →
      Statements.endpointDistance D p.1 < δ →
        ‖iteratedFDeriv ℝ n f p‖ ≤ Statements.endpointDistance D p.1 ^ 2 := by
  obtain ⟨K, A, hK, hbound⟩ := hbound
  have hK1 : 0 < K + 1 := by linarith
  obtain ⟨δ, hδ, hdecay⟩ :=
    exists_material_endpoint_decay hT hγ (inv_pos.mpr hK1) A 2
  refine ⟨δ, hδ, fun p hp hnear => ?_⟩
  have hd : 0 < Statements.endpointDistance D p.1 :=
    lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2)
  have hd2 : 0 < Statements.endpointDistance D p.1 ^ 2 := pow_pos hd 2
  have hpos := hT.2.1 p.1 hp
  have hw : 0 ≤ T.H p.1 ^ γ * T.M p.1 ^ A :=
    mul_nonneg (Real.rpow_pos_of_pos hpos.2.1 _).le
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hpos.2.2.2) _).le
  have hsmall : T.H p.1 ^ γ * T.M p.1 ^ A <
      (K + 1)⁻¹ * Statements.endpointDistance D p.1 ^ 2 :=
    (div_lt_iff₀ hd2).mp (hdecay p.1 hp hnear)
  calc
    _ ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A := hbound p ⟨hp, mem_univ _⟩
    _ = K * (T.H p.1 ^ γ * T.M p.1 ^ A) := mul_assoc _ _ _
    _ ≤ (K + 1) * (T.H p.1 ^ γ * T.M p.1 ^ A) :=
      mul_le_mul_of_nonneg_right (by linarith) hw
    _ ≤ (K + 1) * ((K + 1)⁻¹ * Statements.endpointDistance D p.1 ^ 2) :=
      mul_le_mul_of_nonneg_left hsmall.le hK1.le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hK1.ne', one_mul]

/-- Actual finite material-jet bounds give a genuine finite-order
extension, with the same low-order jets zero off the open annulus. -/
theorem n07b_finite_flat_extension_of_material_decay
    {D : ReferenceData} {T : MaterialData} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) (N : ℕ)
    (hf : ContDiffOn ℝ ((N + 1 : ℕ) : ℕ∞ω) f (annularOpen D))
    (hbound : ∀ n : ℕ, n ≤ N → ∃ K A : ℝ, 0 ≤ K ∧
      ∀ p ∈ annularOpen D,
        ‖iteratedFDeriv ℝ n f p‖ ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A) :
    ContDiff ℝ N ((annularOpen D).indicator f) ∧
      ∀ n : ℕ, n ≤ N → ∀ p : PolarPoint, p.1 ∉ Ioo D.a D.b →
        iteratedFDeriv ℝ n ((annularOpen D).indicator f) p = 0 :=
  n07b_finite_cylinder_zero_extension N hf
    (fun n hn => n07b_frechetJet_quadratic_decay hT hγ n (hbound n hn))

/-- In particular, the C³ transport representative has an actual C²
endpoint extension when its first three jets have the prescribed decay. -/
theorem n07b_c2_flat_extension_of_material_decay
    {D : ReferenceData} {T : MaterialData} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ)
    (hf : ContDiffOn ℝ 3 f (annularOpen D))
    (hbound : ∀ n : ℕ, n ≤ 2 → ∃ K A : ℝ, 0 ≤ K ∧
      ∀ p ∈ annularOpen D,
        ‖iteratedFDeriv ℝ n f p‖ ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A) :
    ContDiff ℝ 2 ((annularOpen D).indicator f) ∧
      ∀ n : ℕ, n ≤ 2 → ∀ p : PolarPoint, p.1 ∉ Ioo D.a D.b →
        iteratedFDeriv ℝ n ((annularOpen D).indicator f) p = 0 :=
  n07b_finite_flat_extension_of_material_decay hT hγ 2 hf hbound

end ContinuousFlexibility.Analysis

