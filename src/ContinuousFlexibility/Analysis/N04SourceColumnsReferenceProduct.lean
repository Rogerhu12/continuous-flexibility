import ContinuousFlexibility.Analysis.N04SourceColumnsData

/-! Products preserve scalar reference envelopes on the actual open strip. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

/-- A uniform finite spatial prefix bounds the local Leibniz product. -/
theorem n04SourceColumns_mixed_mul_bound
    {Ω : Set PolarPoint} (hΩ : IsOpen Ω) {f g : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (a b s : ℕ) (hab : a + b ≤ s) {q : PolarPoint} (hq : q ∈ Ω)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ u w : ℕ, u + w ≤ s → |mixedDerivative u w f q| ≤ A)
    (hgbound : ∀ u w : ℕ, u + w ≤ s → |mixedDerivative u w g q| ≤ B) :
    |mixedDerivative a b (fun p => f p * g p) q| ≤ (2 : ℝ) ^ s * A * B := by
  let RF : MixedJetRegularity (univ : Set ℝ) Ω (fun _ => g) :=
    n04Realization_mixedJetRegularity_fixedSpatial isOpen_univ hg
  let J : SmoothDirections (univ : Set ℝ)
      (fun _ : ℝ => mixedDerivative a b (fun p => f p * g p) q) :=
    smoothDirections_constant isOpen_univ _
  have hb := n04Realization_fixedSpatialProduct_parameterJet_bound hΩ hf RF a b s 0 hab
    hq J (x := (0 : ℝ)) (mem_univ _) Fin.elim0 hA hB (le_rfl : (1 : ℝ) ≤ 1)
    hfbound (fun u w huw => by
      simpa only [smoothDirections_D_zero_apply (RF.parameter u w q hq) (mem_univ _),
        Real.one_rpow, mul_one] using hgbound u w huw)
  have hp : (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ s := pow_le_pow_right₀ (by norm_num) hab
  have hb' : |mixedDerivative a b (fun p => f p * g p) q| ≤
      (2 : ℝ) ^ (a + b) * A * B := by
    simpa only [smoothDirections_D_zero_apply J (mem_univ _) Fin.elim0,
      Real.one_rpow, mul_one] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hA) hB)

theorem N04SourceReferenceData.sourceColumns_mul
    {T : MaterialData} {cell : ℕ → ℕ} {f₀ g₀ : ℕ → PolarPoint → ℝ}
    (hf : N04SourceReferenceData T cell f₀) (hg : N04SourceReferenceData T cell g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04SourceReferenceData T cell (fun m q => f₀ m q * g₀ m q) := by
  refine ⟨fun m => ⟨(hf.1 m).1.mul (hg.1 m).1,
    fun q hq => congrArg₂ (· * ·) ((hf.1 m).2 q hq) ((hg.1 m).2 q hq)⟩, fun s => ?_⟩
  have hsF := hf.2 s
  have hsG := hg.2 s
  have hc := coefficientEnvelope_pack ((2 : ℝ) ^ s * hsF.choose * hsG.choose)
    (hsF.choose + hsG.choose)
  refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
  intro m q hq i j hij
  have he : 0 < T.E0 (T.sample (cell m)) := zero_lt_one.trans_le (hE m)
  have hAf : 0 ≤ hsF.choose * T.E0 (T.sample (cell m)) ^ hsF.choose :=
    mul_nonneg hsF.choose_spec.1.le (Real.rpow_nonneg he.le _)
  have hAg : 0 ≤ hsG.choose * T.E0 (T.sample (cell m)) ^ hsG.choose :=
    mul_nonneg hsG.choose_spec.1.le (Real.rpow_nonneg he.le _)
  have hb := n04SourceColumns_mixed_mul_bound (isOpen_Ioo.prod isOpen_univ)
    (hf.1 m).1 (hg.1 m).1 i j s hij hq hAf hAg
    (fun u w huw => hsF.choose_spec.2 m q hq u w huw)
    (fun u w huw => hsG.choose_spec.2 m q hq u w huw)
  calc
    _ ≤ (2 : ℝ) ^ s * (hsF.choose * T.E0 (T.sample (cell m)) ^ hsF.choose) *
        (hsG.choose * T.E0 (T.sample (cell m)) ^ hsG.choose) := hb
    _ = ((2 : ℝ) ^ s * hsF.choose * hsG.choose) *
        T.E0 (T.sample (cell m)) ^ (hsF.choose + hsG.choose) := by
      rw [Real.rpow_add he]
      ring
    _ ≤ _ := hc.choose_spec.2 _ (hE m)

end ContinuousFlexibility.Analysis
