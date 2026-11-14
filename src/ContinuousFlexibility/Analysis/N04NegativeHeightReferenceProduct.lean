module

public import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData

/-! Products of selected reference fields retain the same sampled
coefficient envelope. The two spatial orders are counted only once. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

/-- Reference multiplication is uniform over the selected pieces. -/
theorem N04HeightReferenceDataOn.height_mul
    {T : MaterialData} {cell : ℕ → ℕ} {P : ℕ → Prop}
    {f g : ℕ → PolarPoint → ℝ}
    (hf : N04HeightReferenceDataOn T cell P f)
    (hg : N04HeightReferenceDataOn T cell P g)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04HeightReferenceDataOn T cell P (fun m q => f m q * g m q) := by
  classical
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  refine ⟨fun m hm => ⟨(hf.1 m hm).1.mul (hg.1 m hm).1,
    fun q hq => by
      change f m (q + (0, Real.pi)) * g m (q + (0, Real.pi)) = f m q * g m q
      rw [(hf.1 m hm).2 q hq, (hg.1 m hm).2 q hq]⟩, ?_⟩
  intro s
  obtain ⟨A, hA, hAf⟩ := hf.2 s
  obtain ⟨B, hB, hBg⟩ := hg.2 s
  obtain ⟨C, hC, hCb⟩ := coefficientEnvelope_pack ((2 : ℝ) ^ s * A * B) (A + B)
  refine ⟨C, hC, ?_⟩
  intro m hm q hq a b hab
  let E : ℝ := T.E0 (T.sample (cell m))
  have hEpos : 0 < E := zero_lt_one.trans_le (hE m)
  have hleft : ∀ u w : ℕ, u + w ≤ s →
      |mixedDerivative u w (f m) q| ≤ A * E ^ A :=
    fun u w huw => hAf m hm q hq u w huw
  have hright : ∀ u w : ℕ, u + w ≤ s →
      |mixedDerivative u w (g m) q| ≤ B * E ^ B :=
    fun u w huw => hBg m hm q hq u w huw
  let RF := n04Realization_mixedJetRegularity_fixedSpatial
    (X := ℝ) isOpen_univ (hg.1 m hm).1
  let J : SmoothDirections (univ : Set ℝ)
      (fun _ => mixedDerivative a b (fun y => f m y * g m y) q) :=
    smoothDirections_constant isOpen_univ _
  have hfixedD (u w : ℕ) :
      (RF.parameter u w q hq).D 0 (0 : ℝ) Fin.elim0 =
        mixedDerivative u w (g m) q :=
    smoothDirections_D_zero_apply (RF.parameter u w q hq) (mem_univ (0 : ℝ)) Fin.elim0
  have ht := n04Realization_fixedSpatialProduct_parameterJet_bound hΩ (hf.1 m hm).1
    RF a b s 0 hab hq J (mem_univ (0 : ℝ)) Fin.elim0
    (mul_nonneg hA.le (Real.rpow_nonneg hEpos.le _))
    (mul_nonneg hB.le (Real.rpow_nonneg hEpos.le _)) le_rfl hleft
    (fun u w huw => by
      rw [hfixedD u w]
      simpa only [Real.one_rpow, mul_one] using hright u w huw)
  have ht' : |mixedDerivative a b (fun y => f m y * g m y) q| ≤
      (2 : ℝ) ^ (a + b) * (A * E ^ A) * (B * E ^ B) := by
    simpa only [smoothDirections_D_zero_apply J (mem_univ (0 : ℝ)),
      Real.one_rpow, mul_one] using ht
  calc
    _ ≤ (2 : ℝ) ^ (a + b) * (A * E ^ A) * (B * E ^ B) := ht'
    _ ≤ (2 : ℝ) ^ s * (A * E ^ A) * (B * E ^ B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hab)
          (mul_nonneg hA.le (Real.rpow_nonneg hEpos.le _)))
        (mul_nonneg hB.le (Real.rpow_nonneg hEpos.le _))
    _ = ((2 : ℝ) ^ s * A * B) * E ^ (A + B) := by
      rw [Real.rpow_add hEpos]
      ring
    _ ≤ C * E ^ C := hCb E (hE m)

end ContinuousFlexibility.Analysis
