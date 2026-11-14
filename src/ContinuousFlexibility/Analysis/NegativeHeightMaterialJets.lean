import ContinuousFlexibility.Analysis.PositivePowerMaterialJets
import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations

/-!
# Actual negative height jets from the determinant ratio

The height is the positive fourth root of the actual radial coordinate
divided by the actual discriminant. Products and two scalar powers give
one common derivative loss. The discriminant upper bound is derived
from the original coefficient values on a fixed low seminorm ball;
neither height jets nor discriminant jets are quantitative inputs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem material_zero_value_le_twice
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    {f : PolarPoint → ℝ} {q : PolarPoint}
    (hA : 0 ≤ A 0) (hz : p loss z ≤ 1)
    (hj : PointwiseMaterialJetBound p loss A z f q) : |f q| ≤ 2 * A 0 := by
  have hh := hj 0
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, zero_add] at hh
  calc
    _ ≤ A 0 * (1 + p loss z) := hh
    _ ≤ A 0 * 2 := mul_le_mul_of_nonneg_left (by linarith only [hz]) hA
    _ = _ := by ring

private theorem discriminant_upper_of_values
    {a b c M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) :
    b ^ 2 - a * c ≤ 2 * M ^ 2 := by
  have hb₂ : b ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hac : |a * c| ≤ M ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul ha hc (abs_nonneg c) hM
  linarith only [hb₂, (abs_le.mp hac).1]

theorem negativeHeight_from_coefficients_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u κ : ℝ, 0 < l → l ≤ u → 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ C : SymmetricCoefficients, ∀ ξ : PolarPoint → ℝ,
      ∀ q : PolarPoint,
        ContDiffAt ℝ ∞ C.a q → ContDiffAt ℝ ∞ C.b q → ContDiffAt ℝ ∞ C.c q →
        ContDiffAt ℝ ∞ ξ q → ξ q ∈ Icc l u → κ ≤ C.b q ^ 2 - C.a q * C.c q →
        PointwiseMaterialJetBound p inputLoss A z C.a q →
        PointwiseMaterialJetBound p inputLoss A z C.b q →
        PointwiseMaterialJetBound p inputLoss A z C.c q →
        PointwiseMaterialJetBound p inputLoss A z ξ q →
        ContDiffAt ℝ ∞ (fun y => (ξ y / (C.b y ^ 2 - C.a y * C.c y)) ^ (1 / 4 : ℝ)) q ∧
        PointwiseMaterialJetBound p outLoss B z
          (fun y => (ξ y / (C.b y ^ 2 - C.a y * C.c y)) ^ (1 / 4 : ℝ)) q := by
  obtain ⟨baseP, lossP, hproduct⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI inputLoss
  let d := max inputLoss lossP
  obtain ⟨baseQ, lossQ, hpower⟩ :=
    positivePower_fixed_loss_material_bound (X := PolarPoint) hp hI d
  obtain ⟨baseR, outLoss, hlast⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI lossQ
  let low := max inputLoss (max baseP (max baseQ baseR))
  refine ⟨low, outLoss, ?_⟩
  intro A hA l u κ hl hlu hκ
  obtain ⟨P, hP, hprod⟩ := hproduct A hA
  let Q : ℕ → ℝ := fun n => A n + (P n + P n)
  have hQ (n : ℕ) : 0 < Q n := add_pos (hA n) (add_pos (hP n) (hP n))
  have hAQ (n : ℕ) : A n ≤ Q n := le_add_of_nonneg_right (add_nonneg (hP n).le (hP n).le)
  have hPQ (n : ℕ) : P n + P n ≤ Q n := le_add_of_nonneg_left (hA n).le
  let upper : ℝ := max κ (2 * (2 * A 0) ^ 2)
  obtain ⟨X, hX, hξpower⟩ := hpower Q hQ l u (1 / 4 : ℝ) hl hlu
  obtain ⟨Y, hY, hΔpower⟩ := hpower Q hQ κ upper (-(1 / 4 : ℝ)) hκ (le_max_left _ _)
  let R : ℕ → ℝ := fun n => X n + Y n
  have hR (n : ℕ) : 0 < R n := add_pos (hX n) (hY n)
  obtain ⟨B, hB, hfinal⟩ := hlast R hR
  refine ⟨B, hB, ?_⟩
  intro z hz C ξ q ha hb hc hξ hξvalue hgap haj hbj hcj hξj
  have hlowI : inputLoss ≤ low := le_max_left _ _
  have hlowP : baseP ≤ low := (le_max_left _ _).trans (le_max_right _ _)
  have hlowQ : baseQ ≤ low :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlowR : baseR ≤ low :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hzI : p inputLoss z ≤ 1 := (hp hlowI z).trans hz
  have hzP : p baseP z ≤ 1 := (hp hlowP z).trans hz
  have hzQ : p baseQ z ≤ 1 := (hp hlowQ z).trans hz
  have hzR : p baseR z ≤ 1 := (hp hlowR z).trans hz
  let Δ : PolarPoint → ℝ := fun y => C.b y ^ 2 - C.a y * C.c y
  have hΔ : ContDiffAt ℝ ∞ Δ q := (hb.pow 2).sub (ha.mul hc)
  have hbb : PointwiseMaterialJetBound p lossP P z (fun y => C.b y * C.b y) q :=
    hprod z hzP C.b C.b q hb hb hbj hbj
  have hac : PointwiseMaterialJetBound p lossP P z (fun y => C.a y * C.c y) q :=
    hprod z hzP C.a C.c q ha hc haj hcj
  have hΔj : PointwiseMaterialJetBound p lossP (fun n => P n + P n) z Δ q := by
    simpa only [PointwiseMaterialJetBound, Δ, pow_two] using
      hbb.sub (hb.mul hb) (ha.mul hc) hac
  have hΔQ : PointwiseMaterialJetBound p d Q z Δ q :=
    hΔj.mono hp (le_max_right _ _) (fun n => add_nonneg (hP n).le (hP n).le) hPQ
  have hξQ : PointwiseMaterialJetBound p d Q z ξ q :=
    hξj.mono hp (le_max_left _ _) (fun n => (hA n).le) hAQ
  have hM : 0 ≤ 2 * A 0 := mul_nonneg (by norm_num) (hA 0).le
  have hΔupper : Δ q ≤ upper :=
    (discriminant_upper_of_values hM
      (material_zero_value_le_twice (hA 0).le hzI haj)
      (material_zero_value_le_twice (hA 0).le hzI hbj)
      (material_zero_value_le_twice (hA 0).le hzI hcj)).trans (le_max_right _ _)
  have hξpos : 0 < ξ q := hl.trans_le hξvalue.1
  have hΔpos : 0 < Δ q := hκ.trans_le hgap
  have hξsmooth : ContDiffAt ℝ ∞ (fun y => ξ y ^ (1 / 4 : ℝ)) q :=
    hξ.rpow_const_of_ne hξpos.ne'
  have hΔsmooth : ContDiffAt ℝ ∞ (fun y => Δ y ^ (-(1 / 4 : ℝ))) q :=
    hΔ.rpow_const_of_ne hΔpos.ne'
  have hξpow : PointwiseMaterialJetBound p lossQ X z (fun y => ξ y ^ (1 / 4 : ℝ)) q :=
    hξpower z hzQ ξ q hξ hξvalue (fun n _ => hξQ n)
  have hΔpow : PointwiseMaterialJetBound p lossQ Y z (fun y => Δ y ^ (-(1 / 4 : ℝ))) q :=
    hΔpower z hzQ Δ q hΔ ⟨hgap, hΔupper⟩ (fun n _ => hΔQ n)
  have hξR : PointwiseMaterialJetBound p lossQ R z (fun y => ξ y ^ (1 / 4 : ℝ)) q :=
    hξpow.mono hp le_rfl (fun n => (hX n).le) (fun n => le_add_of_nonneg_right (hY n).le)
  have hΔR : PointwiseMaterialJetBound p lossQ R z (fun y => Δ y ^ (-(1 / 4 : ℝ))) q :=
    hΔpow.mono hp le_rfl (fun n => (hY n).le) (fun n => le_add_of_nonneg_left (hX n).le)
  have hproductBound := hfinal z hzR _ _ q hξsmooth hΔsmooth hξR hΔR
  have he : (fun y => (ξ y / Δ y) ^ (1 / 4 : ℝ)) =ᶠ[𝓝 q]
      (fun y => ξ y ^ (1 / 4 : ℝ) * Δ y ^ (-(1 / 4 : ℝ))) := by
    filter_upwards [hξ.continuousAt.eventually (Ioi_mem_nhds hξpos),
      hΔ.continuousAt.eventually (Ioi_mem_nhds hΔpos)] with y hyξ hyΔ
    rw [Real.div_rpow hyξ.le hyΔ.le, Real.rpow_neg hyΔ.le, div_eq_mul_inv]
  refine ⟨(hξsmooth.mul hΔsmooth).congr_of_eventuallyEq he, ?_⟩
  intro n
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
  exact hproductBound n

end ContinuousFlexibility.Analysis
