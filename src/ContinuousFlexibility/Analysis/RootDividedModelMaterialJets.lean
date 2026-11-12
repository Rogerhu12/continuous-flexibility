import ContinuousFlexibility.Analysis.RootChartPointwiseMaterialJets
import ContinuousFlexibility.Analysis.RootDividedHeightMaterialJets

/-!
# One fixed-loss estimate for the actual divided root model

The existing chart and divided-height estimates are packaged with one
low order and loss. The three quantitative inputs are the genuine even
field, odd coefficient, and divided determinant. The actual chart,
Jacobian, height and inverse height are all conclusions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def RootDividedModelJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (δ : ℝ) (V : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ)
    (x : PolarPoint) : Prop :=
  RootChartPointwiseJetBound p loss B z G x ∧
    ContDiffAt ℝ ∞ (rootDividedHeight δ V G) x ∧
    0 < rootDividedHeight δ V G x ∧
    PointwiseMaterialJetBound p loss B z (rootDividedHeight δ V G) x ∧
    PointwiseMaterialJetBound p loss B z (fun y => (rootDividedHeight δ V G y)⁻¹) x

theorem rootDividedModel_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ δ lχ uχ lV uV : ℝ,
      0 < δ → 0 < lχ → lχ ≤ uχ → 0 < lV → lV ≤ uV →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ,
      ∀ V : PolarPoint → ℝ, ∀ x : PolarPoint,
      ContDiffAt ℝ ∞ (extendedRootEven G) x →
      ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) x → ContDiffAt ℝ ∞ V x →
      |x.1| ≤ 1 → extendedRootOddCoefficient G x ∈ Icc lχ uχ → V x ∈ Icc lV uV →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootEven G) x →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootOddCoefficient G) x →
      PointwiseMaterialJetBound p inputLoss A z V x →
      RootDividedModelJetBound p loss B z δ V G x := by
  obtain ⟨chartLow, chartLoss, hchart⟩ := rootChart_unitStrip_fixed_loss_material_bound hp hI inputLoss
  obtain ⟨heightLow, heightLoss, hheight⟩ :=
    rootDividedHeight_power_fixed_loss_material_bound hp hI inputLoss
  refine ⟨max chartLow heightLow, max chartLoss heightLoss, ?_⟩
  intro A hA δ lχ uχ lV uV hδ hlχ hluχ hlV hluV
  obtain ⟨C, hC, hCbound⟩ := hchart A hA lχ uχ hlχ hluχ
  obtain ⟨H, hH, hHbound⟩ := hheight A hA δ 1 lχ uχ lV uV hδ hlχ hluχ hlV hluV
  obtain ⟨I, hI', hIbound⟩ := hheight A hA δ (-1) lχ uχ lV uV hδ hlχ hluχ hlV hluV
  let B : ℕ → ℝ := fun n => C n + H n + I n
  have hB (n : ℕ) : 0 < B n := add_pos (add_pos (hC n) (hH n)) (hI' n)
  have hCB (n : ℕ) : C n ≤ B n := by dsimp only [B]; linarith [hH n, hI' n]
  have hHB (n : ℕ) : H n ≤ B n := by dsimp only [B]; linarith [hC n, hI' n]
  have hIB (n : ℕ) : I n ≤ B n := by dsimp only [B]; linarith [hC n, hH n]
  refine ⟨B, hB, ?_⟩
  intro z hz G V x hφ hχ hV hx hχvalue hVvalue hφjet hχjet hVjet
  have hzC : p chartLow z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzH : p heightLow z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hchart' := hCbound z hzC G x hφ hχ hx hχvalue hφjet hχjet
  have hheight' : PointwiseMaterialJetBound p heightLoss H z (rootDividedHeight δ V G) x := by
    simpa only [PointwiseMaterialJetBound, Real.rpow_one] using
      hHbound z hzH G V x hχ hV hχvalue hVvalue hχjet hVjet
  have hinverse' : PointwiseMaterialJetBound p heightLoss I z
      (fun y => (rootDividedHeight δ V G y)⁻¹) x := by
    simpa only [PointwiseMaterialJetBound, Real.rpow_neg_one] using
      hIbound z hzH G V x hχ hV hχvalue hVvalue hχjet hVjet
  have hsmooth := contDiffAt_rootDividedHeight hδ hV hχ
    (hlV.trans_le hVvalue.1) (hlχ.trans_le hχvalue.1)
  exact ⟨⟨hchart'.1,
      hchart'.2.1.mono hp (le_max_left _ _) (fun n => (hC n).le) hCB,
      hchart'.2.2.1.mono hp (le_max_left _ _) (fun n => (hC n).le) hCB,
      hchart'.2.2.2.mono hp (le_max_left _ _) (fun n => (hC n).le) hCB⟩,
    hsmooth.1, hsmooth.2,
    hheight'.mono hp (le_max_right _ _) (fun n => (hH n).le) hHB,
    hinverse'.mono hp (le_max_right _ _) (fun n => (hI' n).le) hIB⟩

end ContinuousFlexibility.Analysis
