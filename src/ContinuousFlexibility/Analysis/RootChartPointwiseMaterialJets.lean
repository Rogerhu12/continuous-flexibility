import ContinuousFlexibility.Analysis.RootRadialPowerMaterialJets
import ContinuousFlexibility.Analysis.PointwiseJacobianMaterialJets
import ContinuousFlexibility.Analysis.RootChartExtension

/-!
# Actual extended root chart jets

The two genuine smooth fields φ and χ determine the radial power and
the root chart. Their actual ordinary jets and a positive value range
for χ imply fixed-loss jets for the chart and its actual Jacobian.
The statement is pointwise at the root; it does not assert a uniform
negative-side collar from a pointwise smoothness hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def RootChartPointwiseJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (G : ℝ × ℝ × ℝ → ℝ) (x : PolarPoint) : Prop :=
  ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) x ∧
    PointwiseMaterialJetBound p loss B z (extendedRootRadialFactor G) x ∧
    PointwiseMaterialJetBound p loss B z (extendedRootEvenOddChart G) x ∧
    PointwiseMaterialJetBound p loss B z (planeJacobian (extendedRootEvenOddChart G)) x

theorem rootChart_pointwise_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u : ℝ, 0 < l → l ≤ u →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ, ∀ x : PolarPoint,
      ContDiffAt ℝ ∞ (extendedRootEven G) x →
      ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) x → x.1 = 0 →
      extendedRootOddCoefficient G x ∈ Icc l u →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootEven G) x →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootOddCoefficient G) x →
      RootChartPointwiseJetBound p loss B z G x := by
  obtain ⟨radialBase, radialLoss, hradial⟩ :=
    rootRadialPower_fixed_loss_material_bound hp hI inputLoss
  let pairLoss := max inputLoss radialLoss
  obtain ⟨jacobianBase, jacobianLoss, hJacobian⟩ :=
    planeJacobian_fixed_loss_material_bound hp hI pairLoss
  refine ⟨max radialBase jacobianBase, max pairLoss jacobianLoss, ?_⟩
  intro A hA l u hl hlu
  obtain ⟨P, hP, hpower⟩ := hradial A hA l u hl hlu
  let D : ℕ → ℝ := fun n => A n + P n
  have hD (n : ℕ) : 0 < D n := add_pos (hA n) (hP n)
  obtain ⟨Q, hQ, hjets⟩ := hJacobian D hD
  let B : ℕ → ℝ := fun n => D n + Q n
  have hB (n : ℕ) : 0 < B n := add_pos (hD n) (hQ n)
  refine ⟨B, hB, ?_⟩
  intro z hz G x hφ hχ hx hvalue hφjet hχjet
  have hzRadial : p radialBase z ≤ 1 := ((hp (le_max_left _ _)) z).trans hz
  have hzJacobian : p jacobianBase z ≤ 1 := ((hp (le_max_right _ _)) z).trans hz
  obtain ⟨hfactor, hξ⟩ := hpower z hzRadial (extendedRootOddCoefficient G) x
    hχ hx hvalue hχjet
  change PointwiseMaterialJetBound p radialLoss P z (extendedRootRadialFactor G) x at hfactor
  change PointwiseMaterialJetBound p radialLoss P z (extendedRootRadialCoordinate G) x at hξ
  have hfactorSmooth : ContDiffAt ℝ ∞ (extendedRootRadialFactor G) x :=
    (contDiffAt_const.mul hχ).rpow_const_of_ne
      (mul_ne_zero (by norm_num) (ne_of_gt (hl.trans_le hvalue.1)))
  have hξSmooth : ContDiffAt ℝ ∞ (extendedRootRadialCoordinate G) x :=
    contDiffAt_fst.mul hfactorSmooth
  have hchartSmooth : ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) x :=
    hξSmooth.prodMk hφ
  have hξD : PointwiseMaterialJetBound p pairLoss D z (extendedRootRadialCoordinate G) x :=
    hξ.mono hp (le_max_right _ _) (fun n => (hP n).le)
      (fun n => le_add_of_nonneg_left (hA n).le)
  have hφD : PointwiseMaterialJetBound p pairLoss D z (extendedRootEven G) x :=
    hφjet.mono hp (le_max_left _ _) (fun n => (hA n).le)
      (fun n => le_add_of_nonneg_right (hP n).le)
  have hchart : PointwiseMaterialJetBound p pairLoss D z (extendedRootEvenOddChart G) x := by
    simpa only [max_self] using hξD.prodMk hξSmooth hφ hφD
  have hJ := hjets z hzJacobian (extendedRootEvenOddChart G) x hchartSmooth hchart
  have hfactorD : PointwiseMaterialJetBound p pairLoss D z (extendedRootRadialFactor G) x :=
    hfactor.mono hp (le_max_right _ _) (fun n => (hP n).le)
      (fun n => le_add_of_nonneg_left (hA n).le)
  exact ⟨hchartSmooth,
    hfactorD.mono hp (le_max_left _ _) (fun n => (hD n).le)
      (fun n => le_add_of_nonneg_right (hQ n).le),
    hchart.mono hp (le_max_left _ _) (fun n => (hD n).le)
      (fun n => le_add_of_nonneg_right (hQ n).le),
    hJ.mono hp (le_max_right _ _) (fun n => (hQ n).le)
      (fun n => le_add_of_nonneg_left (hD n).le)⟩

end ContinuousFlexibility.Analysis
