module

public import ContinuousFlexibility.Analysis.RootChartPointwiseMaterialJets
public import ContinuousFlexibility.Analysis.RootAngularProductMaterialJets
public import ContinuousFlexibility.Analysis.RootSmoothHeight

/-!
# Actual root-height jets from the original smooth fields

The coefficient, chart Jacobian, and angular denominator are combined
by actual products and a reciprocal. A positive value interval for the
resulting factor then controls the actual height and its inverse. All
low orders and losses precede the value intervals and numerical jet
majorants. No derivative bound for the height, factor, or Jacobian is
assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def RootHeightPointwiseJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (a : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) : Prop :=
  ContDiffAt ℝ ∞ (rootSmoothHeight a G) (0, θ) ∧
    PointwiseMaterialJetBound p loss B z (rootHeightFactor a G) (0, θ) ∧
    PointwiseMaterialJetBound p loss B z (rootSmoothHeight a G) (0, θ) ∧
    PointwiseMaterialJetBound p loss B z (fun y => (rootSmoothHeight a G y)⁻¹) (0, θ)

theorem rootHeight_pointwise_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ lχ uχ lB uB lα uα : ℝ,
      0 < lχ → lχ ≤ uχ → 0 < lB → lB ≤ uB → 0 < lα → lα ≤ uα →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ, ∀ a : PolarPoint → ℝ, ∀ θ : ℝ,
      ContDiffAt ℝ ∞ (extendedRootEven G) (0, θ) →
      ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) (0, θ) → ContDiffAt ℝ ∞ a (0, θ) →
      extendedRootOddCoefficient G (0, θ) ∈ Icc lχ uχ →
      rootAngularProduct G (0, θ) ∈ Icc lB uB →
      rootHeightFactor a G (0, θ) ∈ Icc lα uα →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootEven G) (0, θ) →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootOddCoefficient G) (0, θ) →
      PointwiseMaterialJetBound p inputLoss A z a (0, θ) →
      RootHeightPointwiseJetBound p loss B z a G θ := by
  obtain ⟨chartBase, chartLoss, hchart⟩ :=
    rootChart_pointwise_fixed_loss_material_bound hp hI inputLoss
  obtain ⟨angularBase, angularLoss, hangular⟩ :=
    rootAngularProduct_fixed_loss_material_bound hp hI inputLoss
  obtain ⟨reciprocalBase, reciprocalLoss, hreciprocal⟩ :=
    positivePower_fixed_loss_material_bound (X := PolarPoint) hp hI angularLoss
  let numeratorInput := max inputLoss chartLoss
  obtain ⟨numeratorBase, numeratorLoss, hnumerator⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI numeratorInput
  let quotientInput := max numeratorLoss reciprocalLoss
  obtain ⟨quotientBase, quotientLoss, hquotient⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI quotientInput
  obtain ⟨heightBase, heightLoss, hheight⟩ :=
    positivePower_fixed_loss_material_bound (X := PolarPoint) hp hI quotientLoss
  let base := max chartBase (max angularBase (max reciprocalBase
    (max numeratorBase (max quotientBase heightBase))))
  refine ⟨base, max quotientLoss heightLoss, ?_⟩
  intro A hA lχ uχ lB uB lα uα hlχ hluχ hlB hluB hlα hluα
  obtain ⟨C, hC, hchartBound⟩ := hchart A hA lχ uχ hlχ hluχ
  obtain ⟨D, hD, hangularBound⟩ := hangular A hA
  obtain ⟨R, hR, hreciprocalBound⟩ := hreciprocal D hD lB uB (-1) hlB hluB
  let N : ℕ → ℝ := fun n => A n + C n
  have hN (n : ℕ) : 0 < N n := add_pos (hA n) (hC n)
  obtain ⟨P, hP, hnumeratorBound⟩ := hnumerator N hN
  let Q : ℕ → ℝ := fun n => P n + R n
  have hQ (n : ℕ) : 0 < Q n := add_pos (hP n) (hR n)
  obtain ⟨V, hV, hquotientBound⟩ := hquotient Q hQ
  obtain ⟨H, hH, hheightBound⟩ := hheight V hV lα uα (-(1 / 2 : ℝ)) hlα hluα
  obtain ⟨I, hI', hinverseHeightBound⟩ := hheight V hV lα uα (1 / 2 : ℝ) hlα hluα
  let B : ℕ → ℝ := fun n => V n + H n + I n
  have hB (n : ℕ) : 0 < B n := add_pos (add_pos (hV n) (hH n)) (hI' n)
  refine ⟨B, hB, ?_⟩
  intro z hz G a θ hφ hχ ha hχvalue hBvalue hαvalue hφjet hχjet hajet
  have hlow (j : ℕ) (hj : j ≤ base) : p j z ≤ 1 := ((hp hj) z).trans hz
  have hchartAt := hchartBound z (hlow chartBase (by dsimp only [base]; omega)) G (0, θ)
    hφ hχ rfl hχvalue hφjet hχjet
  have hJac : ContDiffAt ℝ ∞ (planeJacobian (extendedRootEvenOddChart G)) (0, θ) :=
    contDiffAt_planeJacobian hchartAt.1
  have hDenom : ContDiffAt ℝ ∞ (rootAngularProduct G) (0, θ) := by
    have hdφ : ContDiffAt ℝ ∞ (angularPartial (extendedRootEven G)) (0, θ) :=
      (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    have hdχ : ContDiffAt ℝ ∞ (angularPartial (extendedRootOddCoefficient G)) (0, θ) :=
      (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    exact (hdφ.pow 2).sub ((contDiffAt_fst.pow 3).mul (hdχ.pow 2))
  have hDenom0 : rootAngularProduct G (0, θ) ≠ 0 := (hlB.trans_le hBvalue.1).ne'
  have hDenomJet := hangularBound z
    (hlow angularBase (by dsimp only [base]; omega)) G θ hφ hχ hφjet hχjet
  have hReciprocal : PointwiseMaterialJetBound p reciprocalLoss R z
      (fun y => (rootAngularProduct G y)⁻¹) (0, θ) := by
    simpa only [PointwiseMaterialJetBound, Real.rpow_neg_one] using hreciprocalBound z
      (hlow reciprocalBase (by dsimp only [base]; omega)) _ (0, θ)
      hDenom hBvalue (fun n _ => hDenomJet n)
  have hReciprocalSmooth : ContDiffAt ℝ ∞ (fun y => (rootAngularProduct G y)⁻¹) (0, θ) :=
    hDenom.fun_inv hDenom0
  have haN : PointwiseMaterialJetBound p numeratorInput N z a (0, θ) :=
    hajet.mono hp (le_max_left _ _) (fun n => (hA n).le)
      (fun n => le_add_of_nonneg_right (hC n).le)
  have hJN : PointwiseMaterialJetBound p numeratorInput N z
      (planeJacobian (extendedRootEvenOddChart G)) (0, θ) :=
    hchartAt.2.2.2.mono hp (le_max_right _ _) (fun n => (hC n).le)
      (fun n => le_add_of_nonneg_left (hA n).le)
  have hNumerator : PointwiseMaterialJetBound p numeratorLoss P z
      (fun y => a y * planeJacobian (extendedRootEvenOddChart G) y) (0, θ) :=
    hnumeratorBound z (hlow numeratorBase (by dsimp only [base]; omega)) _ _ (0, θ)
      ha hJac haN hJN
  have hNumeratorQ := hNumerator.mono hp (le_max_left numeratorLoss reciprocalLoss)
    (fun n => (hP n).le) (fun n => le_add_of_nonneg_right (hR n).le)
  have hReciprocalQ := hReciprocal.mono hp (le_max_right numeratorLoss reciprocalLoss)
    (fun n => (hR n).le) (fun n => le_add_of_nonneg_left (hP n).le)
  have hFactor : PointwiseMaterialJetBound p quotientLoss V z (rootHeightFactor a G) (0, θ) := by
    have hq := hquotientBound z
      (hlow quotientBase (by dsimp only [base]; omega)) _ _ (0, θ)
      (ha.mul hJac) hReciprocalSmooth hNumeratorQ hReciprocalQ
    have he : (fun y : PolarPoint => a y * planeJacobian (extendedRootEvenOddChart G) y *
        (rootAngularProduct G y)⁻¹) = rootHeightFactor a G := by
      funext y
      simp only [rootHeightFactor, div_eq_mul_inv]
    rw [he] at hq
    simpa only [PointwiseMaterialJetBound] using hq
  have hFactorSmooth : ContDiffAt ℝ ∞ (rootHeightFactor a G) (0, θ) :=
    (ha.mul hJac).fun_div hDenom hDenom0
  have hFactorPos : 0 < rootHeightFactor a G (0, θ) := hlα.trans_le hαvalue.1
  have hHeightSmooth : ContDiffAt ℝ ∞ (rootSmoothHeight a G) (0, θ) := by
    have hs : ContDiffAt ℝ ∞ (fun y => Real.sqrt (rootHeightFactor a G y)) (0, θ) := by
      simpa only [Real.sqrt_eq_rpow] using
        hFactorSmooth.rpow_const_of_ne (p := (1 / 2 : ℝ)) hFactorPos.ne'
    exact hs.fun_inv (Real.sqrt_pos.mpr hFactorPos).ne'
  have hHeightPower := hheightBound z
    (hlow heightBase (by dsimp only [base]; omega)) _ (0, θ)
      hFactorSmooth hαvalue (fun n _ => hFactor n)
  have hHeight : PointwiseMaterialJetBound p heightLoss H z (rootSmoothHeight a G) (0, θ) := by
    have hnear : ∀ᶠ y in 𝓝 (0, θ), 0 < rootHeightFactor a G y :=
      hFactorSmooth.continuousAt.eventually (Ioi_mem_nhds hFactorPos)
    have he : (fun y => rootHeightFactor a G y ^ (-(1 / 2 : ℝ))) =ᶠ[𝓝 (0, θ)]
        rootSmoothHeight a G := by
      filter_upwards [hnear] with y hy
      rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
      rfl
    intro n
    rw [← (he.iteratedFDeriv ℝ n).self_of_nhds]
    exact hHeightPower n
  have hInverseHeight : PointwiseMaterialJetBound p heightLoss I z
      (fun y => (rootSmoothHeight a G y)⁻¹) (0, θ) := by
    simpa only [PointwiseMaterialJetBound, rootSmoothHeight, inv_inv, Real.sqrt_eq_rpow] using
      hinverseHeightBound z (hlow heightBase (by dsimp only [base]; omega)) _ (0, θ)
        hFactorSmooth hαvalue (fun n _ => hFactor n)
  have hVB (n : ℕ) : V n ≤ B n := by dsimp only [B]; linarith [hH n, hI' n]
  have hHB (n : ℕ) : H n ≤ B n := by dsimp only [B]; linarith [hV n, hI' n]
  have hIB (n : ℕ) : I n ≤ B n := by dsimp only [B]; linarith [hV n, hH n]
  exact ⟨hHeightSmooth,
    hFactor.mono hp (le_max_left _ _) (fun n => (hV n).le) hVB,
    hHeight.mono hp (le_max_right _ _) (fun n => (hH n).le) hHB,
    hInverseHeight.mono hp (le_max_right _ _) (fun n => (hI' n).le) hIB⟩

end ContinuousFlexibility.Analysis
