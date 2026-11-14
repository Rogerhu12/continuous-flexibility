module

public import ContinuousFlexibility.Analysis.CoordinateFieldJetBounds
public import ContinuousFlexibility.Analysis.CylinderMixedJetNorms
public import ContinuousFlexibility.Analysis.AbsoluteReciprocalJetBounds
public import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual chart derivative and reciprocal-Jacobian primitives

The four scalar derivative entries use only positive ordinary chart
jets. Their two determinant products and the genuine absolute reciprocal
are controlled by the existing fixed-loss estimates. A lower bound on
the actual Jacobian is sufficient; no inverse-Jacobian jet is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem chartDerivativeEntry_norm_le_at
    {F : PolarPoint → PolarPoint} {q : PolarPoint} (hF : ContDiffAt ℝ ∞ F q)
    (v : PolarPoint) (hv : ‖v‖ ≤ 1)
    (L : PolarPoint →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => L (fderiv ℝ F y v)) q‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) F q‖ := by
  have hD : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y v) q :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have he : (L : PolarPoint → ℝ) ∘ (fun y => fderiv ℝ F y v) =
      (fun y => L (fderiv ℝ F y v)) := by
    funext y
    exact Function.comp_apply
  have hc := L.norm_iteratedFDeriv_comp_left hD (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [he] at hc
  have hd := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ F) (c := v) (x := q) (n := n)
    (hF.fderiv_right (m := ∞) (by simp)) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hd
  exact hc.trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans
    (hd.trans (mul_le_of_le_one_left (norm_nonneg _) hv)))

theorem contDiff_coordinateChartDerivativeField
    {F : PolarPoint → PolarPoint} (hF : ContDiff ℝ ∞ F) (i : Fin 4) :
    ContDiff ℝ ∞ (coordinateChartDerivativeField F i) := by
  have hD (v : PolarPoint) : ContDiff ℝ ∞ (fun q => fderiv ℝ F q v) :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  fin_cases i
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_zero] using (hD (1, 0)).fst
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using (hD (0, 1)).fst
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using (hD (1, 0)).snd
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_succ,
      Matrix.cons_val_zero] using (hD (0, 1)).snd

theorem coordinateChartDerivativeField_norm_le_positiveJet_at
    {F : PolarPoint → PolarPoint} {q : PolarPoint} (hF : ContDiffAt ℝ ∞ F q)
    (i : Fin 4) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (coordinateChartDerivativeField F i) q‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) F q‖ := by
  have hr₁ := chartDerivativeEntry_norm_le_at hF (1, 0) (by simp)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) n
  have ht₁ := chartDerivativeEntry_norm_le_at hF (0, 1) (by simp)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) n
  have hr₂ := chartDerivativeEntry_norm_le_at hF (1, 0) (by simp)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) n
  have ht₂ := chartDerivativeEntry_norm_le_at hF (0, 1) (by simp)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) n
  fin_cases i
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_zero,
      ContinuousLinearMap.coe_fst'] using hr₁
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_succ, Matrix.cons_val_zero,
      ContinuousLinearMap.coe_fst'] using ht₁
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_succ, Matrix.cons_val_zero,
      ContinuousLinearMap.coe_snd'] using hr₂
  · simpa [coordinateChartDerivativeField, Matrix.cons_val_succ, Matrix.cons_val_zero,
      ContinuousLinearMap.coe_snd'] using ht₂

theorem coordinateChartDerivativeField_norm_le_positiveJet
    {F : PolarPoint → PolarPoint} (hF : ContDiff ℝ ∞ F)
    (i : Fin 4) (n : ℕ) (q : PolarPoint) :
    ‖iteratedFDeriv ℝ n (coordinateChartDerivativeField F i) q‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) F q‖ :=
  coordinateChartDerivativeField_norm_le_positiveJet_at hF.contDiffAt i n

theorem coordinateChartDerivativeField_mixed_le_positiveJet
    {F : PolarPoint → PolarPoint} (hF : ContDiff ℝ ∞ F)
    (i : Fin 4) (a b : ℕ) (q : PolarPoint) :
    |mixedDerivative a b (coordinateChartDerivativeField F i) q| ≤
      ‖iteratedFDeriv ℝ (a + b + 1) F q‖ :=
  (abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ
    (contDiff_coordinateChartDerivativeField hF i).contDiffOn a b (mem_univ q)).trans
      (coordinateChartDerivativeField_norm_le_positiveJet hF i (a + b) q)

/-- One common low order and loss precede the chart constants and its
Jacobian lower bound. Only positive actual chart jets are supplied. -/
theorem absolutePlaneJacobian_positiveJets_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ κ : ℝ, 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ F : PolarPoint → PolarPoint,
        ContDiff ℝ ∞ F → ∀ q : PolarPoint, κ ≤ |planeJacobian F q| →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F q‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p loss B z (fun y => |planeJacobian F y|⁻¹) q := by
  obtain ⟨baseJ, lossJ, hjacobian⟩ :=
    coordinateJacobianOn_fixed_loss_material_bound hp hI (inputLoss + 1)
  obtain ⟨baseR, lossR, hreciprocal⟩ :=
    absoluteReciprocal_fixed_loss_material_bound hp hI lossJ
  refine ⟨max baseJ baseR, lossR, ?_⟩
  intro A hA κ hκ
  obtain ⟨P, hP, hJbound⟩ := hjacobian (fun n => A (n + 1)) (fun n => hA (n + 1))
  let C (n : ℕ) : ℝ := 1 + P n
  have hC (n : ℕ) : 1 ≤ C n := by dsimp only [C]; linarith [hP n]
  have hPC (n : ℕ) : P n ≤ C n := by dsimp only [C]; linarith
  obtain ⟨B, hB, hRbound⟩ := hreciprocal C hC κ hκ
  refine ⟨B, hB, ?_⟩
  intro z hz F hF q hκq hraw
  have hzJ : p baseJ z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzR : p baseR z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hfields (i : Fin 4) :
      ContDiffOn ℝ ∞ (coordinateChartDerivativeField F i) univ :=
    (contDiff_coordinateChartDerivativeField hF i).contDiffOn
  have hentries (i : Fin 4) (a b : ℕ) :
      |mixedDerivative a b (coordinateChartDerivativeField F i) q| ≤
        A (a + b + 1) * (1 + p (a + b + (inputLoss + 1)) z) := by
    have he := (coordinateChartDerivativeField_mixed_le_positiveJet hF i a b q).trans
      (hraw (a + b + 1) (by omega))
    simpa only [show a + b + 1 + inputLoss = a + b + (inputLoss + 1) by omega] using he
  have hJ (n : ℕ) :
      ‖iteratedFDeriv ℝ n (planeJacobian F) q‖ ≤
        P n * (1 + p (n + lossJ) z) := by
    have hb := hJbound z hzJ 1 le_rfl F univ isOpen_univ hfields q (mem_univ q)
      (fun i a b => by simpa only [Real.one_rpow, mul_one] using hentries i a b) n
    simpa only [Real.one_rpow, mul_one] using hb
  have hJsmooth : ContDiffAt ℝ ∞ (planeJacobian F) q :=
    (contDiffOn_planeJacobian_of_chartDerivativeFields F hfields).contDiffAt
      (isOpen_univ.mem_nhds (mem_univ q))
  intro n
  have hb := hRbound z hzR 1 le_rfl (planeJacobian F) q hJsmooth hκq
    (fun k _hk => by
      have hh := (hJ k).trans (mul_le_mul_of_nonneg_right (hPC k)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
      simpa only [Real.one_rpow, mul_one] using hh) n
  simpa only [Real.one_rpow, mul_one] using hb

end ContinuousFlexibility.Analysis
