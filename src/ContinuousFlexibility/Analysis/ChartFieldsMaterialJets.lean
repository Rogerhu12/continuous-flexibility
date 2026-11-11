import ContinuousFlexibility.Analysis.PositiveChartJacobianJets
import ContinuousFlexibility.Analysis.InverseChartFieldJetBounds

/-!
# Actual canonical fields from chart, inverse, height, and raw coefficients

The reciprocal Jacobian is derived from the actual chart jets and a
numerical determinant lower bound. The nine physical primitives then
feed the established potential/density closure. All losses and low
orders precede the component constants. No zeroth-order angular lift,
reciprocal-derivative, or canonical-field bound is supplied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem chartFields_bound_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {z : E}
    {n l L : ℕ} (hl : l ≤ L) {v A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hv : v ≤ A * (1 + p (n + l) z)) :
    v ≤ B * (1 + p (n + L) z) :=
  hv.trans (mul_le_mul hAB
    (add_le_add le_rfl (hp (Nat.add_le_add_left hl n) z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) (hA.trans hAB))

theorem chartFields_from_positiveJets_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ κ : ℝ, 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 →
      ∀ C₀ : SymmetricCoefficients, ∀ F G : PolarPoint → PolarPoint,
      ∀ h : PolarPoint → ℝ, ∀ U : Set PolarPoint, IsOpen U →
        (∀ i, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i C₀) U) →
        ContDiff ℝ ∞ F → ContDiff ℝ ∞ h →
      ∀ x : PolarPoint, G x ∈ U → ContDiffAt ℝ ∞ G x →
        κ ≤ |planeJacobian F (G x)| →
        (∀ i a b, |mixedDerivative a b (canonicalCoefficientComponent i C₀) (G x)| ≤
          A (a + b) * (1 + p (a + b + inputLoss) z)) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F (G x)‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p inputLoss A z h (G x) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n G x‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
      ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (inverseChartPotential C₀ F G h) x‖ ≤
          B n * (1 + p (n + loss) z) ∧
        ∀ i : Fin 3, ‖iteratedFDeriv ℝ n
          (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients C₀ F G h)) x‖ ≤
            B n * (1 + p (n + loss) z) := by
  obtain ⟨baseR, lossR, hreciprocal⟩ :=
    absolutePlaneJacobian_positiveJets_fixed_loss_bound hp hI inputLoss
  let midLoss := max (inputLoss + 1) lossR
  obtain ⟨baseF, lossF, hfields⟩ :=
    inverseChartFieldsOn_fixed_loss_material_bound hp hI midLoss
  refine ⟨max baseR baseF, lossF, ?_⟩
  intro A hA κ hκ
  obtain ⟨R, hR, hRbound⟩ := hreciprocal A hA κ hκ
  let C (n : ℕ) : ℝ := 1 + A n + A (n + 1) + R n
  have hC (n : ℕ) : 1 ≤ C n := by
    dsimp only [C]
    linarith [hA n, hA (n + 1), hR n]
  have hAC (n : ℕ) : A n ≤ C n := by
    dsimp only [C]
    linarith [hA (n + 1), hR n]
  have hA₁C (n : ℕ) : A (n + 1) ≤ C n := by
    dsimp only [C]
    linarith [hA n, hR n]
  have hRC (n : ℕ) : R n ≤ C n := by
    dsimp only [C]
    linarith [hA n, hA (n + 1)]
  have hinput : inputLoss ≤ midLoss :=
    (Nat.le_succ inputLoss).trans (le_max_left _ _)
  obtain ⟨B, hB, hbound⟩ := hfields C hC
  refine ⟨B, hB, ?_⟩
  intro z hz C₀ F G h U hU hcoeff hF hh x hx hG hκx hraw hFraw hhraw hGraw
  have hzR : p baseR z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzF : p baseF z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hJ : ContDiff ℝ ∞ (planeJacobian F) :=
    contDiffOn_univ.mp (contDiffOn_planeJacobian_of_chartDerivativeFields F
      (fun i => (contDiff_coordinateChartDerivativeField hF i).contDiffOn))
  let V := U ∩ {q : PolarPoint | planeJacobian F q ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne_fun hJ.continuous continuous_const)
  have hxV : G x ∈ V := ⟨hx, abs_pos.mp (hκ.trans_le hκx)⟩
  have hrecip : ContDiffOn ℝ ∞ (fun q => |planeJacobian F q|⁻¹) V := by
    intro q hq
    exact ((contDiffAt_absoluteReciprocal hq.2).comp q hJ.contDiffAt).contDiffWithinAt
  have hprimitive (i : Fin 9) :
      ContDiffOn ℝ ∞ (coordinatePrimitiveJetField C₀ F h i) V := by
    fin_cases i
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using
        (hcoeff 0).mono (inter_subset_left (s := U))
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using
        (hcoeff 1).mono (inter_subset_left (s := U))
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using
        (hcoeff 2).mono (inter_subset_left (s := U))
    · simpa [coordinatePrimitiveJetField] using
        (contDiff_coordinateChartDerivativeField hF 0).contDiffOn (s := V)
    · simpa [coordinatePrimitiveJetField] using
        (contDiff_coordinateChartDerivativeField hF 1).contDiffOn (s := V)
    · simpa [coordinatePrimitiveJetField] using
        (contDiff_coordinateChartDerivativeField hF 2).contDiffOn (s := V)
    · simpa [coordinatePrimitiveJetField] using
        (contDiff_coordinateChartDerivativeField hF 3).contDiffOn (s := V)
    · simpa [coordinatePrimitiveJetField] using hh.contDiffOn (s := V)
    · simpa [coordinatePrimitiveJetField] using hrecip
  have hcoeff' (i : Fin 3) (a b : ℕ) :
      |mixedDerivative a b (canonicalCoefficientComponent i C₀) (G x)| ≤
        C (a + b) * (1 + p (a + b + midLoss) z) :=
    chartFields_bound_mono hp hinput (zero_le_one.trans (hA (a + b)))
      (hAC (a + b)) (hraw i a b)
  have hentry (i : Fin 4) (a b : ℕ) :
      |mixedDerivative a b (coordinateChartDerivativeField F i) (G x)| ≤
        C (a + b) * (1 + p (a + b + midLoss) z) := by
    have he := (coordinateChartDerivativeField_mixed_le_positiveJet hF i a b (G x)).trans
      (hFraw (a + b + 1) (by omega))
    have he' : |mixedDerivative a b (coordinateChartDerivativeField F i) (G x)| ≤
        A (a + b + 1) * (1 + p (a + b + (inputLoss + 1)) z) := by
      simpa only [show a + b + 1 + inputLoss = a + b + (inputLoss + 1) by omega] using he
    exact chartFields_bound_mono hp (le_max_left _ _)
      (zero_le_one.trans (hA (a + b + 1))) (hA₁C (a + b)) he'
  have hheight (a b : ℕ) :
      |mixedDerivative a b h (G x)| ≤
        C (a + b) * (1 + p (a + b + midLoss) z) :=
    chartFields_bound_mono hp hinput (zero_le_one.trans (hA (a + b))) (hAC (a + b))
      ((abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ hh.contDiffOn
        a b (mem_univ (G x))).trans (hhraw (a + b)))
  have hRjets := hRbound z hzR F hF (G x) hκx hFraw
  have hrecip' (a b : ℕ) :
      |mixedDerivative a b (fun q => |planeJacobian F q|⁻¹) (G x)| ≤
        C (a + b) * (1 + p (a + b + midLoss) z) :=
    chartFields_bound_mono hp (le_max_right _ _) (hR (a + b)).le (hRC (a + b))
      ((abs_mixedDerivative_le_norm_iteratedFDeriv hV hrecip a b hxV).trans
        (hRjets (a + b)))
  have hraw' (i : Fin 9) (a b : ℕ) :
      |mixedDerivative a b (coordinatePrimitiveJetField C₀ F h i) (G x)| ≤
        C (a + b) * (1 + p (a + b + midLoss) z) := by
    fin_cases i
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hcoeff' 0 a b
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hcoeff' 1 a b
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hcoeff' 2 a b
    · simpa [coordinatePrimitiveJetField] using hentry 0 a b
    · simpa [coordinatePrimitiveJetField] using hentry 1 a b
    · simpa [coordinatePrimitiveJetField] using hentry 2 a b
    · simpa [coordinatePrimitiveJetField] using hentry 3 a b
    · simpa [coordinatePrimitiveJetField] using hheight a b
    · simpa [coordinatePrimitiveJetField] using hrecip' a b
  have hG' (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k G x‖ ≤ C k * (1 + p (k + midLoss) z) :=
    chartFields_bound_mono hp hinput (zero_le_one.trans (hA k)) (hAC k) (hGraw k hk)
  intro n
  have hb := hbound z hzF 1 le_rfl C₀ F G h V hV hprimitive x hxV hG
    (fun i a b => by simpa only [Real.one_rpow, mul_one] using hraw' i a b)
    (fun k hk => by simpa only [Real.one_rpow, mul_one] using hG' k hk) n
  simpa only [Real.one_rpow, mul_one] using hb

end ContinuousFlexibility.Analysis
