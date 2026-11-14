module

public import ContinuousFlexibility.Analysis.RootHeightPointwiseMaterialJets
public import ContinuousFlexibility.Analysis.RootBoundaryValueIntervals

/-!
# Root chart and height bounds from actual inverse input fields

Only the genuine input fields φ, χ, and the physical radial coefficient
enter the derivative hypotheses. The odd root lower bound and the true
angular normalization derivative supply every positive value interval
needed by the power and reciprocal estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def RootBoundaryMaterialJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (a : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) : Prop :=
  RootChartPointwiseJetBound p loss B z G (0, θ) ∧
    RootHeightPointwiseJetBound p loss B z a G θ ∧
    0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) ∧
    0 < rootSmoothHeight a G (0, θ)

theorem rootBoundary_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ χl al au : ℝ, 0 < χl → 0 < al → al ≤ au →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ, ∀ a : PolarPoint → ℝ,
      ∀ h : ℝ → ℝ, ∀ θ k : ℝ,
      ContDiff ℝ ∞ G →
      (∀ x ζ η, G (x, ζ, η + Real.pi) = G (x, ζ, η) + Real.pi) →
      (∀ η, G (0, 0, η) = h η) → HasDerivAt h k θ → k ∈ Icc (1 / 4 : ℝ) 4 →
      χl ≤ rootOddCoefficient G (0, θ) →
      ContDiffAt ℝ ∞ a (0, θ) → a (0, θ) ∈ Icc al au →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootEven G) (0, θ) →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootOddCoefficient G) (0, θ) →
      PointwiseMaterialJetBound p inputLoss A z a (0, θ) →
      RootBoundaryMaterialJetBound p loss B z a G θ := by
  obtain ⟨chartBase, chartLoss, hchart⟩ :=
    rootChart_pointwise_fixed_loss_material_bound hp hI inputLoss
  obtain ⟨heightBase, heightLoss, hheight⟩ :=
    rootHeight_pointwise_fixed_loss_material_bound hp hI inputLoss
  refine ⟨max inputLoss (max chartBase heightBase), max chartLoss heightLoss, ?_⟩
  intro A hA χl al au hχl hal halu
  let χu := χl + 2 * A 0
  have hχlu : χl ≤ χu := le_add_of_nonneg_right (mul_nonneg (by norm_num) (hA 0).le)
  let αl := al * ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) / 4
  let αu := 4 * au * ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ)
  have hfl : 0 < ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hχl) _
  have hfu : 0 < ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) (hχl.trans_le hχlu)) _
  have hfcompare : ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) ≤
      ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) hχl.le)
      (mul_le_mul_of_nonneg_left hχlu (by norm_num)) (by norm_num)
  have hαl : 0 < αl := div_pos (mul_pos hal hfl) (by norm_num)
  have hαlu : αl ≤ αu := by
    have hprod := mul_le_mul halu hfcompare hfl.le (hal.trans_le halu).le
    dsimp only [αl, αu]
    nlinarith only [hprod, mul_pos hal hfl, mul_pos (hal.trans_le halu) hfu]
  obtain ⟨C, hC, hc⟩ := hchart A hA χl χu hχl hχlu
  obtain ⟨H, hH, hh⟩ := hheight A hA χl χu (1 / 16) 16 αl αu
    hχl hχlu (by norm_num) (by norm_num) hαl hαlu
  let B : ℕ → ℝ := fun n => C n + H n
  refine ⟨B, fun n => add_pos (hC n) (hH n), ?_⟩
  intro z hz G a h θ k hG hperiod hzero hderiv hk hpositive ha havalue hφjet hχjet hajet
  have hzInput : p inputLoss z ≤ 1 := ((hp (le_max_left _ _)) z).trans hz
  have hzChart : p chartBase z ≤ 1 :=
    ((hp ((le_max_left chartBase heightBase).trans (le_max_right _ _))) z).trans hz
  have hzHeight : p heightBase z ≤ 1 :=
    ((hp ((le_max_right chartBase heightBase).trans (le_max_right _ _))) z).trans hz
  have hφperiod : ∀ r, 0 ≤ r → ∀ η,
      rootEven G (r, η + Real.pi) = rootEven G (r, η) + Real.pi :=
    fun r _ η => rootEven_period_add hperiod r η
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hperiod r
  have hφ := (contDiff_extendedRootEven hG Real.pi_ne_zero hφperiod).contDiffAt (x := (0, θ))
  have hχ := (contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχperiod).contDiffAt
    (x := (0, θ))
  have hχvalue : extendedRootOddCoefficient G (0, θ) ∈ Icc χl χu := by
    constructor
    · rw [extendedRootOddCoefficient_of_nonneg G (le_refl (0 : ℝ))]
      exact hpositive
    · have hzeroJet : |extendedRootOddCoefficient G (0, θ)| ≤ A 0 * (1 + p inputLoss z) := by
        simpa only [norm_iteratedFDeriv_zero, zero_add, Real.norm_eq_abs] using hχjet 0
      have hnum : A 0 * (1 + p inputLoss z) ≤ 2 * A 0 := by nlinarith [hA 0]
      exact (le_abs_self _).trans (hzeroJet.trans (hnum.trans
        (le_add_of_nonneg_left hχl.le)))
  have hvalues := rootBoundary_positive_value_intervals hG hperiod hzero hderiv hk
    ha hal havalue hχl hχvalue
  have hCjet := hc z hzChart G (0, θ) hφ hχ rfl hχvalue hφjet hχjet
  have hHjet := hh z hzHeight G a θ hφ hχ ha hχvalue hvalues.1 hvalues.2 hφjet hχjet hajet
  have hJpos : 0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) := by
    rw [planeJacobian_extendedRootEvenOddChart_zero hG Real.pi_ne_zero hχperiod hφperiod
      hzero hderiv (hχl.trans_le hpositive).ne']
    exact mul_pos (rootRadialFactor_pos (hχl.trans_le hpositive))
      ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1)
  have hheightPos : 0 < rootSmoothHeight a G (0, θ) :=
    inv_pos.mpr (Real.sqrt_pos.mpr (hαl.trans_le hvalues.2.1))
  refine ⟨?_, ?_, hJpos, hheightPos⟩
  · exact ⟨hCjet.1,
      hCjet.2.1.mono hp (le_max_left _ _) (fun n => (hC n).le)
        (fun n => le_add_of_nonneg_right (hH n).le),
      hCjet.2.2.1.mono hp (le_max_left _ _) (fun n => (hC n).le)
        (fun n => le_add_of_nonneg_right (hH n).le),
      hCjet.2.2.2.mono hp (le_max_left _ _) (fun n => (hC n).le)
        (fun n => le_add_of_nonneg_right (hH n).le)⟩
  · exact ⟨hHjet.1,
      hHjet.2.1.mono hp (le_max_right _ _) (fun n => (hH n).le)
        (fun n => le_add_of_nonneg_left (hC n).le),
      hHjet.2.2.1.mono hp (le_max_right _ _) (fun n => (hH n).le)
        (fun n => le_add_of_nonneg_left (hC n).le),
      hHjet.2.2.2.mono hp (le_max_right _ _) (fun n => (hH n).le)
        (fun n => le_add_of_nonneg_left (hC n).le)⟩

end ContinuousFlexibility.Analysis
