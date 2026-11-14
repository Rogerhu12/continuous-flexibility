module

public import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds
public import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
public import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Actual positive powers with one fixed state loss

A positive value interval gives a fixed smooth extension of the scalar
power function. Its true derivatives are bounded on that compact interval.
The existing partition estimate then controls the actual composition.
The low order and loss precede the exponent, value interval, and state;
no jets of the powered field occur among the hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem exists_smooth_positivePower_extension
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (a : ℝ) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧
      (∀ x ∈ Icc l u, Φ =ᶠ[𝓝 x] (fun y : ℝ => y ^ a)) ∧
      ∃ D : ℕ → ℝ, ∀ n : ℕ, ∀ x ∈ Icc l u,
        ‖iteratedFDeriv ℝ n Φ x‖ ≤ D n := by
  have hw : l / 2 ≤ u + 1 := by linarith
  have he : 0 < l / 4 := div_pos hl (by norm_num)
  let C := circleFlowSmoothTimeClamp (l / 2) (u + 1) (l / 4) hw he
  have hC : ContDiff ℝ ∞ C := contDiff_circleFlowSmoothTimeClamp hw he
  have hCpos (x : ℝ) : 0 < C x := by
    have hh := (circleFlowSmoothTimeClamp_mem hw he x).1
    change l / 2 - l / 4 < C x at hh
    linarith
  let Φ : ℝ → ℝ := fun x => C x ^ a
  have hΦ : ContDiff ℝ ∞ Φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact hC.contDiffAt.rpow_const_of_ne (hCpos x).ne'
  have heq (x : ℝ) (hx : x ∈ Icc l u) : Φ =ᶠ[𝓝 x] (fun y : ℝ => y ^ a) := by
    have hxin : x ∈ Ioo (l / 2) (u + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds hxin] with y hy
    change circleFlowSmoothTimeClamp (l / 2) (u + 1) (l / 4) hw he y ^ a = y ^ a
    rw [circleFlowSmoothTimeClamp_eq hw he ⟨hy.1.le, hy.2.le⟩]
  have hbound (n : ℕ) : ∃ M : ℝ, ∀ x ∈ Icc l u,
      ‖iteratedFDeriv ℝ n Φ x‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hΦ.continuous_iteratedFDeriv (by simp : (n : ℕ∞ω) ≤ ∞)).continuousOn
  choose D hD using hbound
  exact ⟨Φ, hΦ, heq, D, hD⟩

/-- The bound applies to the ordinary derivatives of the actual positive
power, including order zero. The value interval is uniform in the state,
and its constants enter only after the common low order and loss. -/
theorem positivePower_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u a : ℝ, 0 < l → l ≤ u →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ g : X → ℝ, ∀ x : X,
      ContDiffAt ℝ ∞ g x → g x ∈ Icc l u →
      (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n g x‖ ≤
        A n * (1 + p (n + inputLoss) z)) →
      ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun y => g y ^ a) x‖ ≤
        B n * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hcomposition⟩ :=
    coordinateComposition_fixed_loss_material_bound (X := X) (Y := ℝ) (Z := ℝ)
      hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA l u a hl hlu
  obtain ⟨Φ, hΦ, heq, D, hD⟩ := exists_smooth_positivePower_extension hl hlu a
  let M : ℕ → ℝ := fun n => 1 + |D n| + A n
  have hM (n : ℕ) : 1 ≤ M n := by
    dsimp only [M]
    linarith [abs_nonneg (D n), hA n]
  obtain ⟨C, hC, hbound⟩ := hcomposition M hM
  let B : ℕ → ℝ := fun n => if n = 0 then 1 + |D 0| else C (n - 1)
  have hB (n : ℕ) : 0 < B n := by
    by_cases hn : n = 0
    · simpa only [B, if_pos hn] using add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg (D 0))
    · simpa only [B, if_neg hn] using hC (n - 1)
  refine ⟨B, hB, ?_⟩
  intro z hz g x hg hrange hjet n
  have hfg : (Φ ∘ g) =ᶠ[𝓝 x] (fun y => g y ^ a) :=
    (heq (g x) hrange).comp_tendsto hg.continuousAt
  have hactual := (hfg.iteratedFDeriv ℝ n).self_of_nhds
  by_cases hn : n = 0
  · subst n
    have hv : ‖Φ (g x)‖ ≤ D 0 := by
      simpa only [norm_iteratedFDeriv_zero] using hD 0 (g x) hrange
    rw [← hactual, norm_iteratedFDeriv_zero, Function.comp_apply]
    have hcoef : D 0 ≤ B 0 := by
      simp only [B, if_pos rfl]
      exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)
    exact hv.trans (hcoef.trans
      (le_mul_of_one_le_right (hB 0).le
        (le_add_of_nonneg_right (apply_nonneg _ _))))
  · have hnpos : 1 ≤ n := by omega
    have houter (k : ℕ) (_hk : 1 ≤ k) :
        ‖iteratedFDeriv ℝ k Φ (g x)‖ ≤
          M k * (1 : ℝ) ^ M k * (1 + p (k + inputLoss) z) := by
      have hDM : D k ≤ M k := by
        dsimp only [M]
        linarith [le_abs_self (D k), hA k]
      simpa only [Real.one_rpow, mul_one] using (hD k (g x) hrange).trans
        (hDM.trans (le_mul_of_one_le_right (zero_le_one.trans (hM k))
          (le_add_of_nonneg_right (apply_nonneg _ _))))
    have hinner (k : ℕ) (hk : 1 ≤ k) :
        ‖iteratedFDeriv ℝ k g x‖ ≤
          M k * (1 : ℝ) ^ M k * (1 + p (k + inputLoss) z) := by
      have hAM : A k ≤ M k := by
        dsimp only [M]
        linarith [abs_nonneg (D k)]
      simpa only [Real.one_rpow, mul_one] using (hjet k hk).trans
        (mul_le_mul_of_nonneg_right hAM
          (add_nonneg zero_le_one (apply_nonneg _ _)))
    have hb := hbound z hz 1 le_rfl Φ g x hΦ.contDiffAt hg houter hinner (n - 1)
    rw [Nat.sub_add_cancel hnpos] at hb
    rw [← hactual]
    simpa only [B, if_neg hn, Real.one_rpow, mul_one] using hb

end ContinuousFlexibility.Analysis
