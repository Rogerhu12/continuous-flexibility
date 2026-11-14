module

public import ContinuousFlexibility.Radial.GaussianLaplaceLeftBounds
public import ContinuousFlexibility.Radial.RadialSymbolBounds

/-!
# Actual left Laplace--Gamma symbols on one fixed tail

The functions below are the genuine integral moments. The Gamma
comparison is identified with its homogeneous expression only on the
positive half-line. Every derivative estimate comes from an actual
shifted moment identity and the proved integral error bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Positive-half-line equality suffices for actual derivative symbols,
because all derivative equalities are local. -/
theorem RadialSymbolBounds.congr {L0 s : ℝ} {f g : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hgf : EqOn g f (Ioi 0)) :
    RadialSymbolBounds L0 s g := by
  refine ⟨hf.1.congr hgf, ?_⟩
  intro r
  obtain ⟨C, hC, hCf⟩ := hf.2 r
  refine ⟨C, hC, ?_⟩
  intro L hL0 hL
  rw [hgf.iteratedDeriv_of_isOpen isOpen_Ioi r hL]
  exact hCf L hL0 hL

theorem gammaLaplaceMoment_left_scale {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) :
    gammaLaplaceMoment β (sqrt 2 * L) = gammaLaplaceMoment β (sqrt 2) * L ^ (-β) := by
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  rw [gammaLaplaceMoment_eq hβ (mul_pos hs hL), gammaLaplaceMoment_eq hβ hs]
  simp only [one_div, ← Real.rpow_neg_eq_inv_rpow]
  rw [Real.mul_rpow hs.le hL.le]
  ring

theorem gammaLaplaceMoment_left_succ {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) :
    gammaLaplaceMoment (β + 1) (sqrt 2 * L) =
      (β / (sqrt 2 * L)) * gammaLaplaceMoment β (sqrt 2 * L) :=
  gammaLaplaceMoment_succ hβ (by positivity)

theorem contDiffOn_gammaLaplaceMoment_left {β : ℝ} (hβ : 0 < β) :
    ContDiffOn ℝ ∞ (fun L => gammaLaplaceMoment β (sqrt 2 * L)) (Ioi 0) := by
  have hp : ContDiffOn ℝ ∞ (fun L : ℝ => L ^ (-β)) (Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun L hL => hL.ne')
  have hs : ContDiffOn ℝ ∞
      (fun L : ℝ => gammaLaplaceMoment β (sqrt 2) * L ^ (-β)) (Ioi 0) :=
    contDiffOn_const.mul hp
  exact hs.congr (fun L hL => gammaLaplaceMoment_left_scale hβ hL)

/-- The comparison moment has its true derivative at every positive
parameter, proved through local equality with its Gamma expression. -/
theorem hasDerivAt_gammaLaplaceMoment_left {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) :
    HasDerivAt (fun x => gammaLaplaceMoment β (sqrt 2 * x))
      (-sqrt 2 * gammaLaplaceMoment (β + 1) (sqrt 2 * L)) L := by
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have heq : (fun x => gammaLaplaceMoment β (sqrt 2 * x)) =ᶠ[𝓝 L]
      (fun x => gammaLaplaceMoment β (sqrt 2) * x ^ (-β)) := by
    filter_upwards [Ioi_mem_nhds hL] with x hx
    exact gammaLaplaceMoment_left_scale hβ hx
  have hd := (hasDerivAt_rpow_const (p := -β) (Or.inl hL.ne')).const_mul
    (gammaLaplaceMoment β (sqrt 2))
  have hder : -sqrt 2 * gammaLaplaceMoment (β + 1) (sqrt 2 * L) =
      gammaLaplaceMoment β (sqrt 2) * (-β * L ^ (-β - 1)) := by
    rw [gammaLaplaceMoment_left_scale (by linarith : 0 < β + 1) hL,
      gammaLaplaceMoment_succ hβ hs,
      show -(β + 1) = -β - 1 by ring]
    field_simp [hs.ne']
  rw [hder]
  exact hd.congr_of_eventuallyEq heq

theorem iteratedDeriv_gammaLaplaceMoment_left {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (k : ℕ) :
    iteratedDeriv k (fun x => gammaLaplaceMoment β (sqrt 2 * x)) L =
      (-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L) := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    have hk : 0 < β + (k : ℝ) := by positivity
    have heq : iteratedDeriv k (fun x => gammaLaplaceMoment β (sqrt 2 * x)) =ᶠ[𝓝 L]
        (fun x => (-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * x)) := by
      filter_upwards [Ioi_mem_nhds hL] with x hx
      exact ih hx
    have hd := (hasDerivAt_gammaLaplaceMoment_left hk hL).const_mul ((-sqrt 2) ^ k)
    change HasDerivAt
      (fun x => (-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * x)) _ L at hd
    have hindex : β + (k : ℝ) + 1 = β + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv, hindex, pow_succ]
    ring

/-- The actual Gamma comparison has all symbol orders on any fixed
threshold, since the estimates hold for every positive parameter. -/
theorem gammaLaplaceMoment_left_symbol {β : ℝ} (hβ : 0 < β) (L0 : ℝ) :
    RadialSymbolBounds L0 (-β) (fun L => gammaLaplaceMoment β (sqrt 2 * L)) := by
  refine ⟨contDiffOn_gammaLaplaceMoment_left hβ, ?_⟩
  intro r
  have hr : 0 < β + (r : ℝ) := by positivity
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  let C : ℝ := sqrt 2 ^ r * gammaLaplaceMoment (β + (r : ℝ)) (sqrt 2)
  refine ⟨C, mul_nonneg (pow_nonneg hs.le _) (gammaLaplaceMoment_pos hr hs).le, ?_⟩
  intro L _ hL
  rw [iteratedDeriv_gammaLaplaceMoment_left hβ hL r, norm_mul, norm_pow, norm_neg,
    Real.norm_eq_abs, abs_of_nonneg hs.le, Real.norm_eq_abs,
    abs_of_pos (gammaLaplaceMoment_pos hr (mul_pos hs hL)), gammaLaplaceMoment_left_scale hr hL]
  rw [show -(β + (r : ℝ)) = -β - (r : ℝ) by ring]
  dsimp [C]
  exact le_of_eq (by ring)

/-- Actual Gaussian--Laplace moments, including every real derivative,
are controlled on one common tail by the Gamma comparison. -/
theorem gaussianLaplaceMoment_left_symbol {β : ℝ} (hβ : 0 < β) (L0 : ℝ) :
    RadialSymbolBounds L0 (-β) (fun L => gaussianLaplaceMoment β (-L)) := by
  refine ⟨((contDiff_gaussianLaplaceMoment hβ).comp contDiff_id.neg).contDiffOn, ?_⟩
  intro r
  have hr : 0 < β + (r : ℝ) := by positivity
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  let C : ℝ := sqrt 2 ^ r * gammaLaplaceMoment (β + (r : ℝ)) (sqrt 2)
  refine ⟨C, mul_nonneg (pow_nonneg hs.le _) (gammaLaplaceMoment_pos hr hs).le, ?_⟩
  intro L _ hL
  rw [iteratedDeriv_gaussianLaplaceMoment_neg hβ r, norm_mul, norm_pow, norm_neg,
    Real.norm_eq_abs, abs_of_nonneg hs.le, Real.norm_eq_abs,
    abs_of_pos (gaussianLaplaceMoment_pos hr (-L))]
  calc
    _ ≤ sqrt 2 ^ r * gammaLaplaceMoment (β + (r : ℝ)) (sqrt 2 * L) :=
      mul_le_mul_of_nonneg_left
        (by linarith [(gaussianLaplaceMoment_left_defect hr hL).1]) (pow_nonneg hs.le _)
    _ = C * L ^ (-β - (r : ℝ)) := by
      rw [gammaLaplaceMoment_left_scale hr hL,
        show -(β + (r : ℝ)) = -β - (r : ℝ) by ring]
      dsimp [C]
      ring

/-- The two-order improvement is proved separately at every actual
derivative, rather than inferred from an undifferentiated error bound. -/
theorem gaussianLaplaceMoment_left_error_symbol {β : ℝ} (hβ : 0 < β) (L0 : ℝ) :
    RadialSymbolBounds L0 (-β - 2)
      (fun L => gaussianLaplaceMoment β (-L) - gammaLaplaceMoment β (sqrt 2 * L)) := by
  have hF := gaussianLaplaceMoment_left_symbol hβ L0
  have hG := gammaLaplaceMoment_left_symbol hβ L0
  refine ⟨hF.1.sub hG.1, ?_⟩
  intro r
  have hr : 0 < β + (r : ℝ) + 1 + 1 := by positivity
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  let C : ℝ := sqrt 2 ^ r * ((1 / 2 : ℝ) *
    gammaLaplaceMoment (β + (r : ℝ) + 1 + 1) (sqrt 2))
  refine ⟨C, mul_nonneg (pow_nonneg hs.le _)
    (mul_nonneg (by norm_num) (gammaLaplaceMoment_pos hr hs).le), ?_⟩
  intro L _ hL
  rw [show (fun L => gaussianLaplaceMoment β (-L) - gammaLaplaceMoment β (sqrt 2 * L)) =
      (fun L => gaussianLaplaceMoment β (-L)) - (fun L => gammaLaplaceMoment β (sqrt 2 * L)) from rfl,
    iteratedDeriv_sub ((hF.contDiffAt hL).of_le (by simp))
      ((hG.contDiffAt hL).of_le (by simp)), iteratedDeriv_gammaLaplaceMoment_left hβ hL r]
  calc
    _ ≤ sqrt 2 ^ r * ((1 / 2 : ℝ) *
        gammaLaplaceMoment (β + (r : ℝ) + 1 + 1) (sqrt 2 * L)) :=
      gaussianLaplaceMoment_left_derivative_error hβ hL r
    _ = C * L ^ (-β - 2 - (r : ℝ)) := by
      rw [gammaLaplaceMoment_left_scale hr hL,
        show -(β + (r : ℝ) + 1 + 1) = -β - 2 - (r : ℝ) by ring]
      dsimp [C]
      ring

theorem gaussianLaplaceMoment_left_lower_constant_pos {β : ℝ} (hβ : 0 < β) :
    0 < gammaLaplaceMoment β (sqrt 2) / 2 :=
  div_pos (gammaLaplaceMoment_pos hβ (sqrt_pos.mpr (by norm_num))) (by norm_num)

/-- One explicit threshold gives a positive denominator lower bound,
independently of every later derivative order. -/
theorem gaussianLaplaceMoment_left_lower {β L : ℝ} (hβ : 0 < β) (hL : β + 1 ≤ L) :
    (gammaLaplaceMoment β (sqrt 2) / 2) * L ^ (-β) ≤ gaussianLaplaceMoment β (-L) := by
  have hLp : 0 < L := by linarith
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hJ : 0 < gammaLaplaceMoment β (sqrt 2 * L) := gammaLaplaceMoment_pos hβ (mul_pos hs hLp)
  have hhalf : β * (β + 1) / (4 * L ^ 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * L ^ 2)).mpr
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ β + 1) hL 2
    nlinarith [sq_nonneg (β + 1)]
  have hr : 1 / 2 ≤ gaussianLaplaceMoment β (-L) / gammaLaplaceMoment β (sqrt 2 * L) := by
    linarith [(gaussianLaplaceMoment_left_relative_error hβ hLp).2]
  have hp := mul_le_mul_of_nonneg_right hr hJ.le
  rw [div_mul_cancel₀ _ hJ.ne'] at hp
  calc
    _ = (1 / 2 : ℝ) * (gammaLaplaceMoment β (sqrt 2) * L ^ (-β)) := by ring
    _ = (1 / 2 : ℝ) * gammaLaplaceMoment β (sqrt 2 * L) := by
      rw [gammaLaplaceMoment_left_scale hβ hLp]
    _ ≤ _ := hp

theorem gaussianLaplaceMoment_left_ne_zero {β : ℝ} (hβ : 0 < β) (L : ℝ) :
    gaussianLaplaceMoment β (-L) ≠ 0 :=
  (gaussianLaplaceMoment_pos hβ (-L)).ne'

theorem gammaLaplaceQuotient_left_symbol (β L0 : ℝ) :
    RadialSymbolBounds L0 (-1) (fun L => β / (sqrt 2 * L)) := by
  have hG := (gammaLaplaceMoment_left_symbol (by norm_num : (0 : ℝ) < 1) L0).const_mul β
  apply hG.congr
  intro L hL
  change β / (sqrt 2 * L) = β * gammaLaplaceMoment 1 (sqrt 2 * L)
  rw [gammaLaplaceMoment_eq (by norm_num : (0 : ℝ) < 1)
    (mul_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) hL),
    Real.rpow_one, Gamma_one, mul_one]
  ring

end ContinuousFlexibility.Radial
