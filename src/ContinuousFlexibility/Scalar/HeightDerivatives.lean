import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Actual coordinate derivatives of a height

This file proves the height-compatibility identity in Section 3,
`eq:height-compatibility`, and the displayed actual derivatives of `D`.
All partial derivatives are evaluations of mathlib's Frechet derivative.
No independent jet or unproved mixed-derivative hypothesis is substituted
for a derivative of the height.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {f g z : PolarPoint → ℝ} {x : PolarPoint}

@[simp] theorem radialPartial_const (c : ℝ) :
    radialPartial (fun _ : PolarPoint => c) x = 0 := by
  simp [radialPartial]

@[simp] theorem angularPartial_const (c : ℝ) :
    angularPartial (fun _ : PolarPoint => c) x = 0 := by
  simp [angularPartial]

theorem radialPartial_add (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    radialPartial (fun y => f y + g y) x = radialPartial f x + radialPartial g x := by
  simp only [radialPartial, fderiv_fun_add hf hg, add_apply]

theorem angularPartial_add (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    angularPartial (fun y => f y + g y) x = angularPartial f x + angularPartial g x := by
  simp only [angularPartial, fderiv_fun_add hf hg, add_apply]

theorem radialPartial_sub (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    radialPartial (fun y => f y - g y) x = radialPartial f x - radialPartial g x := by
  simp only [radialPartial, fderiv_fun_sub hf hg, sub_apply]

theorem angularPartial_sub (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    angularPartial (fun y => f y - g y) x = angularPartial f x - angularPartial g x := by
  simp only [angularPartial, fderiv_fun_sub hf hg, sub_apply]

theorem radialPartial_mul (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    radialPartial (fun y => f y * g y) x =
      radialPartial f x * g x + f x * radialPartial g x := by
  simp only [radialPartial, fderiv_fun_mul hf hg,
    add_apply, smul_apply, smul_eq_mul]
  ring

theorem angularPartial_mul (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    angularPartial (fun y => f y * g y) x =
      angularPartial f x * g x + f x * angularPartial g x := by
  simp only [angularPartial, fderiv_fun_mul hf hg,
    add_apply, smul_apply, smul_eq_mul]
  ring

theorem radialPartial_sq (hf : DifferentiableAt ℝ f x) :
    radialPartial (fun y => f y ^ 2) x = 2 * f x * radialPartial f x := by
  simp only [radialPartial, (hf.hasFDerivAt.pow 2).fderiv,
    smul_apply, smul_eq_mul]
  norm_num

theorem angularPartial_sq (hf : DifferentiableAt ℝ f x) :
    angularPartial (fun y => f y ^ 2) x = 2 * f x * angularPartial f x := by
  simp only [angularPartial, (hf.hasFDerivAt.pow 2).fderiv,
    smul_apply, smul_eq_mul]
  norm_num

/-- A quotient rule evaluated on any actual coordinate direction. -/
theorem polar_fderiv_div (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) (v : PolarPoint) :
    fderiv ℝ (fun y => f y / g y) x v =
      (fderiv ℝ f x v * g x - f x * fderiv ℝ g x v) / g x ^ 2 := by
  have hinv := (hasDerivAt_inv hg0).hasFDerivAt.comp x hg.hasFDerivAt
  have h := hf.hasFDerivAt.mul hinv
  have heq := h.fderiv
  change fderiv ℝ (fun y => f y / g y) x = _ at heq
  rw [heq]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, Function.comp_apply]
  field_simp [hg0]
  ring

theorem radialPartial_div (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) :
    radialPartial (fun y => f y / g y) x =
      (radialPartial f x * g x - f x * radialPartial g x) / g x ^ 2 :=
  polar_fderiv_div hf hg hg0 (1, 0)

theorem angularPartial_div (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) :
    angularPartial (fun y => f y / g y) x =
      (angularPartial f x * g x - f x * angularPartial g x) / g x ^ 2 :=
  polar_fderiv_div hf hg hg0 (0, 1)

@[simp] theorem radialPartial_fst : radialPartial Prod.fst x = 1 := by
  simp [radialPartial, fderiv_fst]

@[simp] theorem angularPartial_fst : angularPartial Prod.fst x = 0 := by
  simp [angularPartial, fderiv_fst]

@[simp] theorem radialPartial_snd : radialPartial Prod.snd x = 0 := by
  simp [radialPartial, fderiv_snd]

@[simp] theorem angularPartial_snd : angularPartial Prod.snd x = 1 := by
  simp [angularPartial, fderiv_snd]

theorem contDiffAt_radialPartial {n m : ℕ∞ω} (hz : ContDiffAt ℝ n z x)
    (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (radialPartial z) x := by
  exact (hz.fderiv_right hmn).clm_apply contDiffAt_const

theorem contDiffAt_angularPartial {n m : ℕ∞ω} (hz : ContDiffAt ℝ n z x)
    (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (angularPartial z) x := by
  exact (hz.fderiv_right hmn).clm_apply contDiffAt_const

theorem contDiffAt_heightRadial {n m : ℕ∞ω} (hz : ContDiffAt ℝ n z x)
    (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (heightRadial z) x :=
  contDiffAt_radialPartial hz hmn

theorem contDiffAt_heightAngular {n m : ℕ∞ω} (hz : ContDiffAt ℝ n z x)
    (hmn : m + 1 ≤ n) (hr : x.1 ≠ 0) : ContDiffAt ℝ m (heightAngular z) x :=
  (contDiffAt_angularPartial hz hmn).div contDiffAt_fst hr

/-- Differentiating evaluation of the derivative on a constant direction. -/
theorem polar_fderiv_partial
    (hz : DifferentiableAt ℝ (fderiv ℝ z) x) (u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ z y u) x v =
      fderiv ℝ (fderiv ℝ z) x v u := by
  rw [fderiv_clm_apply hz (differentiableAt_const u)]
  simp

/-- Actual mixed partial derivatives commute at a `C²` point. -/
theorem radial_angular_commute (hz : ContDiffAt ℝ 2 z x) :
    radialPartial (angularPartial z) x = angularPartial (radialPartial z) x := by
  have hz' : DifferentiableAt ℝ (fderiv ℝ z) x :=
    (hz.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold radialPartial angularPartial
  rw [polar_fderiv_partial hz', polar_fderiv_partial hz']
  exact (hz.isSymmSndFDerivAt (by norm_num)) (1, 0) (0, 1)

/-- Section 3's exact compatibility `r p_r = k_θ - p`. -/
theorem height_compatibility (hz : ContDiffAt ℝ 2 z x) (hr : x.1 ≠ 0) :
    x.1 * radialPartial (heightAngular z) x =
      angularPartial (heightRadial z) x - heightAngular z x := by
  have hzθ : DifferentiableAt ℝ (angularPartial z) x :=
    (contDiffAt_angularPartial hz (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold heightAngular
  rw [radialPartial_div hzθ differentiableAt_fst hr, radialPartial_fst,
    radial_angular_commute hz]
  unfold heightRadial
  field_simp

theorem radialPartial_profileEnergy {w : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w x.1) :
    radialPartial (profileEnergy w) x = 2 * w x.1 * deriv w x.1 := by
  have h := (hasFDerivAt_const (1 : ℝ) x).add
    ((hw.hasFDerivAt.comp x hasFDerivAt_fst).pow 2)
  change HasFDerivAt (profileEnergy w) _ x at h
  unfold radialPartial
  rw [h.fderiv]
  simp

theorem angularPartial_profileEnergy {w : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w x.1) :
    angularPartial (profileEnergy w) x = 0 := by
  have h := (hasFDerivAt_const (1 : ℝ) x).add
    ((hw.hasFDerivAt.comp x hasFDerivAt_fst).pow 2)
  change HasFDerivAt (profileEnergy w) _ x at h
  unfold angularPartial
  rw [h.fderiv]
  simp

/-- Radial differentiation of the actual discriminant; all factors are functions. -/
theorem radialPartial_polarDiscriminant {w : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 2 z x) (hr : x.1 ≠ 0) :
    radialPartial (polarDiscriminant w z) x =
      radialPartial (profileEnergy w) x * (1 - heightAngular z x ^ 2) -
        2 * profileEnergy w x * heightAngular z x * radialPartial (heightAngular z) x -
        2 * heightRadial z x * radialPartial (heightRadial z) x := by
  have hE : DifferentiableAt ℝ (profileEnergy w) x :=
    ((hw.comp x differentiableAt_fst).pow 2).const_add 1
  have hk := (contDiffAt_heightRadial hz (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp := (contDiffAt_heightAngular hz (m := 1) (by norm_num) hr).differentiableAt one_ne_zero
  have h := (hE.hasFDerivAt.mul
    ((hasFDerivAt_const (1 : ℝ) x).sub (hp.hasFDerivAt.pow 2))).sub
      (hk.hasFDerivAt.pow 2)
  change HasFDerivAt (polarDiscriminant w z) _ x at h
  unfold radialPartial
  rw [h.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
    zero_apply]
  norm_num
  ring

/-- Angular differentiation of the actual discriminant, using radiality of `E`. -/
theorem angularPartial_polarDiscriminant {w : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w x.1) (hz : ContDiffAt ℝ 2 z x) (hr : x.1 ≠ 0) :
    angularPartial (polarDiscriminant w z) x =
      -2 * profileEnergy w x * heightAngular z x * angularPartial (heightAngular z) x -
        2 * heightRadial z x * angularPartial (heightRadial z) x := by
  have hE : DifferentiableAt ℝ (profileEnergy w) x :=
    ((hw.comp x differentiableAt_fst).pow 2).const_add 1
  have hk := (contDiffAt_heightRadial hz (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp := (contDiffAt_heightAngular hz (m := 1) (by norm_num) hr).differentiableAt one_ne_zero
  have h := (hE.hasFDerivAt.mul
    ((hasFDerivAt_const (1 : ℝ) x).sub (hp.hasFDerivAt.pow 2))).sub
      (hk.hasFDerivAt.pow 2)
  change HasFDerivAt (polarDiscriminant w z) _ x at h
  have he := angularPartial_profileEnergy (x := x) hw
  unfold angularPartial at he ⊢
  rw [h.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
    zero_apply]
  rw [he]
  norm_num
  ring

end ContinuousFlexibility
