module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The actual Morse ground state

The exponential ground function is smooth and satisfies the actual
second-order differential equation. Its whole-line `L²` condition is
proved by the substitution `t = exp (-x)` into a convergent Gamma-type
integral. Neither integrability nor a spectral classification is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def morseGround (α w x : ℝ) : ℝ := exp (-α * x - w * exp (-x))

def morseAnnihilation (α w : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv ψ x + (α - w * exp (-x)) * ψ x

def morseCreation (α w : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv ψ x + (α - w * exp (-x)) * ψ x

def morseExpression (α w V : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv ψ) x +
    (w ^ 2 * exp (-x) ^ 2 - w * (2 * α + 1) * exp (-x) + V) * ψ x

def morseRho (A B x : ℝ) : ℝ := A * (exp (-x) - exp (-2 * x)) - B

def morseSchrodingerExpression (j A B : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv ψ) x - j ^ 2 * morseRho A B x * ψ x

theorem contDiff_morseGround (α w : ℝ) : ContDiff ℝ ∞ (morseGround α w) :=
  ((contDiff_const.mul contDiff_id).sub
    (contDiff_const.mul contDiff_id.neg.exp)).exp

theorem morseGround_pos (α w x : ℝ) : 0 < morseGround α w x := exp_pos _

theorem hasDerivAt_morseGround (α w x : ℝ) :
    HasDerivAt (morseGround α w) ((-α + w * exp (-x)) * morseGround α w x) x := by
  convert (((hasDerivAt_id x).const_mul (-α)).sub
    (((hasDerivAt_id x).neg.exp).const_mul w)).exp using 1
  · funext y
    simp only [morseGround, Pi.sub_apply, Pi.neg_apply, id_eq]
  · simp only [morseGround, Pi.sub_apply, Pi.neg_apply, id_eq]
    ring

theorem deriv_morseGround (α w x : ℝ) :
    deriv (morseGround α w) x = (-α + w * exp (-x)) * morseGround α w x :=
  (hasDerivAt_morseGround α w x).deriv

theorem deriv_deriv_morseGround (α w x : ℝ) :
    deriv (deriv (morseGround α w)) x =
      ((-α + w * exp (-x)) ^ 2 - w * exp (-x)) * morseGround α w x := by
  rw [show deriv (morseGround α w) =
    (fun y => (-α + w * exp (-y)) * morseGround α w y) from
    funext (deriv_morseGround α w)]
  have hc : HasDerivAt (fun y : ℝ => -α + w * exp (-y)) (-w * exp (-x)) x := by
    convert ((((hasDerivAt_id x).neg.exp).const_mul w).const_add (-α)) using 1 <;> simp
  calc
    _ = (-w * exp (-x)) * morseGround α w x +
        (-α + w * exp (-x)) * ((-α + w * exp (-x)) * morseGround α w x) :=
      (hc.mul (hasDerivAt_morseGround α w x)).deriv
    _ = _ := by ring

theorem morseAnnihilation_ground (α w x : ℝ) :
    morseAnnihilation α w (morseGround α w) x = 0 := by
  unfold morseAnnihilation
  rw [deriv_morseGround]
  ring

theorem morseGround_equation (α w V x : ℝ) :
    morseExpression α w V (morseGround α w) x = (V - α ^ 2) * morseGround α w x := by
  unfold morseExpression
  rw [deriv_deriv_morseGround]
  ring

theorem morseSchrodingerExpression_eq {A : ℝ} (hA : 0 ≤ A) (j B : ℝ)
    (ψ : ℝ → ℝ) (x : ℝ) :
    morseSchrodingerExpression j A B ψ x =
      morseExpression ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) ψ x := by
  have hs := sq_sqrt hA
  have he : exp (-2 * x) = exp (-x) ^ 2 := by
    rw [show -2 * x = -x + -x by ring, exp_add, pow_two]
  unfold morseSchrodingerExpression morseRho morseExpression
  rw [he]
  have hw2 : (j * sqrt A) ^ 2 = j ^ 2 * A := by rw [mul_pow, hs]
  have hc : j * sqrt A * (2 * ((j * sqrt A - 1) / 2) + 1) = j ^ 2 * A := by
    calc
      _ = (j * sqrt A) ^ 2 := by ring
      _ = _ := hw2
  rw [hw2, hc]
  ring

/-- The paper's precise potential and ground energy. -/
theorem morseGround_paper_equation {A : ℝ} (hA : 0 ≤ A) (j B x : ℝ) :
    morseSchrodingerExpression j A B
      (morseGround ((j * sqrt A - 1) / 2) (j * sqrt A)) x =
      (j ^ 2 * B - ((j * sqrt A - 1) / 2) ^ 2) *
        morseGround ((j * sqrt A - 1) / 2) (j * sqrt A) x := by
  rw [morseSchrodingerExpression_eq hA, morseGround_equation]

/-- An actual exponential change of variables into a positive-half-line
Gamma integrand proves square integrability on the whole real line. -/
theorem integrable_morseGround_sq {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    Integrable (fun x : ℝ => morseGround α w x ^ 2) volume := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (2 * α - 1) * exp (-2 * w * t)) (Ioi 0) := by
    simpa only [rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2 * α - 1) (p := 1)
        (b := 2 * w) (by linarith) (by norm_num) (by positivity))
  have hh := ((integrable_comp_exp
    (fun t : ℝ => t ^ (2 * α - 1) * exp (-2 * w * t))).mpr hg).comp_neg
  convert hh using 1
  funext x
  simp only [morseGround, smul_eq_mul]
  rw [pow_two, ← exp_mul, ← exp_add, ← exp_add, ← exp_add]
  congr 1
  ring

theorem memLp_morseGround {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    MemLp (morseGround α w) 2 volume :=
  (memLp_two_iff_integrable_sq (contDiff_morseGround α w).continuous.aestronglyMeasurable).mpr
    (integrable_morseGround_sq hα hw)

theorem morseGround_lower_bound {α w x : ℝ} (hα : α ≤ 0) (hw : 0 ≤ w) (hx : 0 ≤ x) :
    exp (-w) ≤ morseGround α w x := by
  apply exp_le_exp.mpr
  have he : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have ha : 0 ≤ -α * x := mul_nonneg (neg_nonneg.mpr hα) hx
  nlinarith [mul_le_mul_of_nonneg_left he hw]

theorem not_memLp_morseGround_of_nonpos {α w : ℝ} (hα : α ≤ 0) (hw : 0 ≤ w) :
    ¬ MemLp (morseGround α w) 2 volume := by
  intro h
  have hc : IntegrableOn (fun _ : ℝ => exp (-w) ^ 2) (Ioi 0) := by
    apply h.integrable_sq.restrict.mono' continuous_const.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos (exp_pos _))]
    exact pow_le_pow_left₀ (exp_pos _).le (morseGround_lower_bound hα hw hx.le) 2
  rcases (integrableOn_const_iff (C := exp (-w) ^ 2)).mp hc with hz | hfinite
  · exact (pow_ne_zero 2 (exp_ne_zero _)) (enorm_eq_zero.mp hz)
  · simp only [Real.volume_Ioi, lt_self_iff_false] at hfinite

theorem memLp_morseGround_iff {α w : ℝ} (hw : 0 < w) :
    MemLp (morseGround α w) 2 volume ↔ 0 < α := by
  constructor
  · intro h
    by_contra hn
    exact not_memLp_morseGround_of_nonpos (le_of_not_gt hn) hw.le h
  · exact fun hα => memLp_morseGround hα hw

theorem morseGround_weight (α w x : ℝ) :
    exp (-x) * morseGround α w x = morseGround (α + 1) w x := by
  unfold morseGround
  rw [← exp_add]
  congr 1
  ring

theorem memLp_exp_neg_mul_morseGround {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    MemLp (fun x : ℝ => exp (-x) * morseGround α w x) 2 volume := by
  simpa only [morseGround_weight] using
    memLp_morseGround (α := α + 1) (by linarith) hw

theorem memLp_deriv_morseGround {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    MemLp (deriv (morseGround α w)) 2 volume := by
  have h := ((memLp_morseGround hα hw).const_mul (-α)).add
    ((memLp_exp_neg_mul_morseGround hα hw).const_mul w)
  convert h using 1
  funext x
  rw [deriv_morseGround]
  simp only [Pi.add_apply]
  ring

/-- A concrete smooth part of the Morse form domain, verified for the
constructed ground state below. -/
def MorseEnergyDomain (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ MemLp ψ 2 volume ∧ MemLp (deriv ψ) 2 volume ∧
    MemLp (fun x : ℝ => exp (-x) * ψ x) 2 volume

theorem morseGround_energyDomain {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    MorseEnergyDomain (morseGround α w) :=
  ⟨(contDiff_morseGround α w).of_le (by simp), memLp_morseGround hα hw,
    memLp_deriv_morseGround hα hw, memLp_exp_neg_mul_morseGround hα hw⟩

theorem morseGround_paper_memLp_iff {j A : ℝ} (hw : 0 < j * sqrt A) :
    MemLp (morseGround ((j * sqrt A - 1) / 2) (j * sqrt A)) 2 volume ↔
      1 < j * sqrt A := by
  rw [memLp_morseGround_iff hw]
  constructor <;> intro h <;> linarith

theorem morseGround_paper_energyDomain {j A : ℝ} (hw : 1 < j * sqrt A) :
    MorseEnergyDomain (morseGround ((j * sqrt A - 1) / 2) (j * sqrt A)) :=
  morseGround_energyDomain (by linarith) (by linarith)

theorem hasDerivAt_morseAnnihilation {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (α w x : ℝ) :
    HasDerivAt (morseAnnihilation α w ψ)
      (deriv (deriv ψ) x +
        (w * exp (-x) * ψ x + (α - w * exp (-x)) * deriv ψ x)) x := by
  have hp := (hψ.differentiable (by norm_num) x).hasDerivAt
  have hpp := (hψ.differentiable_deriv_two x).hasDerivAt
  have hq : HasDerivAt (fun y : ℝ => α - w * exp (-y)) (w * exp (-x)) x := by
    convert ((((hasDerivAt_id x).neg.exp).const_mul w).const_sub α) using 1 <;> simp
  exact hpp.add (hq.mul hp)

theorem hasDerivAt_morseCreation {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (α w x : ℝ) :
    HasDerivAt (morseCreation α w ψ)
      (-deriv (deriv ψ) x +
        (w * exp (-x) * ψ x + (α - w * exp (-x)) * deriv ψ x)) x := by
  have hp := (hψ.differentiable (by norm_num) x).hasDerivAt
  have hpp := (hψ.differentiable_deriv_two x).hasDerivAt
  have hq : HasDerivAt (fun y : ℝ => α - w * exp (-y)) (w * exp (-x)) x := by
    convert ((((hasDerivAt_id x).neg.exp).const_mul w).const_sub α) using 1 <;> simp
  exact hpp.neg.add (hq.mul hp)

/-- The first Darboux identity, using the actual differentiated functions. -/
theorem morseExpression_factor {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (α w V x : ℝ) :
    morseExpression α w V ψ x =
      morseCreation α w (morseAnnihilation α w ψ) x + (V - α ^ 2) * ψ x := by
  unfold morseCreation
  rw [(hasDerivAt_morseAnnihilation hψ α w x).deriv]
  unfold morseAnnihilation morseExpression
  ring

/-- The partner identity has parameter `α - 1` and the same additive energy. -/
theorem morseExpression_partner_factor {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (α w V x : ℝ) :
    morseExpression (α - 1) w V ψ x =
      morseAnnihilation α w (morseCreation α w ψ) x + (V - α ^ 2) * ψ x := by
  unfold morseAnnihilation
  rw [(hasDerivAt_morseCreation hψ α w x).deriv]
  unfold morseCreation morseExpression
  ring

theorem contDiff_morseAnnihilation {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (α w : ℝ) :
    ContDiff ℝ ∞ (morseAnnihilation α w ψ) :=
  (contDiff_infty_iff_deriv.mp hψ).2.add
    ((contDiff_const.sub (contDiff_const.mul contDiff_id.neg.exp)).mul hψ)

/-- A genuine finite-interval quadratic-form identity, including its boundary
term. The integrals use `dX`, and the derivatives are actual derivatives. -/
theorem integral_morse_factor {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (α w V a b : ℝ) :
    (∫ x in a..b, ψ x * (morseExpression α w V ψ x - (V - α ^ 2) * ψ x)) =
      (∫ x in a..b, morseAnnihilation α w ψ x ^ 2) -
        (ψ b * morseAnnihilation α w ψ b - ψ a * morseAnnihilation α w ψ a) := by
  have hD := contDiff_morseAnnihilation hψ α w
  have hp := (contDiff_infty_iff_deriv.mp hψ).2.continuous
  have hDp := (contDiff_infty_iff_deriv.mp hD).2.continuous
  have hs : IntervalIntegrable (fun x => morseAnnihilation α w ψ x ^ 2) volume a b :=
    (hD.continuous.pow 2).intervalIntegrable a b
  have hf : IntervalIntegrable (fun x => deriv ψ x * morseAnnihilation α w ψ x +
      ψ x * deriv (morseAnnihilation α w ψ) x) volume a b :=
    ((hp.mul hD.continuous).add (hψ.continuous.mul hDp)).intervalIntegrable a b
  have hFTC : (∫ x in a..b, deriv ψ x * morseAnnihilation α w ψ x +
      ψ x * deriv (morseAnnihilation α w ψ) x) =
        ψ b * morseAnnihilation α w ψ b - ψ a * morseAnnihilation α w ψ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => ((hψ.differentiable (by simp) x).hasDerivAt).mul
        ((hD.differentiable (by simp) x).hasDerivAt)) hf
  calc
    _ = ∫ x in a..b, morseAnnihilation α w ψ x ^ 2 -
        (deriv ψ x * morseAnnihilation α w ψ x +
          ψ x * deriv (morseAnnihilation α w ψ) x) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [morseExpression_factor (hψ.of_le (by simp)) α w V x]
      unfold morseCreation morseAnnihilation
      ring
    _ = _ := by rw [intervalIntegral.integral_sub hs hf, hFTC]

theorem integral_morse_shifted_nonneg {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (α w V : ℝ) {a b : ℝ} (hab : a ≤ b) (ha : ψ a = 0) (hb : ψ b = 0) :
    0 ≤ ∫ x in a..b, ψ x * (morseExpression α w V ψ x - (V - α ^ 2) * ψ x) := by
  rw [integral_morse_factor hψ, ha, hb, zero_mul, zero_mul, sub_self, sub_zero]
  exact intervalIntegral.integral_nonneg_of_forall hab (fun x => sq_nonneg _)

end ContinuousFlexibility.Radial
