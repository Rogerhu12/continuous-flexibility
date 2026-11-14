module

public import ContinuousFlexibility.Radial.CentralModel
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Uniqueness of the actual square-integrable oscillator ground state

The domain below lists genuine regularity and `MemLp` assumptions. The
eigen-equation is a separate hypothesis, expressed using actual derivatives.
Its annihilation remainder solves a first-order equation; actual `L²`
integrability excludes the growing solution. No spectral decomposition,
closed operator domain, or ground-state uniqueness is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def oscillatorGround (j x : ℝ) : ℝ := exp (-(j * x ^ 2 / 2))

def oscillatorExpression (j : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv ψ) x + j ^ 2 * x ^ 2 * ψ x

/-- A concrete smooth part of the oscillator's quadratic-form domain.
All three `L²` conditions use actual Lebesgue measure on the whole line. -/
def OscillatorEnergyDomain (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ MemLp ψ 2 volume ∧ MemLp (deriv ψ) 2 volume ∧
    MemLp (fun x : ℝ => x * ψ x) 2 volume

def oscillatorAnnihilation (j : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv ψ x + j * x * ψ x

theorem contDiff_oscillatorGround (j : ℝ) : ContDiff ℝ ∞ (oscillatorGround j) :=
  (((contDiff_const.mul (contDiff_id.pow 2)).div_const 2).neg).exp

theorem oscillatorGround_pos (j x : ℝ) : 0 < oscillatorGround j x := exp_pos _

@[simp] theorem oscillatorGround_zero (j : ℝ) : oscillatorGround j 0 = 1 := by
  simp [oscillatorGround]

theorem hasDerivAt_oscillatorGround (j x : ℝ) :
    HasDerivAt (oscillatorGround j) (-j * x * oscillatorGround j x) x := by
  convert ((((hasDerivAt_id x).pow 2).const_mul j).div_const 2).neg.exp using 1
  · funext y
    simp only [oscillatorGround, Pi.pow_apply, Pi.neg_apply, id_eq]
  · simp only [oscillatorGround, Pi.pow_apply, Pi.neg_apply, id_eq]
    ring

theorem deriv_oscillatorGround (j x : ℝ) :
    deriv (oscillatorGround j) x = -j * x * oscillatorGround j x :=
  (hasDerivAt_oscillatorGround j x).deriv

theorem deriv_deriv_oscillatorGround (j x : ℝ) :
    deriv (deriv (oscillatorGround j)) x =
      (j ^ 2 * x ^ 2 - j) * oscillatorGround j x := by
  have hd : deriv (oscillatorGround j) = fun y => -j * y * oscillatorGround j y :=
    funext (deriv_oscillatorGround j)
  rw [hd]
  convert (((hasDerivAt_id x).const_mul (-j)).mul (hasDerivAt_oscillatorGround j x)).deriv using 1
  · rfl
  · simp only [id_eq]
    ring

theorem oscillatorGround_equation (j x : ℝ) :
    oscillatorExpression j (oscillatorGround j) x = j * oscillatorGround j x := by
  unfold oscillatorExpression
  rw [deriv_deriv_oscillatorGround]
  ring

/-- Solving the actual first-order growth equation by an integrating factor. -/
theorem eq_exp_sq_of_hasDerivAt_linear
    {j : ℝ} {g : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (j * x * g x) x) (x : ℝ) :
    g x = g 0 * exp (j * x ^ 2 / 2) := by
  have hd : ∀ y, HasDerivAt (fun z => oscillatorGround j z * g z) 0 y := by
    intro y
    convert (hasDerivAt_oscillatorGround j y).mul (hg y) using 1
    ring
  have hconst := is_const_of_deriv_eq_zero
    (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x 0
  have hval : oscillatorGround j x * g x = g 0 := by
    simpa only [oscillatorGround_zero, one_mul] using hconst
  have hcancel : oscillatorGround j x * exp (j * x ^ 2 / 2) = 1 := by
    rw [oscillatorGround, ← exp_add]
    simp
  calc
    g x = 1 * g x := by ring
    _ = (oscillatorGround j x * exp (j * x ^ 2 / 2)) * g x := by rw [hcancel]
    _ = (oscillatorGround j x * g x) * exp (j * x ^ 2 / 2) := by ring
    _ = _ := by rw [hval]

/-- A nonzero growing Gaussian cannot be square-integrable on the actual
whole real line. Domination would make a nonzero constant `L²`. -/
theorem zero_coefficient_of_memLp_exp_sq
    {j c : ℝ} {g : ℝ → ℝ} (hj : 0 ≤ j) (hg : MemLp g 2 volume)
    (heq : ∀ x, g x = c * exp (j * x ^ 2 / 2)) : c = 0 := by
  have hc : MemLp (fun _ : ℝ => c) 2 volume := by
    apply hg.mono aestronglyMeasurable_const
    filter_upwards with x
    rw [heq x, norm_mul, Real.norm_of_nonneg (exp_pos _).le]
    have he : 1 ≤ exp (j * x ^ 2 / 2) :=
      one_le_exp_iff.mpr (by positivity)
    calc
      ‖c‖ = ‖c‖ * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (norm_nonneg c)
  have hh := (memLp_const_iff (μ := (volume : Measure ℝ)) (p := 2)
    (c := c) (by norm_num) (by norm_num)).mp hc
  simpa only [Real.volume_univ, lt_self_iff_false, or_false] using hh

theorem hasDerivAt_oscillatorAnnihilation
    {j : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (heq : ∀ x, oscillatorExpression j ψ x = j * ψ x) (x : ℝ) :
    HasDerivAt (oscillatorAnnihilation j ψ)
      (j * x * oscillatorAnnihilation j ψ x) x := by
  have hp := (hψ.differentiable (by norm_num) x).hasDerivAt
  have hpp := (hψ.differentiable_deriv_two x).hasDerivAt
  have ho := heq x
  unfold oscillatorExpression at ho
  convert hpp.add (((hasDerivAt_id x).const_mul j).mul hp) using 1
  · funext y
    simp only [oscillatorAnnihilation, Pi.add_apply, Pi.mul_apply, id_eq]
  · simp only [id_eq]
    unfold oscillatorAnnihilation
    nlinarith

theorem memLp_oscillatorAnnihilation
    (j : ℝ) {ψ : ℝ → ℝ} (hψ : OscillatorEnergyDomain ψ) :
    MemLp (oscillatorAnnihilation j ψ) 2 volume := by
  convert hψ.2.2.1.add (hψ.2.2.2.const_mul j) using 1
  funext x
  simp only [oscillatorAnnihilation, Pi.add_apply]
  ring

/-- The factorization remainder actually vanishes; its `L²` hypothesis
comes from the derivative and first-moment conditions in the stated domain. -/
theorem oscillatorAnnihilation_eq_zero
    {j : ℝ} (hj : 0 < j) {ψ : ℝ → ℝ} (hψ : OscillatorEnergyDomain ψ)
    (heq : ∀ x, oscillatorExpression j ψ x = j * ψ x) (x : ℝ) :
    oscillatorAnnihilation j ψ x = 0 := by
  have hg := eq_exp_sq_of_hasDerivAt_linear (hasDerivAt_oscillatorAnnihilation hψ.1 heq)
  have hc := zero_coefficient_of_memLp_exp_sq hj.le (memLp_oscillatorAnnihilation j hψ) hg
  rw [hg x, hc, zero_mul]

/-- Actual whole-line ground-eigenfunction uniqueness in the explicit
`C²` energy domain, with genuine `MemLp` conditions. -/
theorem oscillator_ground_unique
    {j : ℝ} (hj : 0 < j) {ψ : ℝ → ℝ} (hψ : OscillatorEnergyDomain ψ)
    (heq : ∀ x, oscillatorExpression j ψ x = j * ψ x) :
    ψ = fun x => ψ 0 * oscillatorGround j x := by
  have hg := oscillatorAnnihilation_eq_zero hj hψ heq
  have hd : ∀ x, HasDerivAt (fun y => exp (j * y ^ 2 / 2) * ψ y) 0 x := by
    intro x
    have hp := (hψ.1.differentiable (by norm_num) x).hasDerivAt
    have he := hg x
    unfold oscillatorAnnihilation at he
    convert ((((hasDerivAt_id x).pow 2).const_mul j).div_const 2).exp.mul hp using 1
    · funext y
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.pow_apply, id_eq, mul_one]
      linear_combination -(exp (j * x ^ 2 / 2)) * he
  funext x
  have hconst := is_const_of_deriv_eq_zero
    (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x 0
  have hval : exp (j * x ^ 2 / 2) * ψ x = ψ 0 := by
    simpa using hconst
  have hcancel : exp (j * x ^ 2 / 2) * oscillatorGround j x = 1 := by
    rw [oscillatorGround, ← exp_add]
    simp
  calc
    ψ x = 1 * ψ x := by ring
    _ = (exp (j * x ^ 2 / 2) * oscillatorGround j x) * ψ x := by rw [hcancel]
    _ = (exp (j * x ^ 2 / 2) * ψ x) * oscillatorGround j x := by ring
    _ = _ := by rw [hval]

/-- The real-valued square-integrability criterion, without importing the
abstract Hilbert-space realization of `Lp`. -/
theorem oscillator_memLp_two_iff_integrable_sq
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) :
    MemLp f 2 volume ↔ Integrable (fun x => f x ^ 2) volume := by
  simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    (integrable_norm_rpow_iff (p := 2) hf (by norm_num) (by norm_num)).symm

theorem oscillatorGround_sq (j x : ℝ) :
    oscillatorGround j x ^ 2 = exp (-j * x ^ 2) := by
  rw [oscillatorGround, pow_two, ← exp_add]
  congr 1
  ring

/-- The Gaussian belongs to the actual whole-line `L²` space. -/
theorem memLp_oscillatorGround {j : ℝ} (hj : 0 < j) :
    MemLp (oscillatorGround j) 2 volume := by
  apply (oscillator_memLp_two_iff_integrable_sq
    (contDiff_oscillatorGround j).continuous.aestronglyMeasurable).mpr
  convert integrable_exp_neg_mul_sq hj using 1
  funext x
  exact oscillatorGround_sq j x

theorem memLp_mul_oscillatorGround {j : ℝ} (hj : 0 < j) :
    MemLp (fun x : ℝ => x * oscillatorGround j x) 2 volume := by
  apply (oscillator_memLp_two_iff_integrable_sq
    (continuous_id.mul (contDiff_oscillatorGround j).continuous).aestronglyMeasurable).mpr
  have hi : Integrable (fun x : ℝ => x ^ 2 * exp (-j * x ^ 2)) := by
    simpa only [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq hj (s := (2 : ℝ)) (by norm_num)
  convert hi using 1
  funext x
  simp only [Pi.mul_apply, id_eq]
  rw [mul_pow, oscillatorGround_sq]

theorem memLp_deriv_oscillatorGround {j : ℝ} (hj : 0 < j) :
    MemLp (deriv (oscillatorGround j)) 2 volume := by
  convert (memLp_mul_oscillatorGround hj).const_mul (-j) using 1
  funext x
  rw [deriv_oscillatorGround]
  ring

/-- All regularity and integrability fields of the stated domain are
proved for the actual Gaussian, not assumed as a spectral fact. -/
theorem oscillatorGround_energyDomain {j : ℝ} (hj : 0 < j) :
    OscillatorEnergyDomain (oscillatorGround j) :=
  ⟨(contDiff_oscillatorGround j).of_le (by simp), memLp_oscillatorGround hj,
    memLp_deriv_oscillatorGround hj, memLp_mul_oscillatorGround hj⟩

theorem oscillatorEnergyDomain_const_mul
    {ψ : ℝ → ℝ} (hψ : OscillatorEnergyDomain ψ) (c : ℝ) :
    OscillatorEnergyDomain (fun x => c * ψ x) := by
  refine ⟨contDiff_const.mul hψ.1, hψ.2.1.const_mul c, ?_, ?_⟩
  · have hd : deriv (fun x => c * ψ x) = fun x => c * deriv ψ x := by
      funext x
      exact ((hψ.1.differentiable (by norm_num) x).hasDerivAt.const_mul c).deriv
    rw [hd]
    exact hψ.2.2.1.const_mul c
  · convert hψ.2.2.2.const_mul c using 1
    funext x
    ring

theorem oscillatorExpression_const_mul
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (j c x : ℝ) :
    oscillatorExpression j (fun y => c * ψ y) x = c * oscillatorExpression j ψ x := by
  have hd : deriv (fun y => c * ψ y) = fun y => c * deriv ψ y := by
    funext y
    exact ((hψ.differentiable (by norm_num) y).hasDerivAt.const_mul c).deriv
  have hdd : deriv (deriv (fun y => c * ψ y)) x = c * deriv (deriv ψ) x := by
    rw [hd]
    exact ((hψ.differentiable_deriv_two x).hasDerivAt.const_mul c).deriv
  unfold oscillatorExpression
  rw [hdd]
  ring

/-- One-dimensional ground eigenspace in the explicit actual energy
domain, including both membership and uniqueness. This does not assert
that this smooth domain is already the full closed operator domain. -/
theorem oscillator_ground_eigenspace
    {j : ℝ} (hj : 0 < j) (ψ : ℝ → ℝ) :
    (OscillatorEnergyDomain ψ ∧
      ∀ x, oscillatorExpression j ψ x = j * ψ x) ↔
      ∃ c : ℝ, ψ = fun x => c * oscillatorGround j x := by
  constructor
  · rintro ⟨hψ, heq⟩
    exact ⟨ψ 0, oscillator_ground_unique hj hψ heq⟩
  · rintro ⟨c, rfl⟩
    refine ⟨oscillatorEnergyDomain_const_mul (oscillatorGround_energyDomain hj) c, ?_⟩
    intro x
    rw [oscillatorExpression_const_mul ((contDiff_oscillatorGround j).of_le (by simp)),
      oscillatorGround_equation]
    ring

theorem oscillatorGround_two : oscillatorGround 2 = centralOscillatorGround := by
  funext x
  unfold oscillatorGround centralOscillatorGround
  congr 1
  ring

/-- The central Liouville zero equation is exactly oscillator ground
energy two, for the actual radius and density already constructed. -/
theorem central_liouville_zero_iff_ground_equation (ψ : ℝ → ℝ) (x : ℝ) :
    liouvilleSchrodinger 4 centralRadius centralDensityRoot ψ x = 0 ↔
      oscillatorExpression 2 ψ x = 2 * ψ x := by
  unfold liouvilleSchrodinger oscillatorExpression
  rw [centralRadius_liouvilleRho, centralDensityRoot_liouvilleV0, centralRadiusA_sq]
  constructor <;> intro h <;> nlinarith

/-- The actual central mode-two kernel is one-dimensional in the stated
`C²`, `L²` energy domain. Closed-domain identification and higher-mode
spectral completeness are separate remaining results. -/
theorem central_oscillator_kernel_eigenspace (ψ : ℝ → ℝ) :
    (OscillatorEnergyDomain ψ ∧
      ∀ x, liouvilleSchrodinger 4 centralRadius centralDensityRoot ψ x = 0) ↔
      ∃ c : ℝ, ψ = fun x => c * centralOscillatorGround x := by
  rw [← oscillatorGround_two]
  convert oscillator_ground_eigenspace (by norm_num : (0 : ℝ) < 2) ψ using 2
  apply forall_congr'
  intro x
  exact central_liouville_zero_iff_ground_equation ψ x

end ContinuousFlexibility.Radial
