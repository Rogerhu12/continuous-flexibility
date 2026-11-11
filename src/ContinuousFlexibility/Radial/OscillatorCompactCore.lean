import ContinuousFlexibility.Radial.OscillatorClosedGraph
import ContinuousFlexibility.Radial.CentralGraphAdjoint
import ContinuousFlexibility.Radial.OscillatorDifferentialPairing
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual compact cutoffs for the central differential operator

The cutoff below is an actual smooth compactly supported function. Its
rescalings have two explicitly controlled derivatives. These are used to
compare the compact-test distribution graph with the Hermite graph core.
The Friedrichs quadratic-form identification is a separate obligation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open scoped RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

def oscillatorCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (2 - x) * Real.smoothTransition (2 + x)

theorem contDiff_oscillatorCutoff : ContDiff ℝ ∞ oscillatorCutoff :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

theorem oscillatorCutoff_nonneg (x : ℝ) : 0 ≤ oscillatorCutoff x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem oscillatorCutoff_le_one (x : ℝ) : oscillatorCutoff x ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by norm_num)

theorem oscillatorCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : oscillatorCutoff x = 1 := by
  have h := abs_le.mp hx
  unfold oscillatorCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem oscillatorCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : oscillatorCutoff x = 0 := by
  rcases le_abs.mp hx with h | h
  · unfold oscillatorCutoff
    rw [show Real.smoothTransition (2 - x) = 0 from
      Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · unfold oscillatorCutoff
    rw [show Real.smoothTransition (2 + x) = 0 from
      Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

theorem oscillatorCutoff_hasCompactSupport : HasCompactSupport oscillatorCutoff := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))
  intro x hx
  apply oscillatorCutoff_eq_zero
  by_contra h
  have h' := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨by linarith [h'.1], h'.2.le⟩

theorem oscillatorCutoff_derivative_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, |deriv oscillatorCutoff x| ≤ C) ∧
      ∀ x, |deriv (deriv oscillatorCutoff) x| ≤ C := by
  have h1 : ContDiff ℝ ∞ (deriv oscillatorCutoff) :=
    (contDiff_infty_iff_deriv.mp contDiff_oscillatorCutoff).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv oscillatorCutoff)) :=
    (contDiff_infty_iff_deriv.mp h1).2
  obtain ⟨C₁, hC₁⟩ := h1.continuous.bounded_above_of_compact_support
    oscillatorCutoff_hasCompactSupport.deriv
  obtain ⟨C₂, hC₂⟩ := h2.continuous.bounded_above_of_compact_support
    oscillatorCutoff_hasCompactSupport.deriv.deriv
  refine ⟨max 0 (max C₁ C₂), le_max_left _ _, ?_, ?_⟩
  · intro x
    exact (hC₁ x).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro x
    exact (hC₂ x).trans (le_trans (le_max_right _ _) (le_max_right _ _))

def scaledOscillatorCutoff (N : ℕ) (x : ℝ) : ℝ :=
  oscillatorCutoff (x / ((N : ℝ) + 1))

theorem contDiff_scaledOscillatorCutoff (N : ℕ) :
    ContDiff ℝ ∞ (scaledOscillatorCutoff N) :=
  contDiff_oscillatorCutoff.comp (contDiff_id.div_const _)

theorem scaledOscillatorCutoff_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ scaledOscillatorCutoff N x := oscillatorCutoff_nonneg _

theorem scaledOscillatorCutoff_le_one (N : ℕ) (x : ℝ) :
    scaledOscillatorCutoff N x ≤ 1 := oscillatorCutoff_le_one _

theorem scaledOscillatorCutoff_hasCompactSupport (N : ℕ) :
    HasCompactSupport (scaledOscillatorCutoff N) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Icc (-2 * ((N : ℝ) + 1)) (2 * ((N : ℝ) + 1))))
  intro x hx
  apply oscillatorCutoff_eq_zero
  rw [abs_div, abs_of_pos hN, le_div_iff₀ hN]
  by_contra h
  have h' := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨by linarith [h'.1], h'.2.le⟩

theorem deriv_scaledOscillatorCutoff (N : ℕ) (x : ℝ) :
    deriv (scaledOscillatorCutoff N) x =
      deriv oscillatorCutoff (x / ((N : ℝ) + 1)) / ((N : ℝ) + 1) := by
  change deriv (fun y : ℝ => oscillatorCutoff (y / ((N : ℝ) + 1))) x = _
  have hd := (((contDiff_oscillatorCutoff.differentiable (by simp) _).hasDerivAt).comp x
    ((hasDerivAt_id x).div_const ((N : ℝ) + 1))).deriv
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul]
    using hd

theorem deriv_deriv_scaledOscillatorCutoff (N : ℕ) (x : ℝ) :
    deriv (deriv (scaledOscillatorCutoff N)) x =
      deriv (deriv oscillatorCutoff) (x / ((N : ℝ) + 1)) / ((N : ℝ) + 1) ^ 2 := by
  have h1 := (contDiff_infty_iff_deriv.mp contDiff_oscillatorCutoff).2
  have heq : deriv (scaledOscillatorCutoff N) = fun y =>
      deriv oscillatorCutoff (y / ((N : ℝ) + 1)) / ((N : ℝ) + 1) :=
    funext (deriv_scaledOscillatorCutoff N)
  rw [heq]
  have hd := ((((h1.differentiable (by simp) _).hasDerivAt).comp x
    ((hasDerivAt_id x).div_const ((N : ℝ) + 1))).div_const ((N : ℝ) + 1)).deriv
  simp only [Function.comp_def, id_eq] at hd
  convert hd using 1
  field_simp

theorem tendsto_scaledOscillatorCutoff (x : ℝ) :
    Tendsto (fun N : ℕ => scaledOscillatorCutoff N x) atTop (𝓝 1) := by
  have hi : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hx : Tendsto (fun N : ℕ => x / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul x
  have h0 : oscillatorCutoff 0 = 1 := oscillatorCutoff_eq_one (by norm_num)
  simpa only [scaledOscillatorCutoff, Function.comp_def, h0] using
    (contDiff_oscillatorCutoff.continuous.tendsto (0 : ℝ)).comp hx

/-- The actual differential commutator with a smooth cutoff. -/
theorem central_expression_mul (j : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (fun y => f y * g y) x =
      f x * liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot g x -
        2 * deriv f x * deriv g x - deriv (deriv f) x * g x := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hg1 := (contDiff_infty_iff_deriv.mp hg).2
  have hd : deriv (fun y => f y * g y) = fun y => deriv f y * g y + f y * deriv g y :=
    funext fun y => (((hf.differentiable (by simp) y).hasDerivAt).mul
      ((hg.differentiable (by simp) y).hasDerivAt)).deriv
  have hdd := (((hf1.differentiable (by simp) x).hasDerivAt).mul
    ((hg.differentiable (by simp) x).hasDerivAt)).add
    (((hf.differentiable (by simp) x).hasDerivAt).mul
      ((hg1.differentiable (by simp) x).hasDerivAt))
  change HasDerivAt (fun y => deriv f y * g y + f y * deriv g y) _ x at hdd
  rw [central_liouvilleSchrodinger, central_liouvilleSchrodinger, hd, hdd.deriv]
  ring

theorem scaledOscillatorCutoff_derivative_bounds {C : ℝ}
    (hC₁ : ∀ x, |deriv oscillatorCutoff x| ≤ C)
    (hC₂ : ∀ x, |deriv (deriv oscillatorCutoff) x| ≤ C) (N : ℕ) (x : ℝ) :
    |deriv (scaledOscillatorCutoff N) x| ≤ C / ((N : ℝ) + 1) ∧
    |deriv (deriv (scaledOscillatorCutoff N)) x| ≤ C / ((N : ℝ) + 1) ^ 2 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [deriv_scaledOscillatorCutoff, deriv_deriv_scaledOscillatorCutoff,
    abs_div, abs_div, abs_of_pos hN, abs_of_pos (sq_pos_of_pos hN)]
  exact ⟨div_le_div_of_nonneg_right (hC₁ _) hN.le,
    div_le_div_of_nonneg_right (hC₂ _) (sq_nonneg _)⟩

theorem tendsto_derivatives_scaledOscillatorCutoff (x : ℝ) :
    Tendsto (fun N : ℕ => deriv (scaledOscillatorCutoff N) x) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => deriv (deriv (scaledOscillatorCutoff N)) x) atTop (𝓝 0) := by
  obtain ⟨C, hC, hC₁, hC₂⟩ := oscillatorCutoff_derivative_bounds
  have hi : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim₁ : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul C
  have hlim₂ : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero]
      using (hi.pow 2).const_mul C
  have h₁ := squeeze_zero (fun N => abs_nonneg (deriv (scaledOscillatorCutoff N) x))
    (fun N => (scaledOscillatorCutoff_derivative_bounds hC₁ hC₂ N x).1) hlim₁
  have h₂ := squeeze_zero
    (fun N => abs_nonneg (deriv (deriv (scaledOscillatorCutoff N)) x))
    (fun N => (scaledOscillatorCutoff_derivative_bounds hC₁ hC₂ N x).2) hlim₂
  constructor
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using h₁)
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using h₂)

theorem contDiff_centralExpression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℝ) :
    ContDiff ℝ ∞ (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) := by
  have h1 := (contDiff_infty_iff_deriv.mp hψ).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hpot : ContDiff ℝ ∞ (fun x : ℝ =>
      j ^ 2 * x ^ 2 + centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA) := by fun_prop
  convert h2.neg.add (hpot.mul hψ) using 1
  funext x
  exact central_liouvilleSchrodinger j ψ x

theorem hasCompactSupport_centralExpression {ψ : ℝ → ℝ}
    (hψ : HasCompactSupport ψ) (j : ℝ) :
    HasCompactSupport (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) := by
  convert hψ.deriv.deriv.neg.add
    (hψ.mul_left (f := fun x : ℝ =>
      j ^ 2 * x ^ 2 + centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA)) using 1
  funext x
  exact central_liouvilleSchrodinger j ψ x

theorem compactSmooth_energyDomain {ψ : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) : OscillatorEnergyDomain ψ := by
  have h1 := (contDiff_infty_iff_deriv.mp hs).2
  refine ⟨hs.of_le (by simp), hs.continuous.memLp_of_hasCompactSupport hc, ?_, ?_⟩
  · exact h1.continuous.memLp_of_hasCompactSupport hc.deriv
  · exact (continuous_id.mul hs.continuous).memLp_of_hasCompactSupport hc.mul_left

theorem compactSmooth_centralImage_memLp {ψ : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (j : ℝ) :
    MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) 2 volume :=
  (contDiff_centralExpression hs j).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_centralExpression hc j)

private theorem realL2_norm_sq_sub_toLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x : ℝ, (f x - g x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), MemLp.coeFn_toLp hf,
    MemLp.coeFn_toLp hg] with x hsub hfx hgx
  rw [hsub]
  simp only [Pi.sub_apply, hfx, hgx, RCLike.inner_apply, conj_trivial]
  ring

/-- Dominated convergence in genuine Lebesgue `L²`, proved from the
integral of the squared difference. -/
theorem oscillator_tendsto_toLp_of_dominated
    {F : ℕ → ℝ → ℝ} {f B : ℝ → ℝ}
    (hF : ∀ N, MemLp (F N) 2 volume) (hf : MemLp f 2 volume)
    (hB : MemLp B 2 volume) (hbound : ∀ N x, |F N x - f x| ≤ |B x|)
    (hlim : ∀ x, Tendsto (fun N => F N x) atTop (𝓝 (f x))) :
    Tendsto (fun N => (hF N).toLp (F N)) atTop (𝓝 (hf.toLp f)) := by
  have hBsq := (oscillator_memLp_two_iff_integrable_sq hB.aestronglyMeasurable).mp hB
  have hsq : Tendsto (fun N => ∫ x : ℝ, (F N x - f x) ^ 2) atTop (𝓝 0) := by
    simpa only [Pi.sub_apply, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun x => B x ^ 2)
        (fun N => (((hF N).sub hf).aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable)
        hBsq
        (fun N => Eventually.of_forall (fun x => by
          change ‖(F N x - f x) ^ 2‖ ≤ B x ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F N x - f x))]
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (F N x - f x)) (hbound N x) 2))
        (Eventually.of_forall (fun x => (hlim x |>.sub_const (f x)).pow 2)))
  have hnormsq : Tendsto (fun N => ‖(hF N).toLp (F N) - hf.toLp f‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [realL2_norm_sq_sub_toLp] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm

def compactHermiteFunction (j : ℝ) (n N : ℕ) (x : ℝ) : ℝ :=
  scaledOscillatorCutoff N x * normalizedOscillatorHermite j n x

theorem contDiff_compactHermiteFunction (j : ℝ) (n N : ℕ) :
    ContDiff ℝ ∞ (compactHermiteFunction j n N) :=
  (contDiff_scaledOscillatorCutoff N).mul (contDiff_normalizedOscillatorHermite j n)

theorem compactHermiteFunction_hasCompactSupport (j : ℝ) (n N : ℕ) :
    HasCompactSupport (compactHermiteFunction j n N) :=
  (scaledOscillatorCutoff_hasCompactSupport N).mul_right

theorem compactHermiteFunction_memLp (j : ℝ) (n N : ℕ) :
    MemLp (compactHermiteFunction j n N) 2 volume :=
  (contDiff_compactHermiteFunction j n N).continuous.memLp_of_hasCompactSupport
    (compactHermiteFunction_hasCompactSupport j n N)

theorem compactHermiteImage_memLp (j : ℝ) (n N : ℕ) :
    MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (compactHermiteFunction j n N)) 2 volume :=
  compactSmooth_centralImage_memLp (contDiff_compactHermiteFunction j n N)
    (compactHermiteFunction_hasCompactSupport j n N) j

theorem compactHermiteFunction_tendsto_L2 {j : ℝ} (hj : 0 < j) (n : ℕ) :
    Tendsto (fun N => (compactHermiteFunction_memLp j n N).toLp
      (compactHermiteFunction j n N)) atTop (𝓝 (hermiteL2Vector hj n)) := by
  apply oscillator_tendsto_toLp_of_dominated (compactHermiteFunction_memLp j n)
    (normalizedOscillatorHermite_energyDomain hj n).2.1
    (normalizedOscillatorHermite_energyDomain hj n).2.1
  · intro N x
    have hχ : |scaledOscillatorCutoff N x - 1| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [scaledOscillatorCutoff_nonneg N x, scaledOscillatorCutoff_le_one N x]
    calc
      |compactHermiteFunction j n N x - normalizedOscillatorHermite j n x| =
          |scaledOscillatorCutoff N x - 1| * |normalizedOscillatorHermite j n x| := by
        rw [← abs_mul]
        congr 1
        unfold compactHermiteFunction
        ring
      _ ≤ |normalizedOscillatorHermite j n x| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
  · intro x
    simpa only [compactHermiteFunction, one_mul] using
      (tendsto_scaledOscillatorCutoff x).mul_const (normalizedOscillatorHermite j n x)

theorem compactHermiteImage_apply (j : ℝ) (n N : ℕ) (x : ℝ) (hj : 0 < j) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (compactHermiteFunction j n N) x =
      scaledOscillatorCutoff N x *
        (centralSpectralLevel j n * normalizedOscillatorHermite j n x) -
      2 * deriv (scaledOscillatorCutoff N) x * deriv (normalizedOscillatorHermite j n) x -
      deriv (deriv (scaledOscillatorCutoff N)) x * normalizedOscillatorHermite j n x := by
  change liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
    (fun y => scaledOscillatorCutoff N y * normalizedOscillatorHermite j n y) x = _
  rw [central_expression_mul j (contDiff_scaledOscillatorCutoff N)
      (contDiff_normalizedOscillatorHermite j n), central_normalizedHermite_spectralLevel hj]

theorem compactHermiteImage_tendsto_pointwise {j : ℝ} (hj : 0 < j) (n : ℕ) (x : ℝ) :
    Tendsto (fun N => liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (compactHermiteFunction j n N) x) atTop
      (𝓝 (centralSpectralLevel j n * normalizedOscillatorHermite j n x)) := by
  have hχ := tendsto_scaledOscillatorCutoff x
  have hd := tendsto_derivatives_scaledOscillatorCutoff x
  have hh := ((hχ.mul_const (centralSpectralLevel j n * normalizedOscillatorHermite j n x)).sub
    ((hd.1.const_mul 2).mul_const (deriv (normalizedOscillatorHermite j n) x))).sub
      (hd.2.mul_const (normalizedOscillatorHermite j n x))
  simpa only [compactHermiteImage_apply j n _ x hj, one_mul, mul_zero, zero_mul, sub_zero] using hh

/-- Both the input and its genuine central differential image are
approximated by the same compactly supported smooth cutoffs. -/
theorem compactHermiteImage_tendsto_L2 {j : ℝ} (hj : 0 < j) (n : ℕ) :
    Tendsto (fun N => (compactHermiteImage_memLp j n N).toLp
      (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
        (compactHermiteFunction j n N))) atTop
      (𝓝 (centralSpectralLevel j n • hermiteL2Vector hj n)) := by
  obtain ⟨C, hC, hC₁, hC₂⟩ := oscillatorCutoff_derivative_bounds
  let e : ℝ → ℝ := normalizedOscillatorHermite j n
  let E : ℝ := centralSpectralLevel j n
  let B : ℝ → ℝ := fun x => (|E| + C) * |e x| + (2 * C) * |deriv e x|
  have he : MemLp e 2 volume := (normalizedOscillatorHermite_energyDomain hj n).2.1
  have he' : MemLp (deriv e) 2 volume :=
    (normalizedOscillatorHermite_energyDomain hj n).2.2.1
  have hB : MemLp B 2 volume := by
    convert (he.norm.const_mul (|E| + C)).add (he'.norm.const_mul (2 * C)) using 1
  have hEf : MemLp (fun x => E * e x) 2 volume := he.const_mul E
  have hlim := oscillator_tendsto_toLp_of_dominated (compactHermiteImage_memLp j n)
    hEf hB ?_ (compactHermiteImage_tendsto_pointwise hj n)
  · have hEq : hEf.toLp (fun x => E * e x) =
        centralSpectralLevel j n • hermiteL2Vector hj n := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp hEf,
        Lp.coeFn_smul E (hermiteL2Vector hj n), hermiteL2Vector_coeFn hj n] with x hx hy hz
      rw [hx, hy]
      simp only [Pi.smul_apply, smul_eq_mul, hz, e]
    rwa [hEq] at hlim
  · intro N x
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hN2 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
    have hd := scaledOscillatorCutoff_derivative_bounds hC₁ hC₂ N x
    have hd₁ : |deriv (scaledOscillatorCutoff N) x| ≤ C :=
      hd.1.trans ((div_le_iff₀ hN).mpr (by nlinarith))
    have hd₂ : |deriv (deriv (scaledOscillatorCutoff N)) x| ≤ C :=
      hd.2.trans ((div_le_iff₀ (sq_pos_of_pos hN)).mpr
        (by nlinarith [mul_le_mul_of_nonneg_left hN2 hC]))
    have hχ : |scaledOscillatorCutoff N x - 1| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [scaledOscillatorCutoff_nonneg N x,
        scaledOscillatorCutoff_le_one N x]
    have h₁ : |(scaledOscillatorCutoff N x - 1) * (E * e x)| ≤ |E| * |e x| := by
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right hχ
        (mul_nonneg (abs_nonneg E) (abs_nonneg (e x)))]
    have h₂ : |2 * deriv (scaledOscillatorCutoff N) x * deriv e x| ≤
        2 * C * |deriv e x| := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [mul_le_mul_of_nonneg_right hd₁ (abs_nonneg (deriv e x))]
    have h₃ : |deriv (deriv (scaledOscillatorCutoff N)) x * e x| ≤ C * |e x| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hd₂ (abs_nonneg (e x))
    have hid : liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
        (compactHermiteFunction j n N) x - E * e x =
        (scaledOscillatorCutoff N x - 1) * (E * e x) -
          2 * deriv (scaledOscillatorCutoff N) x * deriv e x -
          deriv (deriv (scaledOscillatorCutoff N)) x * e x := by
      rw [compactHermiteImage_apply j n N x hj]
      dsimp [E, e]
      ring
    rw [hid]
    have htri := abs_sub ((scaledOscillatorCutoff N x - 1) * (E * e x) -
      2 * deriv (scaledOscillatorCutoff N) x * deriv e x)
      (deriv (deriv (scaledOscillatorCutoff N)) x * e x)
    have htri' := abs_sub ((scaledOscillatorCutoff N x - 1) * (E * e x))
      (2 * deriv (scaledOscillatorCutoff N) x * deriv e x)
    rw [abs_of_nonneg (show 0 ≤ B x by dsimp [B]; positivity)]
    dsimp [B]
    linarith

private theorem hermiteCoefficient_toLp (j : ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (n : ℕ) :
    hermiteCoefficient j (hf.toLp f) n =
      ∫ x : ℝ, f x * normalizedOscillatorHermite j n x := by
  unfold hermiteCoefficient
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx]

/-- Any genuine smooth-energy differential pair lies in the same closed
graph; its coefficients follow from actual whole-line Green pairing. -/
theorem central_smooth_energy_graph {j : ℝ} (hj : 0 < j) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) 2 volume) :
    (hψ.2.1.toLp ψ,
      hHψ.toLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ)) ∈
      centralClosedGraph hj := by
  apply (mem_centralClosedGraph_iff _ _ _).mpr
  intro n
  rw [hermiteCoefficient_toLp, hermiteCoefficient_toLp]
  exact central_normalizedHermite_pairing hj hψ hHψ n

private theorem realL2_inner_toLp_right (u : HermiteL2) {φ : ℝ → ℝ}
    (hφ : MemLp φ 2 volume) :
    ⟪u, hφ.toLp φ⟫_ℝ = ∫ x : ℝ, u x * φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The actual compact-test distribution equation. The test class is
genuinely smooth and compactly supported on the real line. -/
def CentralCompactWeakEquation (j : ℝ) (u v : HermiteL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : ℝ, v x * φ x) =
      ∫ x : ℝ, u x * liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x

/-- The compact-test weak domain is exactly the genuine Hermite closed
graph. The reverse implication uses actual compact cutoffs converging in
both components of the differential graph. -/
theorem centralClosedGraph_iff_compact_weak {j : ℝ} (hj : 0 < j) (u v : HermiteL2) :
    (u, v) ∈ centralClosedGraph hj ↔ CentralCompactWeakEquation j u v := by
  constructor
  · intro huv φ hs hc
    have hφ := compactSmooth_energyDomain hs hc
    have hHφ := compactSmooth_centralImage_memLp hs hc j
    have hpair := central_smooth_energy_graph hj hφ hHφ
    have hsym := centralClosedGraph_symmetric hj u v _ _ huv hpair
    rw [realL2_inner_toLp_right, realL2_inner_toLp_right] at hsym
    exact hsym
  · intro hweak
    apply (mem_centralClosedGraph_iff hj u v).mpr
    intro n
    have hN (N : ℕ) :
        ⟪v, (compactHermiteFunction_memLp j n N).toLp (compactHermiteFunction j n N)⟫_ℝ =
          ⟪u, (compactHermiteImage_memLp j n N).toLp
            (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
              (compactHermiteFunction j n N))⟫_ℝ := by
      rw [realL2_inner_toLp_right, realL2_inner_toLp_right]
      exact hweak _ (contDiff_compactHermiteFunction j n N)
        (compactHermiteFunction_hasCompactSupport j n N)
    have hl := ((innerSL ℝ v).continuous.tendsto (hermiteL2Vector hj n)).comp
      (compactHermiteFunction_tendsto_L2 hj n)
    have hr := ((innerSL ℝ u).continuous.tendsto
      (centralSpectralLevel j n • hermiteL2Vector hj n)).comp
        (compactHermiteImage_tendsto_L2 hj n)
    have heq : ⟪v, hermiteL2Vector hj n⟫_ℝ =
        ⟪u, centralSpectralLevel j n • hermiteL2Vector hj n⟫_ℝ :=
      tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun N => (hN N).symm))
    rw [inner_hermiteL2Vector_right, real_inner_smul_right,
      inner_hermiteL2Vector_right] at heq
    exact heq

private theorem central_expression_add (j : ℝ) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (φ + ψ) x =
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x +
        liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x := by
  rw [central_liouvilleSchrodinger_eq_oscillator_shift,
    central_liouvilleSchrodinger_eq_oscillator_shift,
    central_liouvilleSchrodinger_eq_oscillator_shift]
  rw [show φ + ψ = (fun y => φ y + ψ y) from rfl,
    oscillatorExpression_add j (hφ.of_le (by simp)) (hψ.of_le (by simp))]
  ring

private theorem central_expression_smul (j a : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (a • φ) x =
      a * liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x := by
  change liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
    (fun y => a * φ y) x = _
  rw [central_liouvilleSchrodinger_eq_oscillator_shift,
    central_liouvilleSchrodinger_eq_oscillator_shift,
    oscillatorExpression_const_mul (hφ.of_le (by simp))]
  ring

/-- The graph consists exactly of genuine smooth compactly supported
functions and their actual central differential images, as L² classes. -/
def centralCompactSmoothGraph (j : ℝ) : Submodule ℝ (HermiteL2 × HermiteL2) where
  carrier := {p | ∃ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
    p = ((compactSmooth_energyDomain hs hc).2.1.toLp φ,
      (compactSmooth_centralImage_memLp hs hc j).toLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ))}
  zero_mem' := by
    have hs : ContDiff ℝ ∞ (0 : ℝ → ℝ) := contDiff_const
    have hc : HasCompactSupport (0 : ℝ → ℝ) := HasCompactSupport.zero
    refine ⟨0, hs, hc, ?_⟩
    apply Prod.ext
    · rfl
    · symm
      change (compactSmooth_centralImage_memLp hs hc j).toLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (0 : ℝ → ℝ)) =
          (0 : HermiteL2)
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (compactSmooth_centralImage_memLp hs hc j),
        Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx hz
      rw [hx, hz]
      simp only [Pi.zero_apply, central_liouvilleSchrodinger, deriv_zero,
        neg_zero, mul_zero, add_zero]
  add_mem' := by
    rintro p q ⟨φ, hsφ, hcφ, rfl⟩ ⟨ψ, hsψ, hcψ, rfl⟩
    refine ⟨φ + ψ, hsφ.add hsψ, hcφ.add hcψ, ?_⟩
    apply Prod.ext
    · rfl
    · symm
      calc
        _ = ((compactSmooth_centralImage_memLp hsφ hcφ j).add
            (compactSmooth_centralImage_memLp hsψ hcψ j)).toLp
              (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ +
                liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) := by
          exact MemLp.toLp_congr
            (compactSmooth_centralImage_memLp (hsφ.add hsψ) (hcφ.add hcψ) j)
            ((compactSmooth_centralImage_memLp hsφ hcφ j).add
              (compactSmooth_centralImage_memLp hsψ hcψ j))
            (Eventually.of_forall (central_expression_add j hsφ hsψ))
        _ = _ := MemLp.toLp_add
          (compactSmooth_centralImage_memLp hsφ hcφ j)
          (compactSmooth_centralImage_memLp hsψ hcψ j)
  smul_mem' := by
    rintro a p ⟨φ, hs, hc, rfl⟩
    have hsa : ContDiff ℝ ∞ (a • φ) := contDiff_const.smul hs
    have hca : HasCompactSupport (a • φ) := by
      convert hc.smul_left (f := fun _ : ℝ => a) using 1
    refine ⟨a • φ, hsa, hca, ?_⟩
    apply Prod.ext
    · symm
      exact MemLp.toLp_const_smul a (compactSmooth_energyDomain hs hc).2.1
    · symm
      calc
        _ = ((compactSmooth_centralImage_memLp hs hc j).const_smul a).toLp
            (a • liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ) := by
          exact MemLp.toLp_congr
            (compactSmooth_centralImage_memLp hsa hca j)
            ((compactSmooth_centralImage_memLp hs hc j).const_smul a)
            (Eventually.of_forall (central_expression_smul j a hs))
        _ = _ := MemLp.toLp_const_smul a (compactSmooth_centralImage_memLp hs hc j)

theorem mem_centralCompactSmoothGraph (j : ℝ) (p : HermiteL2 × HermiteL2) :
    p ∈ centralCompactSmoothGraph j ↔
      ∃ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        p = ((compactSmooth_energyDomain hs hc).2.1.toLp φ,
          (compactSmooth_centralImage_memLp hs hc j).toLp
            (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)) :=
  Iff.rfl

/-- The smooth compact graph is contained in the closed differential graph. -/
theorem centralCompactSmoothGraph_le {j : ℝ} (hj : 0 < j) :
    centralCompactSmoothGraph j ≤ centralClosedGraph hj := by
  intro p hp
  rcases (mem_centralCompactSmoothGraph j p).mp hp with ⟨φ, hs, hc, rfl⟩
  exact central_smooth_energy_graph hj (compactSmooth_energyDomain hs hc)
    (compactSmooth_centralImage_memLp hs hc j)

/-- Actual compactly supported smooth functions form a graph core for
the same central closed differential realization. -/
theorem centralCompactSmoothGraph_closure {j : ℝ} (hj : 0 < j) :
    (centralCompactSmoothGraph j).topologicalClosure = centralClosedGraph hj := by
  apply le_antisymm
  · exact (centralCompactSmoothGraph j).topologicalClosure_minimal
      (centralCompactSmoothGraph_le hj) (centralClosedGraph_isClosed hj)
  · apply (centralFiniteGraph hj).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro p ⟨n, rfl⟩
      change (hermiteL2Vector hj n, centralSpectralLevel j n • hermiteL2Vector hj n) ∈
        closure (centralCompactSmoothGraph j : Set (HermiteL2 × HermiteL2))
      apply mem_closure_of_tendsto
        ((compactHermiteFunction_tendsto_L2 hj n).prodMk_nhds
          (compactHermiteImage_tendsto_L2 hj n))
      apply Eventually.of_forall
      intro N
      apply (mem_centralCompactSmoothGraph j _).mpr
      exact ⟨compactHermiteFunction j n N, contDiff_compactHermiteFunction j n N,
        compactHermiteFunction_hasCompactSupport j n N, rfl⟩
    · exact (centralCompactSmoothGraph j).isClosed_topologicalClosure

end ContinuousFlexibility.Radial
