import ContinuousFlexibility.Radial.MorseWeakEnergy
import ContinuousFlexibility.Radial.OscillatorCompactCore
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Actual compact cutoffs in the weak Morse energy space

Multiplication preserves the actual weak derivative with its genuine product
rule. The fixed smooth cutoff family from `OscillatorCompactCore` then tends
to the identity in the full Hilbert energy norm. Compact support below means
existence of compactly supported representatives of the `L²` classes; it does
not assert compact support of an arbitrarily selected `Lp` representative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

theorem morseMemLp_bounded_mul {χ f : ℝ → ℝ} (hχ : Continuous χ) {C : ℝ}
    (hC : ∀ x, |χ x| ≤ C) (hf : MemLp f 2 volume) :
    MemLp (fun x => χ x * f x) 2 volume := by
  apply hf.of_le_mul (c := C) (hχ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

def morseL2Mul (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) (u : MorseL2) : MorseL2 :=
  (morseMemLp_bounded_mul hχ hC (Lp.memLp u)).toLp (fun x => χ x * u x)

theorem morseL2Mul_coeFn (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) (u : MorseL2) :
    (morseL2Mul χ hχ C hC u : ℝ → ℝ) =ᵐ[volume] (fun x => χ x * u x) :=
  MemLp.coeFn_toLp _

theorem morseL2Mul_norm_le (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) (u : MorseL2) :
    ‖morseL2Mul χ hχ C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [morseL2Mul_coeFn χ hχ C hC u] with x hx
  rw [hx]
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

/-- Actual bounded multiplication on Lebesgue `L²`. -/
def morseL2Multiplier (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) : MorseL2 →L[ℝ] MorseL2 := by
  let L : MorseL2 →ₗ[ℝ] MorseL2 :=
    { toFun := morseL2Mul χ hχ C hC
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [morseL2Mul_coeFn χ hχ C hC (u + v),
          morseL2Mul_coeFn χ hχ C hC u, morseL2Mul_coeFn χ hχ C hC v,
          Lp.coeFn_add u v,
          Lp.coeFn_add (morseL2Mul χ hχ C hC u) (morseL2Mul χ hχ C hC v)] with x hsum hu hv h0 h1
        rw [hsum, h1, h0]
        simp only [Pi.add_apply]
        rw [hu, hv]
        ring
      map_smul' := by
        intro a u
        apply Lp.ext
        filter_upwards [morseL2Mul_coeFn χ hχ C hC (a • u),
          morseL2Mul_coeFn χ hχ C hC u, Lp.coeFn_smul a u,
          Lp.coeFn_smul a (morseL2Mul χ hχ C hC u)] with x hmul hu h0 h1
        change morseL2Mul χ hχ C hC (a • u) x = (a • morseL2Mul χ hχ C hC u) x
        rw [hmul, h1, h0]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hu]
        ring }
  exact L.mkContinuous C (morseL2Mul_norm_le χ hχ C hC)

@[simp] theorem morseL2Multiplier_apply (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) (u : MorseL2) :
    morseL2Multiplier χ hχ C hC u = morseL2Mul χ hχ C hC u := rfl

theorem morseL2Multiplier_pairing (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (u : MorseL2) :
    morseTestPairing φ hφ (morseL2Multiplier χ hχ C hC u) =
      morseTestPairing (fun x => χ x * φ x) (morseMemLp_bounded_mul hχ hC hφ) u := by
  rw [morseTestPairing_apply, morseTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [morseL2Mul_coeFn χ hχ C hC u] with x hx
  rw [morseL2Multiplier_apply, hx]
  ring

/-- The product rule is derived from the defining compact-test equation. -/
theorem MorseWeakDerivativeL2.bounded_smooth_mul {u d : MorseL2}
    (hu : MorseWeakDerivativeL2 u d) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C₀ C₁ : ℝ) (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) :
    MorseWeakDerivativeL2
      (morseL2Multiplier χ hχ.continuous C₀ hC₀ u)
      (morseL2Multiplier χ hχ.continuous C₀ hC₀ d +
        morseL2Multiplier (deriv χ) (contDiff_infty_iff_deriv.mp hχ).2.continuous C₁ hC₁ u) := by
  apply (morseWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2
  let ht := compactSmooth_morseEnergyDomain hφ hc
  have htest : ContDiff ℝ ∞ (fun x => χ x * φ x) := hχ.mul hφ
  have hsupport : HasCompactSupport (fun x => χ x * φ x) := hc.mul_left
  have hT := (morseWeakDerivativeL2_iff_pairings _ _).mp hu _ htest hsupport
  have hdiff : deriv (fun x => χ x * φ x) =
      fun x => deriv χ x * φ x + χ x * deriv φ x := by
    funext x
    exact (((hχ.differentiable (by simp) x).hasDerivAt).mul
      ((hφ.differentiable (by simp) x).hasDerivAt)).deriv
  have hA := morseMemLp_bounded_mul hχd.continuous hC₁ ht.2.1
  have hB := morseMemLp_bounded_mul hχ.continuous hC₀ ht.2.2.1
  have hsplit : morseTestPairing (deriv (fun x => χ x * φ x))
      (compactSmooth_morseEnergyDomain htest hsupport).2.2.1 u =
        morseTestPairing (fun x => deriv χ x * φ x) hA u +
          morseTestPairing (fun x => χ x * deriv φ x) hB u := by
    rw [morseTestPairing_apply, hdiff, morseTestPairing_apply, morseTestPairing_apply]
    calc
      _ = ∫ x : ℝ, u x * (deriv χ x * φ x) + u x * (χ x * deriv φ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by
        simpa only [Pi.add_apply, Pi.mul_apply] using
          integral_add ((Lp.memLp u).integrable_mul hA) ((Lp.memLp u).integrable_mul hB)
  rw [hsplit] at hT
  rw [map_add, morseL2Multiplier_pairing, morseL2Multiplier_pairing, morseL2Multiplier_pairing]
  linarith [hT]

def morseCutoffTriple (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) :
    MorseWeakEnergy →L[ℝ] MorseEnergyTriple :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => MorseL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (morseL2Multiplier χ hχ.continuous C₀ hC₀).comp morseEnergyBase,
      (morseL2Multiplier χ hχ.continuous C₀ hC₀).comp morseEnergyDerivative +
        (morseL2Multiplier (deriv χ) (contDiff_infty_iff_deriv.mp hχ).2.continuous C₁ hC₁).comp
          morseEnergyBase,
      (morseL2Multiplier χ hχ.continuous C₀ hC₀).comp morseEnergyWeight])

theorem morseCutoffTriple_mem (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) (u : MorseWeakEnergy) :
    morseCutoffTriple χ hχ C₀ C₁ hC₀ hC₁ u ∈ morseEnergyGraph := by
  apply (mem_morseEnergyGraph_iff _).mpr
  refine ⟨(morseEnergyDerivative_weak u).bounded_smooth_mul χ hχ C₀ C₁ hC₀ hC₁, ?_⟩
  filter_upwards [morseL2Mul_coeFn χ hχ.continuous C₀ hC₀ (morseEnergyWeight u),
    morseEnergyWeight_ae u,
    morseL2Mul_coeFn χ hχ.continuous C₀ hC₀ (morseEnergyBase u)] with x hz hw hu
  change morseL2Mul χ hχ.continuous C₀ hC₀ (morseEnergyWeight u) x =
    exp (-x) * morseL2Mul χ hχ.continuous C₀ hC₀ (morseEnergyBase u) x
  rw [hz, hw, hu]
  ring

/-- A genuine continuous linear cutoff operator on the weak energy domain. -/
def morseEnergyCutoff (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) :
    MorseWeakEnergy →L[ℝ] MorseWeakEnergy :=
  (morseCutoffTriple χ hχ C₀ C₁ hC₀ hC₁).codRestrict morseEnergyGraph
    (morseCutoffTriple_mem χ hχ C₀ C₁ hC₀ hC₁)

@[simp] theorem morseEnergyCutoff_base (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) (u : MorseWeakEnergy) :
    morseEnergyBase (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) =
      morseL2Multiplier χ hχ.continuous C₀ hC₀ (morseEnergyBase u) := rfl

@[simp] theorem morseEnergyCutoff_derivative (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) (u : MorseWeakEnergy) :
    morseEnergyDerivative (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) =
      morseL2Multiplier χ hχ.continuous C₀ hC₀ (morseEnergyDerivative u) +
        morseL2Multiplier (deriv χ) (contDiff_infty_iff_deriv.mp hχ).2.continuous C₁ hC₁
          (morseEnergyBase u) := rfl

@[simp] theorem morseEnergyCutoff_weight (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C₀ C₁ : ℝ)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |deriv χ x| ≤ C₁) (u : MorseWeakEnergy) :
    morseEnergyWeight (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) =
      morseL2Multiplier χ hχ.continuous C₀ hC₀ (morseEnergyWeight u) := rfl

/-- Compact representatives for all three weak energy coordinates. -/
def MorseCompactEnergy (u : MorseWeakEnergy) : Prop :=
  ∀ i : Fin 3, ∃ f : ℝ → ℝ, HasCompactSupport f ∧
    (morseEnergyCoordinate i u : ℝ → ℝ) =ᵐ[volume] f

theorem morseEnergyCutoff_compact (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (C₀ C₁ : ℝ) (hC₀ : ∀ x, |χ x| ≤ C₀)
    (hC₁ : ∀ x, |deriv χ x| ≤ C₁) (u : MorseWeakEnergy) :
    MorseCompactEnergy (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) := by
  intro i
  fin_cases i
  · refine ⟨fun x => χ x * morseEnergyBase u x, hc.mul_right, ?_⟩
    change (morseEnergyBase (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) : ℝ → ℝ) =ᵐ[volume] _
    rw [morseEnergyCutoff_base, morseL2Multiplier_apply]
    exact morseL2Mul_coeFn _ _ _ _ _
  · refine ⟨fun x => χ x * morseEnergyDerivative u x + deriv χ x * morseEnergyBase u x,
      hc.mul_right.add hc.deriv.mul_right, ?_⟩
    change (morseEnergyDerivative (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) : ℝ → ℝ) =ᵐ[volume] _
    rw [morseEnergyCutoff_derivative]
    filter_upwards [Lp.coeFn_add
      (morseL2Multiplier χ hχ.continuous C₀ hC₀ (morseEnergyDerivative u))
      (morseL2Multiplier (deriv χ) (contDiff_infty_iff_deriv.mp hχ).2.continuous C₁ hC₁
        (morseEnergyBase u)),
      morseL2Mul_coeFn χ hχ.continuous C₀ hC₀ (morseEnergyDerivative u),
      morseL2Mul_coeFn (deriv χ) (contDiff_infty_iff_deriv.mp hχ).2.continuous C₁ hC₁
        (morseEnergyBase u)] with x hadd h0 h1
    rw [hadd]
    simp only [Pi.add_apply, morseL2Multiplier_apply, h0, h1]
  · refine ⟨fun x => χ x * morseEnergyWeight u x, hc.mul_right, ?_⟩
    change (morseEnergyWeight (morseEnergyCutoff χ hχ C₀ C₁ hC₀ hC₁ u) : ℝ → ℝ) =ᵐ[volume] _
    rw [morseEnergyCutoff_weight, morseL2Multiplier_apply]
    exact morseL2Mul_coeFn _ _ _ _ _

def morseCutoffDerivativeConstant : ℝ := Classical.choose oscillatorCutoff_derivative_bounds

theorem morseCutoffDerivativeConstant_nonneg : 0 ≤ morseCutoffDerivativeConstant :=
  (Classical.choose_spec oscillatorCutoff_derivative_bounds).1

theorem morseScaledCutoff_abs_le_one (N : ℕ) (x : ℝ) :
    |scaledOscillatorCutoff N x| ≤ 1 := by
  rw [abs_of_nonneg (scaledOscillatorCutoff_nonneg N x)]
  exact scaledOscillatorCutoff_le_one N x

theorem morseScaledCutoff_deriv_abs_le (N : ℕ) (x : ℝ) :
    |deriv (scaledOscillatorCutoff N) x| ≤ morseCutoffDerivativeConstant := by
  have hc := Classical.choose_spec oscillatorCutoff_derivative_bounds
  have hh := (scaledOscillatorCutoff_derivative_bounds hc.2.1 hc.2.2 N x).1
  apply hh.trans
  change morseCutoffDerivativeConstant / ((N : ℝ) + 1) ≤ morseCutoffDerivativeConstant
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hN]
  nlinarith [mul_nonneg morseCutoffDerivativeConstant_nonneg (Nat.cast_nonneg (α := ℝ) N)]

def morseScaledEnergyCutoff (N : ℕ) : MorseWeakEnergy →L[ℝ] MorseWeakEnergy :=
  morseEnergyCutoff (scaledOscillatorCutoff N) (contDiff_scaledOscillatorCutoff N)
    1 morseCutoffDerivativeConstant (morseScaledCutoff_abs_le_one N) (morseScaledCutoff_deriv_abs_le N)

theorem morseScaledEnergyCutoff_compact (N : ℕ) (u : MorseWeakEnergy) :
    MorseCompactEnergy (morseScaledEnergyCutoff N u) :=
  morseEnergyCutoff_compact _ _ (scaledOscillatorCutoff_hasCompactSupport N) _ _ _ _ u

/-- Dominated convergence is in actual whole-line Lebesgue `L²`. -/
theorem morseScaledL2Multiplier_tendsto (u : MorseL2) :
    Tendsto (fun N : ℕ => morseL2Multiplier (scaledOscillatorCutoff N)
      (contDiff_scaledOscillatorCutoff N).continuous 1 (morseScaledCutoff_abs_le_one N) u)
      atTop (𝓝 u) := by
  have hF := fun N => morseMemLp_bounded_mul (contDiff_scaledOscillatorCutoff N).continuous
    (morseScaledCutoff_abs_le_one N) (Lp.memLp u)
  have hdom : ∀ N x, |scaledOscillatorCutoff N x * u x - u x| ≤ |u x| := by
    intro N x
    have hχ : |scaledOscillatorCutoff N x - 1| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (scaledOscillatorCutoff_le_one N x))]
      linarith [scaledOscillatorCutoff_nonneg N x]
    calc
      _ = |scaledOscillatorCutoff N x - 1| * |u x| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ 1 * |u x| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
      _ = _ := one_mul _
  have hl := oscillator_tendsto_toLp_of_dominated hF (Lp.memLp u) (Lp.memLp u) hdom
    (fun x => by simpa only [one_mul] using (tendsto_scaledOscillatorCutoff x).mul_const (u x))
  simpa only [morseL2Multiplier_apply, morseL2Mul, Lp.toLp_coeFn] using hl

theorem morseScaledDerivativeMultiplier_tendsto (u : MorseL2) :
    Tendsto (fun N : ℕ => morseL2Multiplier (deriv (scaledOscillatorCutoff N))
      (contDiff_infty_iff_deriv.mp (contDiff_scaledOscillatorCutoff N)).2.continuous
      morseCutoffDerivativeConstant (morseScaledCutoff_deriv_abs_le N) u)
      atTop (𝓝 0) := by
  have hF := fun N => morseMemLp_bounded_mul
    (contDiff_infty_iff_deriv.mp (contDiff_scaledOscillatorCutoff N)).2.continuous
    (morseScaledCutoff_deriv_abs_le N) (Lp.memLp u)
  have hdom : ∀ N x, |deriv (scaledOscillatorCutoff N) x * u x - 0| ≤
      |morseCutoffDerivativeConstant * u x| := by
    intro N x
    simpa only [sub_zero, abs_mul, abs_of_nonneg morseCutoffDerivativeConstant_nonneg] using
      mul_le_mul_of_nonneg_right (morseScaledCutoff_deriv_abs_le N x) (abs_nonneg (u x))
  have hl := oscillator_tendsto_toLp_of_dominated hF
    (MemLp.zero' : MemLp (fun _ : ℝ => (0 : ℝ)) 2 volume)
    ((Lp.memLp u).const_mul morseCutoffDerivativeConstant) hdom
    (fun x => by simpa only [zero_mul] using
      (tendsto_derivatives_scaledOscillatorCutoff x).1.mul_const (u x))
  have hz : (MemLp.zero' : MemLp (fun _ : ℝ => (0 : ℝ)) 2 volume).toLp
      (fun _ : ℝ => (0 : ℝ)) = (0 : MorseL2) := by
    change (MemLp.zero' : MemLp (0 : ℝ → ℝ) 2 volume).toLp 0 = 0
    exact MemLp.toLp_zero _
  rw [hz] at hl
  simpa only [morseL2Multiplier_apply, morseL2Mul] using hl

/-- All three physical coordinates converge, including the derivative
commutator `χ'_N u`; hence convergence is in the full energy norm. -/
theorem morseScaledEnergyCutoff_tendsto (u : MorseWeakEnergy) :
    Tendsto (fun N : ℕ => morseScaledEnergyCutoff N u) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  have h0 := morseScaledL2Multiplier_tendsto (morseEnergyBase u)
  have h2 := morseScaledL2Multiplier_tendsto (morseEnergyWeight u)
  have h1 := (morseScaledL2Multiplier_tendsto (morseEnergyDerivative u)).add
    (morseScaledDerivativeMultiplier_tendsto (morseEnergyBase u))
  have hp : Tendsto (fun N : ℕ => fun i : Fin 3 => (morseScaledEnergyCutoff N u).val i)
      atTop (𝓝 (fun i : Fin 3 => u.val i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Tendsto (fun N : ℕ => morseEnergyBase (morseScaledEnergyCutoff N u))
        atTop (𝓝 (morseEnergyBase u))
      simpa only [morseScaledEnergyCutoff, morseEnergyCutoff_base] using h0
    · change Tendsto (fun N : ℕ => morseEnergyDerivative (morseScaledEnergyCutoff N u))
        atTop (𝓝 (morseEnergyDerivative u))
      simpa only [morseScaledEnergyCutoff, morseEnergyCutoff_derivative, add_zero] using h1
    · change Tendsto (fun N : ℕ => morseEnergyWeight (morseScaledEnergyCutoff N u))
        atTop (𝓝 (morseEnergyWeight u))
      simpa only [morseScaledEnergyCutoff, morseEnergyCutoff_weight] using h2
  have ht := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => MorseL2)).symm.continuous.tendsto
    (fun i : Fin 3 => u.val i)).comp hp
  convert ht using 1 <;> rfl

theorem morseCompactEnergy_dense : Dense {u : MorseWeakEnergy | MorseCompactEnergy u} := by
  intro u
  exact mem_closure_of_tendsto (morseScaledEnergyCutoff_tendsto u)
    (Eventually.of_forall (fun N => morseScaledEnergyCutoff_compact N u))

end ContinuousFlexibility.Radial
