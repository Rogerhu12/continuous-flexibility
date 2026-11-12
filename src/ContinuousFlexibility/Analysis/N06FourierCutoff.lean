import ContinuousFlexibility.Analysis.SpacesCircleFourierCut
import ContinuousFlexibility.Radial.R11bLpConvergence
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Strong finite Fourier cutoff convergence in the actual angular L² norm

The existing Fourier isometry sends a cutoff to the corresponding finite
sum of coordinates. Square-summability proves strong convergence, and the
projection bound supplies a uniform squared-error majorant for radial Fubini.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

def n06FourierCutoff (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem n06FourierCutoff_neg (N : ℕ) (n : ℤ) :
    -n ∈ n06FourierCutoff N ↔ n ∈ n06FourierCutoff N := by
  simp only [n06FourierCutoff, Finset.mem_Icc]
  omega

theorem n06FourierCutoff_tendsto : Tendsto n06FourierCutoff atTop atTop := by
  have hmono : Monotone n06FourierCutoff := by
    intro N M hNM n hn
    simp only [n06FourierCutoff, Finset.mem_Icc] at hn ⊢
    omega
  apply hmono.tendsto_atTop_finset
  intro n
  refine ⟨n.natAbs, ?_⟩
  simp only [n06FourierCutoff, Finset.mem_Icc]
  rw [← Int.abs_eq_natAbs]
  exact ⟨neg_abs_le n, le_abs_self n⟩

theorem n06_circleFourierCut_norm_le (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (f : AngleL2) :
    ‖circleFourierJetCutFun s 0 f‖ ≤ ‖f‖ := by
  simpa only [one_smul, one_mul] using
    circleFourierJetCutFun_weighted_norm_le s hs 0 f 1 (by norm_num : (0 : ℝ) ≤ 1)
      (fun n _ => by simp)

theorem n06_circleFourierCut_transform (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (f : AngleL2) :
    circleFourierTransform (circleFourierJetCutFun s 0 f) =
      ∑ n ∈ s, lp.single 2 n (circleFourierTransform f n) := by
  apply lp.ext
  funext n
  rw [circleFourierTransform_jetCut_apply s hs 0 f n]
  simp only [pow_zero, one_mul, lp.coeFn_sum, lp.coeFn_single,
    Finset.sum_apply, Finset.sum_pi_single]

theorem n06_circleFourierCut_tendsto (f : AngleL2) :
    Tendsto (fun N => circleFourierJetCutFun (n06FourierCutoff N) 0 f)
      atTop (𝓝 f) := by
  apply circleFourierTransform.isometry.tendsto_nhds_iff.mpr
  have h := (lp.hasSum_single ENNReal.ofNat_ne_top (circleFourierTransform f)).comp
    n06FourierCutoff_tendsto
  change Tendsto (fun N => circleFourierTransform
    (circleFourierJetCutFun (n06FourierCutoff N) 0 f)) atTop
      (𝓝 (circleFourierTransform f))
  have heq : (fun N => circleFourierTransform
      (circleFourierJetCutFun (n06FourierCutoff N) 0 f)) =
      fun N => ∑ n ∈ n06FourierCutoff N, lp.single 2 n (circleFourierTransform f n) := by
    funext N
    exact n06_circleFourierCut_transform _ (n06FourierCutoff_neg N) f
  rw [heq]
  exact h

/-- Equality of the actual Fourier symbols makes differentiated cutoffs
of the zeroth field equal to ordinary cutoffs of the stored derivative. -/
theorem n06_circleFourierJetCut_eq_of_symbols (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) {f g : AngleL2} (j : ℕ)
    (hcoeff : ∀ n, circleFourierCoeff g n =
      (2 * Complex.I * (n : ℂ)) ^ j * circleFourierCoeff f n) :
    circleFourierJetCutFun s j f = circleFourierJetCutFun s 0 g := by
  apply circleFourierCoeff_injective
  funext n
  rw [circleFourierJetCutFun_coeff s hs j f n,
    circleFourierJetCutFun_coeff s hs 0 g n, hcoeff n]
  simp only [pow_zero, one_mul]

theorem n06_circleFourierJetCut_tendsto_of_symbols {f g : AngleL2} (j : ℕ)
    (hcoeff : ∀ n, circleFourierCoeff g n =
      (2 * Complex.I * (n : ℂ)) ^ j * circleFourierCoeff f n) :
    Tendsto (fun N => circleFourierJetCutFun (n06FourierCutoff N) j f)
      atTop (𝓝 g) := by
  simpa only [n06_circleFourierJetCut_eq_of_symbols _ (n06FourierCutoff_neg _) j hcoeff]
    using n06_circleFourierCut_tendsto g

/-- The raw polynomial of an arbitrary representative, before choosing its
L² class. Its coefficients are the original half-period integrals. -/
def n06CircleFourierCut (s : Finset ℤ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (circleFourierPolynomial s (circleFourierCoeff f) θ).re

theorem n06CircleFourierCut_contDiff (s : Finset ℤ) (f : ℝ → ℝ) :
    ContDiff ℝ ∞ (n06CircleFourierCut s f) :=
  Complex.reCLM.contDiff.comp (circleFourierPolynomial_contDiff s (circleFourierCoeff f))

theorem n06CircleFourierCut_periodic (s : Finset ℤ) (f : ℝ → ℝ) :
    Function.Periodic (n06CircleFourierCut s f) Real.pi := by
  intro θ
  exact congrArg Complex.re (circleFourierPolynomial_periodic s (circleFourierCoeff f) θ)

theorem n06CircleFourierCut_toLp {f : ℝ → ℝ} (hf : MemLp f 2 angleMeasure)
    (s : Finset ℤ) (j : ℕ) :
    (memLp_angleMeasure_iteratedDeriv_of_contDiff (n06CircleFourierCut_contDiff s f) j).toLp
        (iteratedDeriv j (n06CircleFourierCut s f)) =
      circleFourierJetCutFun s j (hf.toLp f) := by
  have hcoeff := circleFourierCoeff_congr_ae hf.coeFn_toLp
  have hfun : circleFourierCutFunction s (hf.toLp f) = n06CircleFourierCut s f := by
    unfold circleFourierCutFunction n06CircleFourierCut
    rw [hcoeff]
  unfold circleFourierJetCutFun
  apply MemLp.toLp_congr
  exact Eventually.of_forall (fun θ =>
    congrFun (congrArg (iteratedDeriv j) hfun.symm) θ)

theorem n06CircleFourierCut_error_tendsto {f : ℝ → ℝ} (hf : MemLp f 2 angleMeasure) :
    Tendsto (fun N => ∫ θ, (n06CircleFourierCut (n06FourierCutoff N) f θ - f θ) ^ 2
      ∂angleMeasure) atTop (𝓝 0) := by
  let hP (N : ℕ) : MemLp (n06CircleFourierCut (n06FourierCutoff N) f) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous
      (n06CircleFourierCut_contDiff (n06FourierCutoff N) f).continuous
  have hclass (N : ℕ) : (hP N).toLp (n06CircleFourierCut (n06FourierCutoff N) f) =
      circleFourierJetCutFun (n06FourierCutoff N) 0 (hf.toLp f) := by
    simpa only [iteratedDeriv_zero] using n06CircleFourierCut_toLp hf (n06FourierCutoff N) 0
  apply (r11b_tendsto_toLp_iff_integral_sq_sub hP hf).mp
  simpa only [hclass] using n06_circleFourierCut_tendsto (hf.toLp f)

theorem n06CircleFourierCut_error_sq_le {f : ℝ → ℝ} (hf : MemLp f 2 angleMeasure)
    (s : Finset ℤ) (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) :
    (∫ θ, (n06CircleFourierCut s f θ - f θ) ^ 2 ∂angleMeasure) ≤
      4 * ∫ θ, f θ ^ 2 ∂angleMeasure := by
  let hP : MemLp (n06CircleFourierCut s f) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous (n06CircleFourierCut_contDiff s f).continuous
  have hclass : hP.toLp (n06CircleFourierCut s f) =
      circleFourierJetCutFun s 0 (hf.toLp f) := by
    simpa only [iteratedDeriv_zero] using n06CircleFourierCut_toLp hf s 0
  have hnorm : ‖hP.toLp (n06CircleFourierCut s f) - hf.toLp f‖ ≤ 2 * ‖hf.toLp f‖ := by
    calc
      _ ≤ ‖hP.toLp (n06CircleFourierCut s f)‖ + ‖hf.toLp f‖ := norm_sub_le _ _
      _ ≤ 2 * ‖hf.toLp f‖ := by
        rw [hclass]
        linarith only [n06_circleFourierCut_norm_le s hs (hf.toLp f)]
  rw [← r11b_norm_toLp_sub_sq hP hf]
  calc
    _ ≤ (2 * ‖hf.toLp f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
    _ = _ := by rw [mul_pow, r11b_norm_toLp_sq]; norm_num

end ContinuousFlexibility.Statements
