module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual bounded real multiplication on L2

A measurable real multiplier with an almost-everywhere bound gives a
continuous linear map on the actual L2 space. Its representatives,
operator norm, composition, and symmetry are proved explicitly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable (μ : Measure ℝ) {φ : ℝ → ℝ} {M : ℝ}

theorem l2Multiplier_memLp (hφ : AEStronglyMeasurable φ μ)
    (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) (f : Lp ℝ 2 μ) :
    MemLp (fun x => φ x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := M) (hφ.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hbound] with x hx
  change ‖φ x * f x‖ ≤ M * ‖f x‖
  rw [norm_mul, Real.norm_eq_abs (φ x)]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def l2MultiplierLinear (hφ : AEStronglyMeasurable φ μ)
    (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (l2Multiplier_memLp μ hφ hbound f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(l2Multiplier_memLp μ hφ hbound (f + g)).coeFn_toLp,
      (l2Multiplier_memLp μ hφ hbound f).coeFn_toLp,
      (l2Multiplier_memLp μ hφ hbound g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((l2Multiplier_memLp μ hφ hbound f).toLp _)
        ((l2Multiplier_memLp μ hφ hbound g).toLp _)] with x hfg hf hg hadd hout
    simp only [Pi.add_apply] at hadd hout
    rw [hfg, hout, hf, hg, hadd]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(l2Multiplier_memLp μ hφ hbound (c • f)).coeFn_toLp,
      (l2Multiplier_memLp μ hφ hbound f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((l2Multiplier_memLp μ hφ hbound f).toLp _)] with x hcf hf hsmul hout
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul hout
    simp only [RingHom.id_apply]
    rw [hcf, hout, hf, hsmul]
    ring

theorem l2MultiplierLinear_ae (hφ : AEStronglyMeasurable φ μ)
    (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) (f : Lp ℝ 2 μ) :
    l2MultiplierLinear μ hφ hbound f =ᵐ[μ] fun x => φ x * f x :=
  (l2Multiplier_memLp μ hφ hbound f).coeFn_toLp

def l2BoundedMultiplier (hφ : AEStronglyMeasurable φ μ)
    (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2MultiplierLinear μ hφ hbound).mkContinuous M (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [l2MultiplierLinear_ae μ hφ hbound f, hbound] with x hx hb
    rw [hx, norm_mul, Real.norm_eq_abs (φ x)]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem l2BoundedMultiplier_ae (hφ : AEStronglyMeasurable φ μ)
    (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) (f : Lp ℝ 2 μ) :
    l2BoundedMultiplier μ hφ hbound f =ᵐ[μ] fun x => φ x * f x :=
  l2MultiplierLinear_ae μ hφ hbound f

theorem norm_l2BoundedMultiplier_le (hφ : AEStronglyMeasurable φ μ)
    (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) :
    ‖l2BoundedMultiplier μ hφ hbound‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2BoundedMultiplier_ae μ hφ hbound f, hbound] with x hx hb
  rw [hx, norm_mul, Real.norm_eq_abs (φ x)]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem inner_l2BoundedMultiplier (hφ : AEStronglyMeasurable φ μ)
    (hbound : ∀ᵐ x ∂μ, |φ x| ≤ M) (f g : Lp ℝ 2 μ) :
    inner ℝ (l2BoundedMultiplier μ hφ hbound f) g =
      inner ℝ f (l2BoundedMultiplier μ hφ hbound g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2BoundedMultiplier_ae μ hφ hbound f,
    l2BoundedMultiplier_ae μ hφ hbound g] with x hf hg
  rw [Real.inner_apply, Real.inner_apply, hf, hg]
  ring

theorem l2BoundedMultiplier_comp
    {ψ : ℝ → ℝ} {N : ℝ} (hφ : AEStronglyMeasurable φ μ)
    (hψ : AEStronglyMeasurable ψ μ)
    (hφb : ∀ᵐ x ∂μ, |φ x| ≤ M) (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ N) :
    (l2BoundedMultiplier μ hφ hφb).comp (l2BoundedMultiplier μ hψ hψb) =
      l2BoundedMultiplier μ (M := M * N) (hφ.mul hψ) (by
        filter_upwards [hφb, hψb] with x hx hy
        change |φ x * ψ x| ≤ M * N
        rw [abs_mul]
        exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)) := by
  have hprod : ∀ᵐ x ∂μ, |φ x * ψ x| ≤ M * N := by
    filter_upwards [hφb, hψb] with x hx hy
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)
  ext f
  filter_upwards
    [l2BoundedMultiplier_ae μ hφ hφb (l2BoundedMultiplier μ hψ hψb f),
      l2BoundedMultiplier_ae μ hψ hψb f,
      l2BoundedMultiplier_ae μ (hφ.mul hψ) hprod f] with x houter hinner hproduct
  change l2BoundedMultiplier μ hφ hφb (l2BoundedMultiplier μ hψ hψb f) x = _
  rw [houter, hinner, hproduct]
  simp only [Pi.mul_apply]
  ring

end ContinuousFlexibility.Analysis
