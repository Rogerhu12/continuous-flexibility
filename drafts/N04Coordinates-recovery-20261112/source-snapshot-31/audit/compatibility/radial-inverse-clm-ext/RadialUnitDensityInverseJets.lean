import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope
import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Local inverse jets from the actual radial unit density

A nonzero radial derivative has constant sign near the point. Its
absolute value is fixed by the unit density, so positive forward jets
are controlled by the height and physical profile. The first inverse
derivative is their reciprocal product. The finite inverse polynomial
then uses only those actual data, without a bound on the inverse value.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

private theorem radialUnit_abs_jet_of_abs_germ
    {f g : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x) (hne : f x ≠ 0)
    (he : (fun t => |f t|) =ᶠ[𝓝 x] g) (n : ℕ) :
    |iteratedDeriv n f x| = |iteratedDeriv n g x| := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hn : ∀ᶠ t in 𝓝 x, f t < 0 := hf.eventually (Iio_mem_nhds hneg)
    have hfg : f =ᶠ[𝓝 x] (fun t => -g t) := by
      filter_upwards [he, hn] with t het hnt
      rw [abs_of_neg hnt] at het
      linarith only [het]
    rw [hfg.iteratedDeriv_eq n, iteratedDeriv_fun_neg, abs_neg]
  · have hp : ∀ᶠ t in 𝓝 x, 0 < f t := hf.eventually (Ioi_mem_nhds hpos)
    have hfg : f =ᶠ[𝓝 x] g := by
      filter_upwards [he, hp] with t het hpt
      simpa only [abs_of_pos hpt] using het
    rw [hfg.iteratedDeriv_eq n]

private theorem radialUnit_scalar_normalization
    {h w j : ℝ} (he : h ^ 2 * w * |j| = 1) :
    j ≠ 0 ∧ |j|⁻¹ = h ^ 2 * w ∧ |j| = h ^ (-2 : ℝ) * w⁻¹ := by
  have hj : j ≠ 0 := by
    intro hj
    rw [hj, abs_zero, mul_zero] at he
    exact zero_ne_one he
  have hi : |j|⁻¹ = h ^ 2 * w := inv_eq_of_mul_eq_one_left he
  refine ⟨hj, hi, ?_⟩
  calc
    |j| = (h ^ 2 * w)⁻¹ := by
      have hi' := congrArg (fun t : ℝ => t⁻¹) hi
      simpa only [inv_inv] using hi'
    _ = (h ^ 2)⁻¹ * w⁻¹ := by rw [mul_inv_rev, mul_comm]
    _ = h ^ (-2 : ℝ) * w⁻¹ := by
      simp only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]

/-- Constants precede all fields and the point. The inverse is a genuine
local inverse; the unit normalization and the height/profile jets are
the quantitative inputs. No zeroth inverse-coordinate bound is needed. -/
theorem radialUnitDensity_inverse_finiteJet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ {M : ℝ}, 1 ≤ M →
      ∀ Y χ H w : ℝ → ℝ, ∀ x : ℝ,
        ContDiffAt ℝ ∞ Y (χ x) → ContDiffAt ℝ ∞ χ x →
        ContDiffAt ℝ ∞ H (χ x) → ContDiffAt ℝ ∞ w (χ x) →
        0 < H (χ x) → 0 < w (χ x) →
        Y ∘ χ =ᶠ[𝓝 x] (id : ℝ → ℝ) →
        (∀ᶠ r in 𝓝 (χ x), H r ^ 2 * w r * |deriv Y r| = 1) →
        H (χ x) ^ 2 ≤ M → w (χ x) ≤ M →
        (∀ k, k ≤ N → |iteratedDeriv k (fun r => H r ^ (-2 : ℝ)) (χ x)| ≤ M) →
        (∀ k, k ≤ N → |iteratedDeriv k (fun r => (w r)⁻¹) (χ x)| ≤ M) →
        |iteratedDeriv (N + 1) χ x| ≤ C * M ^ d := by
  obtain ⟨CP, hCP, hprod⟩ := referencePotential_product_envelope N
  obtain ⟨CI, hCI, d, hinverse⟩ :=
    exists_nonlinearInverse_finiteJet_polynomial_envelope (E := ℝ) (F := ℝ) N
  let A : ℝ := 1 + CP
  have hA : 1 ≤ A := le_add_of_nonneg_right (zero_le_one.trans hCP)
  refine ⟨CI * A ^ d, one_le_mul_of_one_le_of_one_le hCI
    (one_le_pow₀ hA), 2 * d, ?_⟩
  intro M hM Y χ H w x hY hχ hH hw hHpos hwpos hright hunit hHbound hwbound hHjets hwjets
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hunitx := radialUnit_scalar_normalization hunit.self_of_nhds
  have hYprime : ContDiffAt ℝ ∞ (deriv Y) (χ x) := hY.derivWithin (by simp)
  have hjets (k : ℕ) (hk : k ≤ N) :
      |iteratedDeriv (k + 1) Y (χ x)| ≤ CP * M * M := by
    rw [iteratedDeriv_succ']
    have he : (fun r => |deriv Y r|) =ᶠ[𝓝 (χ x)]
        (fun r => H r ^ (-2 : ℝ) * (w r)⁻¹) := by
      filter_upwards [hunit] with r hr
      exact (radialUnit_scalar_normalization hr).2.2
    rw [radialUnit_abs_jet_of_abs_germ hYprime.continuousAt hunitx.1 he k]
    exact hprod hM0 hM0 (fun r => H r ^ (-2 : ℝ)) (fun r => (w r)⁻¹) (χ x)
      (hH.rpow_const_of_ne hHpos.ne') (hw.inv hwpos.ne') hHjets hwjets k hk
  have hchain : deriv Y (χ x) * deriv χ x = 1 :=
    (((hY.differentiableAt (by simp)).hasDerivAt.comp x
      (hχ.differentiableAt (by simp)).hasDerivAt).congr_of_eventuallyEq hright.symm).unique
        (hasDerivAt_id x)
  have habsprod : |deriv χ x| * |deriv Y (χ x)| = 1 := by
    rw [← abs_mul, mul_comm, hchain, abs_one]
  have hfirst : |deriv χ x| = H (χ x) ^ 2 * w (χ x) :=
    (inv_eq_of_mul_eq_one_left habsprod).symm.trans hunitx.2.1
  let V : ℝ := A * M ^ 2
  have hV : 1 ≤ V := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hM)
  have hrawV : CP * M * M ≤ V := by
    change CP * M * M ≤ (1 + CP) * M ^ 2
    nlinarith only [sq_nonneg M]
  have hfirstV : |deriv χ x| ≤ V := by
    rw [hfirst]
    calc
      H (χ x) ^ 2 * w (χ x) ≤ M * M :=
        mul_le_mul hHbound hwbound hwpos.le hM0
      _ = M ^ 2 := (pow_two M).symm
      _ ≤ A * M ^ 2 := le_mul_of_one_le_left (sq_nonneg M) hA
  have hL : (fderiv ℝ χ x).comp (fderiv ℝ Y (χ x)) =
      ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      fderiv_eq_deriv_mul]
    calc
      deriv χ x * (deriv Y (χ x) * v) = (deriv Y (χ x) * deriv χ x) * v := by ring
      _ = v := by rw [hchain, one_mul]
  have hLb : ‖fderiv ℝ χ x‖ ≤ V := by
    rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
    exact hfirstV
  have hraw (k : ℕ) (_hk : 1 ≤ k) (hkN : k ≤ N) :
      ‖iteratedFDeriv ℝ (k + 1) Y (χ x)‖ ≤ V := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      (hjets k hkN).trans hrawV
  have hb := hinverse hV Y χ x hY hχ hright (fderiv ℝ χ x) hL hLb hraw
  have hb' : |iteratedDeriv (N + 1) χ x| ≤ CI * V ^ d := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb
  apply hb'.trans_eq
  dsimp only [V]
  rw [mul_pow, ← pow_mul]
  ring

end ContinuousFlexibility.Analysis
