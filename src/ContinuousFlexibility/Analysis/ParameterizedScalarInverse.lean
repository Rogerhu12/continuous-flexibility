module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Joint smoothness of the actual scalar inverse

The implicit equation is F(p, theta) = y. Its angular differential is
an invertible scalar map. The implicit function theorem gives a local
smooth solution, and strict monotonicity identifies that solution with
any supplied actual right inverse. No parameter continuity or
differentiability of the inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

private theorem isInvertible_real_toSpanSingleton {d : ℝ} (hd : d ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
  · ext x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      ContinuousLinearMap.id_apply]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  · ext x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      ContinuousLinearMap.id_apply]
    rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]

/-- A jointly smooth scalar family with positive angular derivative
has a jointly smooth actual right inverse. This applies to the true
parameterized inverse flow, without any assumed regularity of its choice. -/
theorem contDiff_parameterized_scalar_rightInverse
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F G : P × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (hright : ∀ z : P × ℝ, F (z.1, G z) = z.2) :
    ContDiff ℝ ∞ G := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  let H : (P × ℝ) × ℝ → ℝ := fun z => F (z.1.1, z.2) - z.1.2
  have hH : ContDiff ℝ ∞ H :=
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd
  let d : ℝ := deriv (fun θ => F (q.1, θ)) (G q)
  have hd : d ≠ 0 := (hpositive (q.1, G q)).ne'
  have ha : HasDerivAt (fun θ => F (q.1, θ)) d (G q) :=
    (differentiableAt_of_deriv_ne_zero hd).hasDerivAt
  have hs : HasFDerivAt (fun θ => H (q, θ))
      (ContinuousLinearMap.toSpanSingleton ℝ d) (G q) := by
    simpa only [H] using (ha.sub_const q.2).hasFDerivAt
  have hp : HasFDerivAt (fun θ => H (q, θ))
      ((fderiv ℝ H (q, G q)).comp (ContinuousLinearMap.inr ℝ (P × ℝ) ℝ)) (G q) := by
    have hh := (hH.differentiable (by simp) (q, G q)).hasFDerivAt.comp (G q)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q (G q))
    have he : H ∘ Prod.mk q = (fun θ : ℝ => H (q, θ)) := by
      funext θ
      exact Function.comp_apply
    rw [he] at hh
    exact hh
  have hi : ((fderiv ℝ H (q, G q)).comp
      (ContinuousLinearMap.inr ℝ (P × ℝ) ℝ)).IsInvertible := by
    rw [hp.unique hs]
    exact isInvertible_real_toSpanSingleton hd
  have hc : ContDiffAt ℝ ∞ H (q, G q) := hH.contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ : P × ℝ → ℝ := hc.implicitFunction hn hi
  have hψ : ContDiffAt ℝ ∞ ψ q := hc.contDiffAt_implicitFunction hn hi
  have hsol : ∀ᶠ z in 𝓝 q, H (z, ψ z) = H (q, G q) :=
    hc.eventually_apply_implicitFunction hn hi
  have hzero : H (q, G q) = 0 := by
    dsimp only [H]
    rw [hright q, sub_self]
  have heq : G =ᶠ[𝓝 q] ψ := by
    filter_upwards [hsol] with z hz
    rw [hzero] at hz
    change F (z.1, ψ z) - z.2 = 0 at hz
    apply (strictMono_of_deriv_pos (f := fun θ : ℝ => F (z.1, θ))
      (fun θ => hpositive (z.1, θ))).injective
    exact (hright z).trans (sub_eq_zero.mp hz).symm
  exact hψ.congr_of_eventuallyEq heq

end ContinuousFlexibility.Analysis
