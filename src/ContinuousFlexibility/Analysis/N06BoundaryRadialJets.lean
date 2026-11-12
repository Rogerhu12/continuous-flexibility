import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual boundary jets from smoothness on the boundary axis

The canonical coordinate contract gives ordinary smoothness at each point
of a closed physical strip. It does not give a globally smooth extension
of the chart. This module extracts the actual radial boundary derivatives
and proves that they are smooth functions of the angular parameter using
only that pointwise contract.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

/-- The finite-order linear chain rule needs smoothness only at the point.
The open neighborhood used in its proof may depend on the finite order. -/
theorem n06_iteratedFDeriv_compCLM_at
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} (g : G →L[ℝ] E) {x : G} (n : ℕ)
    (hf : ContDiffAt ℝ (n : ℕ∞ω) f (g x)) :
    iteratedFDeriv ℝ n (f ∘ g) x =
      (iteratedFDeriv ℝ n f (g x)).compContinuousLinearMap (fun _ => g) := by
  obtain ⟨U, hU, hx, hfU⟩ := hf.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ (g x)), Set.univ_inter] at hfU
  have hpre : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have he := g.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn
    hpre.uniqueDiffOn hx (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre hx,
    iteratedFDerivWithin_of_isOpen n hU hx] at he
  exact he

/-- A true radial slice derivative is the full derivative evaluated on the
radial coordinate vector. Only smoothness at the specified point is used. -/
theorem n06_radialBoundaryJet_eq_frechet
    {f : ℝ × ℝ → ℝ} {c θ : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f (c, θ)) :
    radialBoundaryJet f c n θ =
      iteratedFDeriv ℝ n f (c, θ) (fun _ => (1, 0)) := by
  let L : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inl ℝ ℝ ℝ
  let g : ℝ × ℝ → ℝ := fun p => f (p + (0, θ))
  have hpoint : L c + (0, θ) = (c, θ) := by
    simp only [L, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
  have hsource : ContDiffAt ℝ (n : ℕ∞ω) f (L c + (0, θ)) := by
    rw [hpoint]
    exact hf.of_le (by simp)
  have hg : ContDiffAt ℝ (n : ℕ∞ω) g (L c) :=
    hsource.comp (L c) (contDiffAt_id.add contDiffAt_const)
  have he := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℝ =>
      A (fun _ => 1)) (n06_iteratedFDeriv_compCLM_at L n hg)
  have hslice : g ∘ L = fun r => f (r, θ) := by
    funext r
    simp only [Function.comp_def, g, L, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [hslice] at he
  change radialBoundaryJet f c n θ =
    ((iteratedFDeriv ℝ n g (L c)).compContinuousLinearMap
      (fun _ => L)) (fun _ => 1) at he
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  have hshift : iteratedFDeriv ℝ n g (L c) = iteratedFDeriv ℝ n f (c, θ) := by
    change iteratedFDeriv ℝ n (fun p => f (p + (0, θ))) (L c) = _
    rw [iteratedFDeriv_comp_add_right, hpoint]
  rw [hshift] at he
  simpa only [L, ContinuousLinearMap.inl_apply] using he

/-- Every actual radial boundary jet is smooth in the angle, with no
global smooth extension assumed for the original field. -/
theorem n06_contDiff_radialBoundaryJet_of_axis
    {f : ℝ × ℝ → ℝ} {c : ℝ}
    (hf : ∀ θ, ContDiffAt ℝ ∞ f (c, θ)) (n : ℕ) :
    ContDiff ℝ ∞ (radialBoundaryJet f c n) := by
  have he : radialBoundaryJet f c n = fun θ =>
      iteratedFDeriv ℝ n f (c, θ) (fun _ => (1, 0)) := by
    funext θ
    exact n06_radialBoundaryJet_eq_frechet n (hf θ)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hjet : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ n f) (c, θ) :=
    (hf θ).iteratedFDeriv_right (by simp)
  have hslice : ContDiffAt ℝ ∞
      (fun η => iteratedFDeriv ℝ n f (c, η)) θ :=
    hjet.comp θ (contDiffAt_const.prodMk contDiffAt_id)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) ℝ
    (fun _ => (1, 0))).contDiff.contDiffAt.comp θ hslice

end ContinuousFlexibility.Analysis
