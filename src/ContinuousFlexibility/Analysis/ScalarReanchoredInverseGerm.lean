import ContinuousFlexibility.Analysis.ScalarEquationBoundaryContinuity

/-!
# Actual inverse germs under a change of initial label

A true scalar equation between increasing boundary lifts determines a
bijective initial-label map and the continuity of its chosen inverse.
Local equality of two forward families then identifies their actual
inverse values near the base point, using only the supplied right
inverse and injectivity. No inverse regularity is postulated for the
second family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem bijective_and_continuous_invFun_of_scalar_equation
    {F G H : ℝ → ℝ} (hF : Continuous F) (hFmono : StrictMono F)
    (hFonto : Function.Surjective F) (hG : Continuous G)
    (hGinj : Function.Injective G) (heq : ∀ x, G (H x) = F x) :
    Function.Bijective H ∧ Continuous (Function.invFun H) := by
  have hHinj : Function.Injective H := by
    intro x y hxy
    apply hFmono.injective
    rw [← heq x, ← heq y, hxy]
  have hHonto : Function.Surjective H := by
    intro y
    obtain ⟨x, hx⟩ := hFonto (G y)
    exact ⟨x, hGinj ((heq x).trans hx)⟩
  have hvalue (y : ℝ) : F (Function.invFun H y) = G y := by
    rw [← heq (Function.invFun H y), Function.rightInverse_invFun hHonto y]
  refine ⟨⟨hHinj, hHonto⟩, continuous_iff_continuousAt.mpr ?_⟩
  intro y
  have hy : Tendsto G (𝓝 y) (𝓝 (F (Function.invFun H y))) := by
    rw [hvalue]
    exact hG.tendsto y
  exact tendsto_of_injective_scalar_equation
    (F := fun _ : ℝ => F) (u := Function.invFun H) (y := G)
    (G := F) (θ := Function.invFun H y)
    (Eventually.of_forall (fun _ => hF))
    (Eventually.of_forall (fun _ => hFmono.injective))
    (Eventually.of_forall hvalue)
    (fun _ => tendsto_const_nhds) hy hFmono

/-- Agreement on an initial-label neighborhood determines the actual
inverse germ. The second family's inverse is merely `Function.invFun`;
its continuity is not an input. -/
theorem invFun_reanchored_eq_eventually
    {P : Type*} {l : Filter (P × ℝ)} {f g : P → ℝ → ℝ}
    {H : ℝ → ℝ} {J : P × ℝ → ℝ} {ι : ℝ} {V : Set ℝ}
    (hH : Function.Bijective H)
    (hHinv : ContinuousAt (Function.invFun H) (H ι))
    (hJ : Tendsto J l (𝓝 (H ι))) (hV : V ∈ 𝓝 ι)
    (heq : ∀ᶠ p in l, ∀ u ∈ V, g p.1 (H u) = f p.1 u)
    (hright : ∀ᶠ p in l, g p.1 (J p) = p.2)
    (hinj : ∀ᶠ p in l, Function.Injective (f p.1)) :
    ∀ᶠ p in l, H (Function.invFun (f p.1) p.2) = J p := by
  have hlimit : Tendsto (fun p => Function.invFun H (J p)) l (𝓝 ι) := by
    simpa only [Function.comp_def, Function.leftInverse_invFun hH.1 ι] using
      hHinv.tendsto.comp hJ
  filter_upwards [heq, hright, hinj, hlimit.eventually hV] with p hp hr hi hv
  have hHright := Function.rightInverse_invFun hH.2 (J p)
  have hmatch : g p.1 (J p) = f p.1 (Function.invFun H (J p)) := by
    simpa only [hHright] using hp (Function.invFun H (J p)) hv
  have hvalue : f p.1 (Function.invFun H (J p)) = p.2 := hmatch.symm.trans hr
  have hchosen : Function.invFun (f p.1) p.2 = Function.invFun H (J p) := by
    rw [← hvalue]
    exact Function.leftInverse_invFun hi _
  exact (congrArg H hchosen).trans hHright

end ContinuousFlexibility.Analysis
