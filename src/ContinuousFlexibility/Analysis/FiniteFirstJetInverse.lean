import ContinuousFlexibility.Analysis.FiniteFullJetBoundary

/-!
# First jets of the same local inverse maps

The inverse points are fixed by the genuine left-inverse germs. The
derivative equality uses one left and one right inverse of the common
forward derivative; no inverse is chosen by the proof.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem finiteFullJetMatch_one_of_value_fderiv
    {x : E} {f g : E → F}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hvalue : f x = g x) (hderiv : fderiv ℝ f x = fderiv ℝ g x) :
    FiniteFullJetMatch 1 x f g := by
  refine ⟨hf, hg, ?_⟩
  intro k hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · ext v
    simpa only [iteratedFDeriv_zero_apply] using hvalue
  · ext v
    simpa only [iteratedFDeriv_one_apply] using
      congrArg (fun L : E →L[ℝ] F => L (v 0)) hderiv

/-- Both the inner map and the outer map may have matching finite jets,
provided the outer comparison is at the actual common inner value. -/
theorem FiniteFullJetMatch.comp_match
    {n : ℕ} {x : E} {f g : E → F} {H K : F → G}
    (h : FiniteFullJetMatch n x f g)
    (houter : FiniteFullJetMatch n (f x) H K) :
    FiniteFullJetMatch n x (H ∘ f) (K ∘ g) := by
  have houtg : FiniteFullJetMatch n (g x) H K := h.value ▸ houter
  exact (h.comp houter.left_smooth).trans (houtg.precomp h.right_smooth)

theorem FiniteFullJetMatch.div
    {n : ℕ} {x : E} {f g u v : E → ℝ}
    (h : FiniteFullJetMatch n x f g) (k : FiniteFullJetMatch n x u v)
    (hu : u x ≠ 0) :
    FiniteFullJetMatch n x (fun y => f y / u y) (fun y => g y / v y) := by
  have hquot : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.1 / p.2) (f x, u x) :=
    contDiffAt_fst.div contDiffAt_snd hu
  simpa only [Function.comp_def] using (h.prodMk k).comp hquot

/-- The two inverse maps are compared at the actual common image of
the forward point. All three germs concern the displayed maps. -/
theorem finiteFullJetMatch_one_inverse_of_germs
    {x : E} {f₁ f₂ : E → F} {g₁ g₂ : F → E}
    (h : FiniteFullJetMatch 1 x f₁ f₂)
    (hg₁ : ContDiffAt ℝ ∞ g₁ (f₁ x))
    (hg₂ : ContDiffAt ℝ ∞ g₂ (f₁ x))
    (hleft₁ : g₁ ∘ f₁ =ᶠ[𝓝 x] (id : E → E))
    (hleft₂ : g₂ ∘ f₂ =ᶠ[𝓝 x] (id : E → E))
    (hright₂ : f₂ ∘ g₂ =ᶠ[𝓝 (f₁ x)] (id : F → F)) :
    FiniteFullJetMatch 1 (f₁ x) g₁ g₂ := by
  have hv₁ : g₁ (f₁ x) = x := hleft₁.eq_of_nhds
  have hv₂ : g₂ (f₁ x) = x :=
    (congrArg g₂ h.value).trans hleft₂.eq_of_nhds
  have hdf : fderiv ℝ f₁ x = fderiv ℝ f₂ x := h.fderiv.value
  have hfd₂ : DifferentiableAt ℝ f₂ (g₂ (f₁ x)) := by
    rw [hv₂]
    exact h.right_smooth.differentiableAt (by simp)
  let A : E →L[ℝ] F := fderiv ℝ f₁ x
  let L₁ : F →L[ℝ] E := fderiv ℝ g₁ (f₁ x)
  let L₂ : F →L[ℝ] E := fderiv ℝ g₂ (f₁ x)
  have hL : L₁.comp A = ContinuousLinearMap.id ℝ E := by
    calc
      _ = fderiv ℝ (g₁ ∘ f₁) x :=
        (fderiv_comp x (hg₁.differentiableAt (by simp))
          (h.left_smooth.differentiableAt (by simp))).symm
      _ = fderiv ℝ (id : E → E) x := hleft₁.fderiv_eq
      _ = _ := by rw [fderiv_id]
  have hR : A.comp L₂ = ContinuousLinearMap.id ℝ F := by
    calc
      _ = (fderiv ℝ f₂ (g₂ (f₁ x))).comp L₂ := by rw [hv₂, ← hdf]
      _ = fderiv ℝ (f₂ ∘ g₂) (f₁ x) :=
        (fderiv_comp (f₁ x) hfd₂ (hg₂.differentiableAt (by simp))).symm
      _ = fderiv ℝ (id : F → F) (f₁ x) := hright₂.fderiv_eq
      _ = _ := by rw [fderiv_id]
  have he : L₁ = L₂ := by
    apply ContinuousLinearMap.ext
    intro v
    have hRv : A (L₂ v) = v := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun L : F →L[ℝ] F => L v) hR
    have hLv : L₁ (A (L₂ v)) = L₂ v := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun L : E →L[ℝ] E => L (L₂ v)) hL
    exact (congrArg L₁ hRv.symm).trans hLv
  exact finiteFullJetMatch_one_of_value_fderiv hg₁ hg₂ (hv₁.trans hv₂.symm) he

end ContinuousFlexibility.Analysis
