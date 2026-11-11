import ContinuousFlexibility.Analysis.SeeleyWithinCylinderJets
import ContinuousFlexibility.Analysis.PeriodicScalarFlow
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Automatic bounds for periodic within-jets with radial support

Angular periodicity propagates through actual within-derivatives because
translation preserves the half-plane. Vanishing on an open radial tail
also propagates through derivatives, by germ congruence. Compactness of
one angular period therefore bounds every actual within-jet separately.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff Pointwise

set_option backward.isDefEq.respectTransparency false

private theorem angularTranslate_seeleyHalfPlane (T : ℝ) :
    ((0, T) : ℝ × ℝ) +ᵥ seeleyHalfPlane = seeleyHalfPlane := by
  apply Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨by simpa only [vadd_eq_add, Prod.fst_add, zero_add] using hq.1, mem_univ _⟩
  · intro p hp
    refine ⟨-((0, T) : ℝ × ℝ) + p, ?_, ?_⟩
    · exact ⟨by simpa only [Prod.fst_add, Prod.fst_neg, neg_zero, zero_add] using hp.1,
        mem_univ _⟩
    · simp only [vadd_eq_add, ← add_assoc, add_neg_cancel, zero_add]

/-- Periodicity of a function on the half-plane passes to its actual
within-partial; no differentiability is required outside the half-plane. -/
theorem seeleyWithinPartial_periodic
    {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T)
    (v : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r) :
    Function.Periodic (fun θ => seeleyWithinPartial v f (r, θ)) T := by
  intro θ
  have he : EqOn (fun q : ℝ × ℝ => f (q + (0, T))) f seeleyHalfPlane := by
    rintro ⟨s, t⟩ hp
    simpa only [Prod.mk_add_mk, add_zero] using hperiod s hp.1 t
  have hd := fderivWithin_comp_add_right (𝕜 := ℝ) (f := f)
    (s := seeleyHalfPlane) (x := (r, θ)) ((0, T) : ℝ × ℝ)
  rw [angularTranslate_seeleyHalfPlane,
    fderivWithin_congr' he (show (r, θ) ∈ seeleyHalfPlane from ⟨hr, mem_univ _⟩)] at hd
  simpa only [seeleyWithinPartial, Prod.mk_add_mk, add_zero] using
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v) hd.symm

private theorem iterate_seeleyWithinPartial_periodic
    {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T)
    (v : ℝ × ℝ) (n : ℕ) :
    ∀ r, 0 ≤ r → Function.Periodic
      (fun θ => ((seeleyWithinPartial v)^[n] f) (r, θ)) T := by
  induction n with
  | zero => exact hperiod
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact seeleyWithinPartial_periodic ih v

theorem seeleyWithinMixedJet_periodic
    {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T)
    (a b : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Function.Periodic (fun θ => seeleyWithinMixedJet f a b (r, θ)) T :=
  iterate_seeleyWithinPartial_periodic
    (iterate_seeleyWithinPartial_periodic hperiod (0, 1) b) (1, 0) a r hr

private theorem seeleyWithinPartial_zero_after
    {f : ℝ × ℝ → ℝ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → f p = 0) (v : ℝ × ℝ) :
    ∀ p, R < p.1 → seeleyWithinPartial v f p = 0 := by
  intro p hp
  have he : f =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
    exact hzero q hq
  unfold seeleyWithinPartial
  rw [he.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := seeleyHalfPlane)]
  simp only [fderivWithin_const_apply, ContinuousLinearMap.zero_apply]

private theorem iterate_seeleyWithinPartial_zero_after
    {f : ℝ × ℝ → ℝ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → f p = 0) (v : ℝ × ℝ) (n : ℕ) :
    ∀ p, R < p.1 → ((seeleyWithinPartial v)^[n] f) p = 0 := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact seeleyWithinPartial_zero_after ih v

theorem seeleyWithinMixedJet_zero_after
    {f : ℝ × ℝ → ℝ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → f p = 0) (a b : ℕ) :
    ∀ p, R < p.1 → seeleyWithinMixedJet f a b p = 0 :=
  iterate_seeleyWithinPartial_zero_after
    (iterate_seeleyWithinPartial_zero_after hzero (0, 1) b) (1, 0) a

/-- Periodicity and an actual open zero tail supply all bounds required
by Seeley's construction, using a compact radial interval and one period. -/
theorem seeleyWithinMixedJet_bounded_of_periodic_of_zero_after
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    {T R : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T)
    (hzero : ∀ p, R < p.1 → f p = 0) :
    ∀ a b, ∃ M : ℝ, ∀ p, 0 ≤ p.1 → ‖seeleyWithinMixedJet f a b p‖ ≤ M := by
  intro a b
  have hc : ContinuousOn (seeleyWithinMixedJet f a b) (Icc (0 : ℝ) R ×ˢ univ) :=
    (contDiffOn_seeleyWithinMixedJet hf a b).continuousOn.mono
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  obtain ⟨M, hM0, hM⟩ := exists_norm_bound_periodic_compact isCompact_Icc hT hc
    (fun r hr => seeleyWithinMixedJet_periodic hperiod a b r hr.1)
  refine ⟨M, ?_⟩
  intro p hp
  by_cases hR : p.1 ≤ R
  · exact hM p.1 ⟨hp, hR⟩ p.2
  · rw [seeleyWithinMixedJet_zero_after hzero a b p (lt_of_not_ge hR), norm_zero]
    exact hM0

end ContinuousFlexibility.Analysis
