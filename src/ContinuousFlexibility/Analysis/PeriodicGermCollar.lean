module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform periodic collars from actual local neighborhoods

This generic compactness lemma is factored from RootUniformCollar.
It uses one compact angular period and does not depend on root charts,
Seeley extensions, or canonical coordinate data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

/-- A periodic property holding on a neighborhood of every point of the
zero-radius axis holds on one uniform two-sided radial collar. -/
theorem exists_uniform_periodic_collar_of_local
    {Q : ℝ × ℝ → Prop} {T : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r θ, Q (r, θ + T) ↔ Q (r, θ))
    (hlocal : ∀ θ : ℝ, ∀ᶠ p in 𝓝 (0, θ), Q p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r θ : ℝ, |r| < δ → Q (r, θ) := by
  let K : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ uIcc (0 : ℝ) T
  have hK : IsCompact K := isCompact_singleton.prod isCompact_uIcc
  have hsub : K ⊆ interior {p | Q p} := by
    rintro ⟨r, θ⟩ hp
    have hr : r = 0 := mem_singleton_iff.mp hp.1
    subst r
    exact mem_interior_iff_mem_nhds.mpr (hlocal θ)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open isOpen_interior hsub
  refine ⟨δ, hδ, ?_⟩
  intro r θ hr
  have hp : Function.Periodic (fun η : ℝ => Q (r, η)) T :=
    fun η => propext (hperiod r η)
  have hq : Q (r, θ) ∈ Set.range (fun η : ℝ => Q (r, η)) := ⟨θ, rfl⟩
  rw [← hp.image_uIcc hT 0] at hq
  obtain ⟨η, hη, heq⟩ := hq
  have hη' : η ∈ uIcc (0 : ℝ) T := by simpa only [zero_add] using hη
  have hm : (r, η) ∈ Metric.thickening δ K := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, η), ⟨(by simp : (0 : ℝ) ∈ ({0} : Set ℝ)), hη'⟩, ?_⟩
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
      max_eq_left (abs_nonneg r)] using hr
  have hQ : Q (r, η) := interior_subset (hthick hm)
  exact heq ▸ hQ

end ContinuousFlexibility.Analysis
