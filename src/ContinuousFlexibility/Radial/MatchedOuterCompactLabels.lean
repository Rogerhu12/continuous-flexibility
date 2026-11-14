module

public import ContinuousFlexibility.Radial.OuterGreenAssembly
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# The actual localizers and solutions on a fixed compact outer core

Compact local finiteness bounds every label of a nonzero original
localizer on the core. The bounds on the supplied fundamental pair come
from its already proved continuity. No spatial envelope is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- All actual localizers meeting a compact subset of the core have a
common action bound, including localizers crossing its endpoints. -/
theorem exists_reference_compact_localizer_action_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ m r, r ∈ K → D.localizer m r ≠ 0 →
      radialS (D.cellIndex m) ≤ T := by
  obtain ⟨C, hC⟩ := hD
  have hfinite : Set.Finite {m | (D.cells m ∩ K).Nonempty} :=
    hC.2.2.2.2.2.1 K hK hcore
  obtain ⟨T, hT⟩ := (hfinite.image (fun m => radialS (D.cellIndex m))).bddAbove
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  intro m r hr hlocal
  have hcell : r ∈ D.cells m := hC.2.1.2.2.1 m hlocal
  exact (hT ⟨m, ⟨r, hcell, hr⟩, rfl⟩).trans (le_max_left _ _)

/-- The same full fundamental pair is bounded on its actual compact core. -/
theorem OuterFundamentalStatePair.exists_compact_pair_bound
    {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (hcb : c < b) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x ∈ Icc a c, |H.U x| ≤ K) ∧
      (∀ x ∈ Icc a c, |H.V x| ≤ K) := by
  obtain ⟨KU, hKU⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (H.continuousOn_core hcb).1
  obtain ⟨KV, hKV⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (H.continuousOn_core hcb).2
  refine ⟨max (max KU KV) 0 + 1, by positivity, ?_, ?_⟩
  · intro x hx
    have h := hKU x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (by linarith only [le_max_left KU KV, le_max_left (max KU KV) 0])
  · intro x hx
    have h := hKV x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (by linarith only [le_max_right KU KV, le_max_left (max KU KV) 0])

/-- Applying the actual radial coordinate to a compact interval does not
require a localizer's whole support to lie in that interval. -/
theorem exists_reference_compact_coordinate_action_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {a c : ℝ} (r : ℝ → ℝ)
    (hr : Continuous r) (hcore : ∀ x ∈ Icc a c, r x ∈ radialCore D) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ m x, x ∈ Icc a c →
      D.localizer m (r x) ≠ 0 → radialS (D.cellIndex m) ≤ T := by
  obtain ⟨T, hT, hbound⟩ := exists_reference_compact_localizer_action_bound
    hD (isCompact_Icc.image hr) (by rintro _ ⟨x, hx, rfl⟩; exact hcore x hx)
  exact ⟨T, hT, fun m x hx hlocal => hbound m (r x) ⟨x, hx, rfl⟩ hlocal⟩

end ContinuousFlexibility.Radial
