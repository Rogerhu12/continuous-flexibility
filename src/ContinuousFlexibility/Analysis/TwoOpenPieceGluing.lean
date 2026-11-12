import ContinuousFlexibility.Analysis.FirstDerivativeGluing

/-!
# First-derivative gluing across the omitted interface of two open pieces

The two pieces cover the ambient domain away from a common interface.
Openness and disjointness identify every relative boundary point with
that interface. This supplies the closure hypotheses required for genuine
first-derivative gluing, without any parametrization of the interface.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- Inside the covered domain, the closure of one open piece adds only
points of the omitted interface. -/
theorem openPieces_closure_subset_piece_union_interface
    {X : Type*} [TopologicalSpace X] {U s t Γ : Set X}
    (ht : IsOpen t) (hdisjoint : Disjoint s t) (hcover : s ∪ t = U \ Γ) :
    U ∩ closure s ⊆ s ∪ Γ := by
  have hst : s ⊆ tᶜ := fun _ hx hxt => Set.disjoint_left.mp hdisjoint hx hxt
  have hclosure : closure s ⊆ tᶜ := closure_minimal hst ht.isClosed_compl
  intro x hx
  by_cases hΓ : x ∈ Γ
  · exact Or.inr hΓ
  · have hpieces : x ∈ s ∪ t := by
      rw [hcover]
      exact ⟨hx.1, hΓ⟩
    rcases hpieces with hxs | hxt
    · exact Or.inl hxs
    · exact False.elim (hclosure hx.2 hxt)

/-- Matching actual first jets on the interface give a genuine C¹
function on the whole open ambient domain. -/
theorem contDiffOn_one_piecewise_two_open_domains
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U s t Γ : Set E} [DecidablePred (· ∈ s)]
    (hU : IsOpen U) (hs : IsOpen s) (ht : IsOpen t)
    (hdisjoint : Disjoint s t) (hcover : s ∪ t = U \ Γ)
    (hΓ : Γ ⊆ closure s ∩ closure t) {f g : E → F}
    (hf : ∀ x ∈ U ∩ closure s, ContDiffAt ℝ 1 f x)
    (hg : ∀ x ∈ U ∩ closure t, ContDiffAt ℝ 1 g x)
    (hmatch : ∀ x ∈ U ∩ Γ, f x = g x ∧ fderiv ℝ f x = fderiv ℝ g x) :
    ContDiffOn ℝ 1 (s.piecewise f g) U := by
  apply contDiffOn_one_piecewise_of_matching_jets hU hf
  · intro x hx
    have hxs : x ∉ s := by
      simpa only [hs.isClosed_compl.closure_eq] using hx.2
    by_cases hxΓ : x ∈ Γ
    · exact hg x ⟨hx.1, (hΓ hxΓ).2⟩
    · have hpieces : x ∈ s ∪ t := by
        rw [hcover]
        exact ⟨hx.1, hxΓ⟩
      rcases hpieces with hleft | hright
      · exact False.elim (hxs hleft)
      · exact hg x ⟨hx.1, subset_closure hright⟩
  · intro x hx
    have hfront : x ∈ closure s ∧ x ∉ s := by
      simpa only [hs.frontier_eq] using hx.2
    have hpieces := openPieces_closure_subset_piece_union_interface
      ht hdisjoint hcover ⟨hx.1, hfront.1⟩
    rcases hpieces with hleft | hinterface
    · exact False.elim (hfront.2 hleft)
    · exact hmatch x ⟨hx.1, hinterface⟩

end ContinuousFlexibility.Analysis
