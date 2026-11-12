import ContinuousFlexibility.Analysis.N01cCanonicalComponentEnumeration
import ContinuousFlexibility.Radial.R11aRetainedFamily

/-! # The canonical enumeration on the exact reference returned by R11a -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- Keep the actual control host on the same retained reference. All
coordinate and enumeration inputs come from the closed R11a constructor. -/
theorem SeedRetainedPair.n01c_component_enumeration
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length Cstar : ℝ}
    {requested : ℕ} (metadata : R10aSelectedMetadata Cstar requested S)
    (P : SeedRetainedPair S K q length) (Γ : ConnectedReferenceGeometry)
    (hq : 0 < q) (hΓ : Γ.Realizes) (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (host : N01aNegativeComponent Γ.reference → ℕ)
    (hhost : ∀ J, J.interval ⊆ Γ.reference.cells (host J)) :
    ∃ e : ℕ ≃ N01aNegativeComponent Γ.reference, ∃ B : ℝ, 0 < B ∧
      ∀ m, |(Γ.reference.cellIndex (host (e m)) : ℝ) - Γ.reference.cellIndex m| ≤ B := by
  have hreal := (metadata.selected.2.2.2.1 S.sigma metadata.selected.2.2.1).1
  have hseam (side : Bool) (n : ℕ) :
      S.entry side n = morseChainSeam S.chain side n := by
    simp only [metadata.entry, r07CellEntry, morseChainSeam]
  have hseams (side : Bool) (n : ℕ) (hn : S.chain.index ≤ n) :
      if side then morseChainSeam S.chain side S.chain.index ≤ morseChainSeam S.chain side n
      else morseChainSeam S.chain side n ≤ morseChainSeam S.chain side S.chain.index := by
    simpa only [hseam] using (metadata.retained_entries side n hn).2
  obtain ⟨e, N, _, hlabels, hindex, hcells, _, hleft, hright, _, ha, hb⟩ := hcoordinates
  have hindex' (m : ℕ) :
      Γ.reference.cellIndex m = max ((S.family S.sigma).cellIndex m) N := by
    simp only [hindex, hlabels]
  apply exists_n01c_canonical_component_enumeration hreal metadata.selected.2.2.1
    (P.toEntryPair metadata.selected metadata.first_two)
    (hseam false S.chain.index) (hseam true S.chain.index)
    hq hΓ.2.1 ha hb hw hseams hlabels N hindex' ?_ host hhost
  intro side m r hr hm
  have hr' : r ∈ radialTailInterval (S.family S.sigma) side (S.entry side S.chain.index) := by
    simpa only [hseam] using hr
  apply hcells m
  cases side
  · change e (P.pair.radiusL * r) ∈ (S.family S.sigma).cells m
    rw [← hleft r hr'.2.le, e.apply_symm_apply]
    exact hm
  · change e (P.pair.radiusR * r) ∈ (S.family S.sigma).cells m
    rw [← hright r hr'.1.le, e.apply_symm_apply]
    exact hm

end ContinuousFlexibility.Radial
