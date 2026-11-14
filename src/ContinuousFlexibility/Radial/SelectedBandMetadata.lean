module

public import ContinuousFlexibility.Radial.SelectedFixedBandAssembly

/-!
# Selected-tail assembly retaining solution metadata

The existing selected-tail record is used without a second representation.
The existential conclusion retains its chosen incoming and outgoing
families, so callers can recover the prescribed chain, entries and Cstar.
An index-dependent angle bound and an arbitrary proved property of each
actual pair of solutions are retained along with IsSelectedTail.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem exists_r10a_selected_fixed_data_with (T : MorseChainData)
    (family : (ℕ → ℝ) → ReferenceData) (constants sigma : ℕ → ℝ) (C c₀ : ℝ)
    (cut joinInner entry : Bool → ℕ → ℝ) (margin : ℕ → ℝ)
    (Payload : Bool → ℕ → ℕ → (ℝ → ℝ) → (ℝ → ℝ) → Prop)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hmargin : ∀ n, c₀ ≤ margin n)
    (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2)
    (hfamily : ∀ tau, (∀ n, 1 ≤ tau n ∧ tau n ≤ 2) →
      MorseChainRealization T tau (family tau) constants ∧
        MorseMassResistanceBounds T tau (family tau) constants)
    (hmatch : ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
      ∃ u v : ℝ → ℝ,
        R07MatchingGeometry T (family sigma) right n j
          (cut right n) (joinInner right n) (entry right n) u v ∧
        margin n * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine
            (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) u)
            (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) v) ∧
        Payload right n j u v) :
    ∃ incoming outgoing : Bool → ℕ → ℕ → ℝ → ℝ,
      let S := r07SelectedTailData T family constants sigma C c₀ cut joinInner entry
        incoming outgoing hbands
      IsSelectedTail S ∧
      (∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
        margin n * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine
            (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n))
              (S.incoming right j))
            (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n))
              (S.outgoing right j))) ∧
      ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
        Payload right n j (S.incoming right j) (S.outgoing right j) := by
  classical
  let Match (right : Bool) (n j : ℕ) (uv : (ℝ → ℝ) × (ℝ → ℝ)) : Prop :=
    R07MatchingGeometry T (family sigma) right n j
      (cut right n) (joinInner right n) (entry right n) uv.1 uv.2 ∧
    margin n * exp (-(n : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) uv.1)
        (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) uv.2) ∧
    Payload right n j uv.1 uv.2
  have hexists (right : Bool) (n j : ℕ)
      (h : 2 ≤ j ∧ Even j ∧ radialFrequencyBand T C n j) : ∃ uv, Match right n j uv := by
    obtain ⟨u, v, hG, hA, hP⟩ := hmatch right n j h.1 h.2.1 h.2.2
    exact ⟨(u, v), hG, hA, hP⟩
  let solution (right : Bool) (n j : ℕ) : (ℝ → ℝ) × (ℝ → ℝ) :=
    if h : 2 ≤ j ∧ Even j ∧ radialFrequencyBand T C n j
    then Classical.choose (hexists right n j h) else (0, 0)
  have hsolution (right : Bool) (n j : ℕ) (hj : 2 ≤ j) (heven : Even j)
      (hband : radialFrequencyBand T C n j) : Match right n j (solution right n j) := by
    dsimp only [solution]
    rw [dif_pos ⟨hj, heven, hband⟩]
    exact Classical.choose_spec (hexists right n j ⟨hj, heven, hband⟩)
  refine ⟨(fun right n j => (solution right n j).1),
    (fun right n j => (solution right n j).2), ?_, ?_, ?_⟩
  · apply r07_selectedTail_of_matching T family constants sigma C c₀ cut joinInner entry
      (fun right n j => (solution right n j).1)
      (fun right n j => (solution right n j).2)
      hbands hC hc₀ hsigma hfamily
    · exact fun right n j hj heven hband => (hsolution right n j hj heven hband).1
    · intro right n j hj heven hband
      exact (mul_le_mul_of_nonneg_right (hmargin n) (exp_pos _).le).trans
        (hsolution right n j hj heven hband).2.1
  · intro right n j hj heven hband
    have hn := r07BandIndex_eq T C hbands hj heven hband
    dsimp only [r07SelectedTailData]
    rw [hn]
    exact (hsolution right n j hj heven hband).2.1
  · intro right n j hj heven hband
    have hn := r07BandIndex_eq T C hbands hj heven hband
    dsimp only [r07SelectedTailData]
    rw [hn]
    exact (hsolution right n j hj heven hband).2.2

end ContinuousFlexibility.Radial
