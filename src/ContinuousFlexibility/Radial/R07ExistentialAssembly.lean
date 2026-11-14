module

public import ContinuousFlexibility.Radial.R07Assembly

/-!
# Assembling concrete per-band solutions

The ODE constructions may choose their solutions only at admissible
frequencies. Classical choice extends those actual witnesses to the total
function fields required by the public statement; unused frequencies carry
zero functions. The matching conclusion itself is unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem r07_exists_selectedTail_of_band_matching (T : MorseChainData)
    (family : (ℕ → ℝ) → ReferenceData) (constants sigma : ℕ → ℝ) (C c₀ : ℝ)
    (cut joinInner entry : Bool → ℕ → ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2)
    (hfamily : ∀ tau, (∀ n, 1 ≤ tau n ∧ tau n ≤ 2) →
      MorseChainRealization T tau (family tau) constants ∧
      MorseMassResistanceBounds T tau (family tau) constants)
    (hmatch : ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
      ∃ u v : ℝ → ℝ,
        R07MatchingGeometry T (family sigma) right n j (cut right n) (joinInner right n)
          (entry right n) u v ∧
        c₀ * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine
            (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) u)
            (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) v)) :
    R07Statement := by
  classical
  let Match (right : Bool) (n j : ℕ) (uv : (ℝ → ℝ) × (ℝ → ℝ)) : Prop :=
    R07MatchingGeometry T (family sigma) right n j (cut right n) (joinInner right n)
      (entry right n) uv.1 uv.2 ∧
    c₀ * exp (-(n : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) uv.1)
        (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n)) uv.2)
  have hexists (right : Bool) (n j : ℕ)
      (h : 2 ≤ j ∧ Even j ∧ radialFrequencyBand T C n j) : ∃ uv, Match right n j uv := by
    obtain ⟨u, v, hG, hA⟩ := hmatch right n j h.1 h.2.1 h.2.2
    exact ⟨(u, v), hG, hA⟩
  let solution (right : Bool) (n j : ℕ) : (ℝ → ℝ) × (ℝ → ℝ) :=
    if h : 2 ≤ j ∧ Even j ∧ radialFrequencyBand T C n j
    then Classical.choose (hexists right n j h) else (0, 0)
  have hsolution (right : Bool) (n j : ℕ) (hj : 2 ≤ j) (heven : Even j)
      (hband : radialFrequencyBand T C n j) : Match right n j (solution right n j) := by
    dsimp only [solution]
    rw [dif_pos ⟨hj, heven, hband⟩]
    exact Classical.choose_spec (hexists right n j ⟨hj, heven, hband⟩)
  refine ⟨r07SelectedTailData T family constants sigma C c₀ cut joinInner entry
    (fun right n j => (solution right n j).1) (fun right n j => (solution right n j).2) hbands, ?_⟩
  apply r07_selectedTail_of_matching T family constants sigma C c₀ cut joinInner entry
    (fun right n j => (solution right n j).1) (fun right n j => (solution right n j).2)
    hbands hC hc₀ hsigma hfamily
  · exact fun right n j hj heven hband => (hsolution right n j hj heven hband).1
  · exact fun right n j hj heven hband => (hsolution right n j hj heven hband).2

end ContinuousFlexibility.Radial
