import ContinuousFlexibility.Radial.R07LaterSelection

/-!
# Exact assembly of the selected radial tail

The matching construction naturally produces one solution for a side,
band, and frequency. The public R07 data are indexed only by side and
frequency. Uniqueness of the frequency band removes the redundant index.
The geometric record below consists exactly of the non-angle clauses in
`IsSelectedTail`; the final theorem adds the angle bound and no extra
analytic hypothesis. Separate initial and later margins are combined by
their positive minimum.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

private theorem r07_band_exists (T : MorseChainData) (C : ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    {j : ℕ} (hj : 2 ≤ j) (heven : Even j) : ∃ n, radialFrequencyBand T C n j := by
  obtain ⟨n, hn, _⟩ := hbands j hj heven
  exact ⟨n, hn⟩

/-- The unique band of an admissible frequency. Values below two or at
odd frequencies are unused by the selected-tail statement. -/
def r07BandIndex (T : MorseChainData) (C : ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j) (j : ℕ) : ℕ := by
  classical
  exact if h : 2 ≤ j ∧ Even j then
    Classical.choose (r07_band_exists T C hbands h.1 h.2) else T.index

theorem r07BandIndex_spec (T : MorseChainData) (C : ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    {j : ℕ} (hj : 2 ≤ j) (heven : Even j) :
    radialFrequencyBand T C (r07BandIndex T C hbands j) j := by
  rw [r07BandIndex, dif_pos ⟨hj, heven⟩]
  exact Classical.choose_spec (r07_band_exists T C hbands hj heven)

theorem r07BandIndex_eq (T : MorseChainData) (C : ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j) (hn : radialFrequencyBand T C n j) :
    r07BandIndex T C hbands j = n := by
  obtain ⟨m, _, huniq⟩ := hbands j hj heven
  exact (huniq _ (r07BandIndex_spec T C hbands hj heven)).trans (huniq n hn).symm

/-- All matching clauses other than the angle estimate, with the exact
cut normalization and interval conventions of the frozen R07 statement. -/
structure R07MatchingGeometry (T : MorseChainData) (D : ReferenceData)
    (right : Bool) (n j : ℕ) (c join entry : ℝ) (u v : ℝ → ℝ) : Prop where
  cut_mem : c ∈ radialCore D
  entry_mem : entry ∈ radialCore D
  join_mem : join ∈ radialCore D
  join_positive : 0 < D.w join
  order : if right then c < join ∧ join < entry else entry < join ∧ join < c
  entry_eq : entry = T.radius right n (if right then T.leftX right n else T.rightX right n)
  initial : if n = T.index then
      (∃ scale : ℝ, 0 < scale ∧ D.w =ᶠ[𝓝 c] fun r => scale * r) ∧
        u c = 1 ∧ deriv u c = (if right then (j : ℝ) else -(j : ℝ)) / c
    else u c = 0 ∧ u join = 1 ∧ (if right then 0 < deriv u c else deriv u c < 0)
  profile_increasing : ∀ r ∈ radialOpenSpan c join, 0 < deriv D.w r
  cut_smooth : ContDiffAt ℝ ∞ u c
  entry_smooth : ContDiffAt ℝ ∞ u entry
  incoming_equation : RadialHomogeneousOn D j (uIcc c entry) u
  outgoing_natural : RadialNaturalTail D right j entry v

/-- Assemble the public data by looking up each frequency's unique band. -/
def r07SelectedTailData (T : MorseChainData) (family : (ℕ → ℝ) → ReferenceData)
    (constants sigma : ℕ → ℝ) (C c₀ : ℝ)
    (cut joinInner entry : Bool → ℕ → ℝ)
    (incoming outgoing : Bool → ℕ → ℕ → ℝ → ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j) : SelectedTailData where
  chain := T
  family := family
  constants := constants
  sigma := sigma
  Cstar := C
  c₀ := c₀
  cut := cut
  joinInner := joinInner
  entry := entry
  incoming := fun right j => incoming right (r07BandIndex T C hbands j) j
  outgoing := fun right j => outgoing right (r07BandIndex T C hbands j) j

/-- The per-band construction satisfies the exact `IsSelectedTail`
statement after the redundant band index is removed. -/
theorem r07_selectedTail_of_matching (T : MorseChainData)
    (family : (ℕ → ℝ) → ReferenceData) (constants sigma : ℕ → ℝ) (C c₀ : ℝ)
    (cut joinInner entry : Bool → ℕ → ℝ)
    (incoming outgoing : Bool → ℕ → ℕ → ℝ → ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2)
    (hfamily : ∀ tau, (∀ n, 1 ≤ tau n ∧ tau n ≤ 2) →
      MorseChainRealization T tau (family tau) constants ∧
      MorseMassResistanceBounds T tau (family tau) constants)
    (hgeometry : ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
      R07MatchingGeometry T (family sigma) right n j (cut right n) (joinInner right n)
        (entry right n) (incoming right n j) (outgoing right n j))
    (hangle : ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
      c₀ * exp (-(n : ℝ) ^ 2) ≤
        radialAngleSine
          (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n))
            (incoming right n j))
          (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n))
            (outgoing right n j))) :
    IsSelectedTail (r07SelectedTailData T family constants sigma C c₀ cut joinInner entry
      incoming outgoing hbands) := by
  refine ⟨hC, hc₀, hsigma, hfamily, hbands, ?_⟩
  intro right n j hj heven hband
  have hn := r07BandIndex_eq T C hbands hj heven hband
  have hg := hgeometry right n j hj heven hband
  have ha := hangle right n j hj heven hband
  dsimp only [r07SelectedTailData]
  rw [hn]
  exact ⟨hg.cut_mem, hg.entry_mem, hg.join_mem, hg.join_positive, hg.order, hg.entry_eq,
    hg.initial, hg.profile_increasing, hg.cut_smooth, hg.entry_smooth,
    hg.incoming_equation, hg.outgoing_natural, ha⟩

/-- A finite initial-band margin may be smaller than the tolerance used
to select all later heights. Taking their positive minimum preserves both
sets of angle inequalities and all other fields of the construction. -/
theorem r07_selectedTail_of_initial_later (T : MorseChainData)
    (family : (ℕ → ℝ) → ReferenceData) (constants sigma : ℕ → ℝ) (C cFirst cLater : ℝ)
    (cut joinInner entry : Bool → ℕ → ℝ)
    (incoming outgoing : Bool → ℕ → ℕ → ℝ → ℝ)
    (hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j)
    (hC : 0 < C) (hcFirst : 0 < cFirst) (hcLater : 0 < cLater)
    (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2)
    (hfamily : ∀ tau, (∀ n, 1 ≤ tau n ∧ tau n ≤ 2) →
      MorseChainRealization T tau (family tau) constants ∧
      MorseMassResistanceBounds T tau (family tau) constants)
    (hgeometry : ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
      R07MatchingGeometry T (family sigma) right n j (cut right n) (joinInner right n)
        (entry right n) (incoming right n j) (outgoing right n j))
    (hfirst : ∀ right j, 2 ≤ j → Even j → radialFrequencyBand T C T.index j →
      cFirst * exp (-(T.index : ℝ) ^ 2) ≤
        radialAngleSine
          (radialState (family sigma) j (entry right T.index) ((family sigma).w (joinInner right T.index))
            (incoming right T.index j))
          (radialState (family sigma) j (entry right T.index) ((family sigma).w (joinInner right T.index))
            (outgoing right T.index j)))
    (hlater : ∀ right n j, 2 ≤ j → Even j → T.index < n → radialFrequencyBand T C n j →
      cLater * exp (-(n : ℝ) ^ 2) ≤
        radialAngleSine
          (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n))
            (incoming right n j))
          (radialState (family sigma) j (entry right n) ((family sigma).w (joinInner right n))
            (outgoing right n j))) :
    IsSelectedTail (r07SelectedTailData T family constants sigma C (min cFirst cLater)
      cut joinInner entry incoming outgoing hbands) := by
  apply r07_selectedTail_of_matching T family constants sigma C (min cFirst cLater)
    cut joinInner entry incoming outgoing hbands hC (lt_min hcFirst hcLater) hsigma hfamily hgeometry
  intro right n j hj heven hband
  by_cases hn : n = T.index
  · subst n
    exact (mul_le_mul_of_nonneg_right (min_le_left cFirst cLater) (exp_pos _).le).trans
      (hfirst right j hj heven hband)
  · have hnle := hband.1
    have hnlt : T.index < n := by omega
    exact (mul_le_mul_of_nonneg_right (min_le_right cFirst cLater) (exp_pos _).le).trans
      (hlater right n j hj heven hnlt hband)

end ContinuousFlexibility.Radial
