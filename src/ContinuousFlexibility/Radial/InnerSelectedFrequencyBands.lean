module

public import ContinuousFlexibility.Radial.InnerSelectedPhysicalChain

/-!
# Every positive even frequency has one actual inner depth

The selected tail supplies the unique frequency-band index. Its lower
index condition expresses that index uniquely as N+K, including K=0.
The chosen depth therefore uses the same all-band physical chain and the
same selected outer joins, with no weight exponent or analytic premise.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

include P

/-- Reindex the unique selected band by the nonnegative number of
retained Morse cells on each side. -/
theorem frequencyBand_depth_existsUnique (j : ℕ) (hj : 2 ≤ j) (hEven : Even j) :
    ∃! K : ℕ, radialFrequencyBand S.chain S.Cstar (S.chain.index + K) j := by
  obtain ⟨n, hn, hunique⟩ := P.selected.2.2.2.2.1 j hj hEven
  have hindex : S.chain.index ≤ n := hn.1
  have he : S.chain.index + (n - S.chain.index) = n := by omega
  refine ⟨n - S.chain.index, ?_, ?_⟩
  · simpa only [he] using hn
  · intro K hK
    have hk : S.chain.index + K = n := hunique _ hK
    omega

/-- All positive even frequencies, parameterized by j=2q, are covered. -/
theorem evenFrequencyBand_existsUnique (q : ℕ) (hq : 1 ≤ q) :
    ∃! K : ℕ, radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q) := by
  apply P.frequencyBand_depth_existsUnique (2 * q) (by omega)
  exact ⟨q, by omega⟩

/-- The canonical depth comes from the same selected frequency bands. -/
def selectedDepth (q : ℕ) (hq : 1 ≤ q) : ℕ :=
  Classical.choose (P.evenFrequencyBand_existsUnique q hq).exists

theorem selectedDepth_band (q : ℕ) (hq : 1 ≤ q) :
    radialFrequencyBand S.chain S.Cstar
      (S.chain.index + P.selectedDepth q hq) (2 * q) :=
  Classical.choose_spec (P.evenFrequencyBand_existsUnique q hq).exists

theorem selectedDepth_eq (q : ℕ) (hq : 1 ≤ q) {K : ℕ}
    (hK : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q)) :
    P.selectedDepth q hq = K := by
  obtain ⟨k, _, hunique⟩ := P.evenFrequencyBand_existsUnique q hq
  exact (hunique _ (P.selectedDepth_band q hq)).trans (hunique K hK).symm

theorem selectedDepth_zero_iff (q : ℕ) (hq : 1 ≤ q) :
    P.selectedDepth q hq = 0 ↔ radialFrequencyBand S.chain S.Cstar S.chain.index (2 * q) := by
  constructor
  · intro hzero
    have hb := P.selectedDepth_band q hq
    simpa only [hzero, Nat.add_zero] using hb
  · intro hb
    apply P.selectedDepth_eq q hq
    simpa only [Nat.add_zero] using hb

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
