import ContinuousFlexibility.Analysis.CanonicalJetNormalization

/-!
# Why the qualitative canonical identities do not bound an arbitrary witness

The divided coefficients on a negative piece are absent from `N04PartA` and
`N04PartB`.  Replacing one of them by the unbounded angular coordinate preserves
both qualitative properties and destroys the zeroth-order uniform bound.

This is a counterexample to a *same-witness* completion lemma.  It is not a
counterexample to `N04bStatement → N04cStatement`: that existential statement
is allowed to construct different, quantitatively normalized canonical data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

private def angularCanonicalCoefficients : SymmetricCoefficients where
  a := fun p => p.2
  b := fun _ => 0
  c := fun _ => 0

/-- Change only the divided coefficients which the negative canonical operator
does not use.  Charts, height factors, potentials, and actual operators stay fixed. -/
def unboundedNegativeDividedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) : CanonicalData S :=
  { K with dividedDifference := fun z m =>
      if K.positive m = true then K.dividedDifference z m
      else angularCanonicalCoefficients }

theorem unboundedNegativeDividedCanonicalData_dividedDifference_of_positive
    {S : PhysicalSpacesData} (K : CanonicalData S) (z : AnnularState S × ℝ)
    {m : ℕ} (hm : K.positive m = true) :
    (unboundedNegativeDividedCanonicalData S K).dividedDifference z m =
      K.dividedDifference z m := by
  simp only [unboundedNegativeDividedCanonicalData, hm, if_true]

theorem n04PartA_unboundedNegativeDividedCanonicalData
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : N04PartA D S C K base ε) :
    N04PartA D S C (unboundedNegativeDividedCanonicalData S K) base ε := h

theorem n04PartB_unboundedNegativeDividedCanonicalData
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : N04PartB S C L K base ε) :
    N04PartB S C L (unboundedNegativeDividedCanonicalData S K) base ε := by
  obtain ⟨hcut, htrans, hop, hneg, hpos⟩ := h
  refine ⟨hcut, htrans, hop, hneg, ?_⟩
  intro z hz hs m hm p hp
  simpa only [unboundedNegativeDividedCanonicalData, hm, if_true]
    using hpos z hz hs m hm p hp

/-- Any nonempty negative piece obstructs the full bound for the modified data.
No regularity, positivity, or growth assumption on the material weights is used. -/
theorem not_canonicalJetBounds_unboundedNegativeDividedCanonicalData
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (K : CanonicalData S) {base loss : ℕ} {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) (hm : K.positive m = false) (hinterval : K.left m < K.right m) :
    ¬CanonicalJetBounds T S C (unboundedNegativeDividedCanonicalData S K) base loss ε := by
  intro hbound
  unfold CanonicalJetBounds at hbound
  obtain ⟨B, _, hB⟩ := hbound 0
  unfold CanonicalJetBoundAtOrder at hB
  obtain ⟨r, hlr, hrr⟩ := exists_between hinterval
  let Q : ℝ := B * T.E0 (T.sample (K.cell m)) ^ B
  have hz : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    change stateGrading S base (C.referenceState - C.referenceState) < ε ∧ |(0 : ℝ)| < ε
    constructor
    · simpa only [sub_self, map_zero] using hε
    · simpa only [abs_zero] using hε
  have hp : (r, |Q| + 1) ∈
      canonicalOpen S (unboundedNegativeDividedCanonicalData S K) m :=
    ⟨⟨hlr, hrr⟩, mem_univ _⟩
  have hb := hB (C.referenceState, 0) hz m (r, |Q| + 1) hp 0 0 (Nat.le_refl 0)
  simp only [mixedDerivative, iteratedDeriv_zero,
    unboundedNegativeDividedCanonicalData, hm, Bool.false_eq_true, if_false,
    angularCanonicalCoefficients, Nat.zero_add, sub_self, map_zero,
    abs_zero, add_zero, mul_one] at hb
  change |K.potential (C.referenceState, 0) m (r, |Q| + 1)| + ||Q| + 1| ≤ Q at hb
  have hangle : 0 ≤ |Q| + 1 := by linarith [abs_nonneg Q]
  rw [abs_of_nonneg hangle] at hb
  linarith [abs_nonneg (K.potential (C.referenceState, 0) m (r, |Q| + 1)), le_abs_self Q]

/-- Starting from any qualitative canonical witness, there is another witness
of exactly the same qualitative clauses for which the requested jet bound fails.
The negative piece supplied by the first cut pair is sufficient. -/
theorem exists_qualitativeCanonicalData_without_jetBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ K' : CanonicalData S,
      N04PartA D S C K' base ε ∧ N04PartB S C L K' base ε ∧
        ¬CanonicalJetBounds T S C K' base loss ε := by
  refine ⟨unboundedNegativeDividedCanonicalData S K,
    n04PartA_unboundedNegativeDividedCanonicalData hA,
    n04PartB_unboundedNegativeDividedCanonicalData hB, ?_⟩
  exact not_canonicalJetBounds_unboundedNegativeDividedCanonicalData K hε
    (K.cutPair 0).1 (hB.1 0).1 (hA.2.2.2.1 (K.cutPair 0).1).2.1

end ContinuousFlexibility.Analysis
