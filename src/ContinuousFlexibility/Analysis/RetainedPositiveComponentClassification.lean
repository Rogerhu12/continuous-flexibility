module

public import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapComponents
public import ContinuousFlexibility.Analysis.RetainedPositiveComponentInteriorEndpoints
public import ContinuousFlexibility.Analysis.PositiveComponentAdjacency

/-!
# Whole positive components of the same retained reference

Every positive component has a genuine negative neighbor on its left.
The actual negative-component classification identifies that neighbor
as central or as a retained Morse model. Except for the central right
root and the first left-tail right root, its right endpoint is exactly
the left endpoint of one of the positive Morse gaps already recognized.
The two exceptional left endpoints yield only finitely many components.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ContDiff

theorem retainedReference_positive_component_classification
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C)
    (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)) :
    (n04PositiveLeft i = centralRadius (sqrt centralOscillatorA) ∨
      n04PositiveLeft i = P.sideRadius false * S.chain.radius false S.chain.index
        (morseRightTurn (morseChainA S.chain S.chain.index)
          (morseChainB S.chain S.chain.index))) ∨
    ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
      n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
      n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n := by
  have hD : RadialProfileGeometry Γ.reference := hΓ.2.1.choose_spec.1
  have hf : Continuous (deriv Γ.reference.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hroot := retainedReference_positive_endpoints_interior
    P hS hband hq hΓ hw hcoordinates i false
  have hinterior : n04PositiveEndpoint i false ≠ Γ.reference.a := hroot.1.1.ne'
  obtain ⟨m, hm⟩ := n04PositiveEndpoint_exists_negative_neighbor hD hC i false hinterior
  simp only [n04PositiveEndpoint, Bool.false_eq_true, ↓reduceIte] at hm
  have hcomponent : NegativeRadialComponent Γ.reference (C.left m) (C.right m) :=
    ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
      (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩
  have hidentify (side : Bool) (n : ℕ) (hn : S.chain.index ≤ n)
      (hl : n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n) :
      n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
        n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n := by
    obtain ⟨j, hj, _⟩ := retainedReference_positive_gap_is_component
      P hS hband hΓ hw hcoordinates side hn
    have hij : i = j := n04PositiveLeft_injective hf (hl.trans hj.1.symm)
    simpa only [hij] using hj
  rcases retainedReference_negative_component_identification
    P hS hband hq hΓ hw hcoordinates hcomponent with hcentral | htail
  · exact Or.inl (Or.inl (hm.trans hcentral.2))
  · obtain ⟨side, n, hn, _, hr, _⟩ := htail
    change C.right m = P.sideRadius side * S.chain.radius side n
      (morseRightTurn (morseChainA S.chain n) (morseChainB S.chain n)) at hr
    cases side with
    | false =>
      by_cases hnstart : n = S.chain.index
      · exact Or.inl (Or.inr (by simpa only [hnstart] using hm.trans hr))
      · have hnprev : S.chain.index ≤ n - 1 := by omega
        have hnnext : n - 1 + 1 = n := by omega
        refine Or.inr ⟨false, n - 1, hnprev, hidentify false (n - 1) hnprev ?_⟩
        simpa only [n06MorsePositiveLeft, Bool.false_eq_true, ↓reduceIte, hnnext]
          using hm.trans hr
    | true =>
      refine Or.inr ⟨true, n, hn, hidentify true n hn ?_⟩
      simpa only [n06MorsePositiveLeft, ↓reduceIte] using hm.trans hr

/-- The central exceptions are a finite part of the actual component
family, not additional artificial intervals. Their reciprocal widths
have one constant before the component index. -/
theorem retainedReference_positive_gap_exceptions_finite
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C) :
    let U : Set (N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)) :=
      {i | ¬ ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
        n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
        n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n}
    U.Finite ∧ ∃ B : ℝ, 0 < B ∧ ∀ i ∈ U,
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B := by
  let U : Set (N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)) :=
    {i | ¬ ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
      n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
      n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n}
  let A : Set ℝ := {centralRadius (sqrt centralOscillatorA),
    P.sideRadius false * S.chain.radius false S.chain.index
      (morseRightTurn (morseChainA S.chain S.chain.index)
        (morseChainB S.chain S.chain.index))}
  have hA : A.Finite := Set.Finite.insert _ (Set.finite_singleton _)
  have hf : Continuous (deriv Γ.reference.w) :=
    hΓ.2.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  have hsub : U ⊆ {i | n04PositiveLeft i ∈ A} := by
    intro i hi
    rcases retainedReference_positive_component_classification
      P hS hband hq hΓ hw hcoordinates hC i with he | hg
    · simpa only [A, mem_setOf_eq, mem_insert_iff, mem_singleton_iff] using he
    · exact (hi hg).elim
  obtain ⟨B, hB, hbound⟩ := n04PositiveComponent_width_inverse_bound_of_left_mem hf hA
  exact ⟨(n04PositiveComponent_finite_of_left_mem hf hA).subset hsub,
    B, hB, fun i hi => hbound i (hsub hi)⟩

end ContinuousFlexibility.Radial
