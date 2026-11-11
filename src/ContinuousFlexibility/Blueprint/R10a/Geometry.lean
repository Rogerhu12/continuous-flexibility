import ContinuousFlexibility.Radial.SelectedTailParameters
import ContinuousFlexibility.Radial.SeedRetainedReference

/-!
# R10a: one parameterized selected tail and its reference geometries

The selected object is chosen once after Cstar and the requested start.
Every later central window, head length and retained-cone length is then
realized with that same object and the prescribed fixed central column.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

/-- The actual selected construction data used by both regional inverses. -/
structure R10aSelectedMetadata (C : ℝ) (requestedIndex : ℕ) (S : SelectedTailData) where
  selected : IsSelectedTail S
  cstar : S.Cstar = C
  requested_index : requestedIndex ≤ S.chain.index
  large_index : 100 ≤ S.chain.index
  geometry : MorseChainGeometryWitness S.chain
  family_endpoints : ∀ sigma tau, (S.family sigma).a = (S.family tau).a ∧
    (S.family sigma).b = (S.family tau).b
  entry : S.entry = r07CellEntry S.chain
  entries_order : S.entry false S.chain.index < S.entry true S.chain.index
  first_two : radialFrequencyBand S.chain S.Cstar S.chain.index 2
  initial : ∀ right, S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
    0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
    RadialNaturalTail (S.family S.sigma) right 2 (S.entry right S.chain.index)
      (S.outgoing right 2)
  retained_entries : ∀ right n, S.chain.index ≤ n →
    S.entry right n ∈ radialCore (S.family S.sigma) ∧
    (if right then S.entry right S.chain.index ≤ S.entry right n
      else S.entry right n ≤ S.entry right S.chain.index)
  later_cut : ∀ right n, S.chain.index < n →
    S.cut right n = r07PreviousCellCut S.chain right (n - 1)
  later_join : ∀ right n, S.chain.index < n →
    S.joinInner right n = r07PreviousCellJoin S.chain right (n - 1)
  regular : ∀ right n j, 2 ≤ j → Even j → radialFrequencyBand S.chain S.Cstar n j →
    ContDiff ℝ ∞ (S.incoming right j) ∧ ContDiff ℝ ∞ (S.outgoing right j)
  later_join_state : ∀ right n j, 2 ≤ j → Even j → S.chain.index < n →
    radialFrequencyBand S.chain S.Cstar n j →
    ∃ a : ℝ, a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) ∧
      radialState (S.family S.sigma) j (S.joinInner right n)
        ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j) = (1, a)
  later_angle : ∀ right n j, 2 ≤ j → Even j → S.chain.index < n →
    radialFrequencyBand S.chain S.Cstar n j →
    r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState (S.family S.sigma) j (S.entry right n)
          ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j))
        (radialState (S.family S.sigma) j (S.entry right n)
          ((S.family S.sigma).w (S.joinInner right n)) (S.outgoing right j))
  join_small : R07JoinActionSmall S.chain S.Cstar (r07UniformTolerance S.Cstar / 100)
  first_cut_order : S.cut false S.chain.index < S.cut true S.chain.index
  first_cone : ∀ right, ∃ scale : ℝ, 0 < scale ∧
    ∀ r ∈ uIcc (S.cut right S.chain.index) (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[𝓝 r] (fun x => scale * x)

/-- Choose the selected sequence before the three freely adjustable
geometric parameters. The returned P is the actual retained construction,
including its uniform gap bounds, and Γ has exactly P's profile and height. -/
def R10aGeometrySupply : Prop :=
  ∀ (B : FixedCentralBorder) (C : ℝ), 1000 ≤ C → ∀ requestedIndex : ℕ,
    ∃ S : SelectedTailData, ∃ _metadata : R10aSelectedMetadata C requestedIndex S,
      ∀ T q length : ℝ, sqrt centralOscillatorA + 2 ≤ T → 0 < q → 0 < length →
        ∃ K : SeedCentralCutoff, ∃ P : SeedRetainedPair S K q length,
          ∃ Γ : ConnectedReferenceGeometry,
            Γ.selected = S ∧ Γ.headLength = q ∧ Γ.Realizes ∧
            Γ.reference.w = P.pair.profile ∧ Γ.reference.phi = P.pair.height ∧
            Γ.centralLeft = exp K.left ∧ Γ.centralRight = exp K.right ∧
            Γ.centralLeft < centralRadius (-T) ∧ centralRadius T < Γ.centralRight ∧
            referenceColumn Γ.reference = fixedCentralColumn B.chi ∧
            EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight) ∧
            EqOn Γ.reference.phi centralKernelHeight (Ioo Γ.centralLeft Γ.centralRight)

/-- The controlled selected-tail and retained-reference constructors
already prove the complete geometry supply, using only the deep-tail input. -/
theorem R10aGeometry (hR06 : R06Statement) : R10aGeometrySupply := by
  intro B C hC requestedIndex
  obtain ⟨S, hS, hCstar, hrequested, hlarge, hentry, horder, hfirst, hinitial,
    hretained, hangle, hregular, hsmall, hcutOrder, hcone, hconstruction⟩ :=
    exists_r10a_parameterized_selectedTail_with_data hR06 C hC requestedIndex
  rcases hconstruction with ⟨cFirst, G, H, phi, _, _, _, _, _, _, hfamily, hcut, hjoin⟩
  let metadata : R10aSelectedMetadata C requestedIndex S := {
    selected := hS
    cstar := hCstar
    requested_index := hrequested
    large_index := hlarge
    geometry := G
    family_endpoints := by
      intro sigma tau
      rw [hfamily]
      exact ⟨rfl, rfl⟩
    entry := hentry
    entries_order := horder
    first_two := hfirst
    initial := hinitial
    retained_entries := hretained
    later_cut := by
      intro right n hn
      rw [hcut, if_neg hn.ne']
    later_join := by
      intro right n hn
      rw [hjoin, if_neg hn.ne']
    regular := fun right n j hj heven hband =>
      ⟨(hregular right n j hj heven hband).1, (hregular right n j hj heven hband).2.1⟩
    later_join_state := fun right n j hj heven hn hband =>
      (hregular right n j hj heven hband).2.2 hn
    later_angle := by simpa only [hCstar] using hangle
    join_small := by simpa only [hCstar] using hsmall
    first_cut_order := hcutOrder
    first_cone := hcone }
  refine ⟨S, metadata, ?_⟩
  intro T q length hT hq hlength
  exact exists_seedRetainedFixedBorderGeometry B hS horder hfirst hT hq hlength

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R10aGeometry
