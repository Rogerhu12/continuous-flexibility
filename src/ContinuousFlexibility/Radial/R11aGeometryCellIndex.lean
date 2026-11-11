import ContinuousFlexibility.Blueprint.R10a.Geometry
import ContinuousFlexibility.Radial.SeedRetainedReference
import ContinuousFlexibility.Radial.SeedReturnMargins
import ContinuousFlexibility.Radial.MatchedWeightFlooredMorseFibers

/-!
# One constructed reference with retained coordinates and return margins

The actual selected family is chosen before the central window and head
length. The same retained-pair reference receives the finite index floor
and cell saturation from the proved return-margin construction. Its
profiles, true border and every localizer stay unchanged. We retain the
exact floor, the original cell inclusion, and a finite multiplicity bound
for the final reference itself.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The original parameterized construction, with actual return margins
and the complete localizer pullback on the same final reference. -/
theorem r11a_exists_parameterized_geometry_with_construction_geometry
    (hR06 : R06Statement) (B : FixedCentralBorder)
    (C : ℝ) (hC1000 : 1000 ≤ C) (requestedIndex : ℕ) :
    ∃ S : SelectedTailData, ∃ _metadata : R10aSelectedMetadata C requestedIndex S,
      ∀ T q length : ℝ, sqrt centralOscillatorA + 2 ≤ T → 0 < q → 0 < length →
        ∃ K : SeedCentralCutoff, ∃ P : SeedRetainedPair S K q length,
          ∃ Γ : ConnectedReferenceGeometry, ∃ e : ℝ ≃o ℝ, ∃ N : ℕ, 1 ≤ N ∧
            Γ.selected = S ∧ Γ.headLength = q ∧ Γ.Realizes ∧
            RadialConstructionGeometry Γ.reference ∧
            (S.family S.sigma).cellIndex =
              morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) ∧
            Γ.reference.cellIndex = (fun m =>
              max (morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) m) N) ∧
            (∀ m, e ⁻¹' (S.family S.sigma).cells m ⊆ Γ.reference.cells m) ∧
            Γ.reference.localizer = (fun m r => (S.family S.sigma).localizer m (e r)) ∧
            (∀ r ≤ S.entry false S.chain.index, e.symm r = P.pair.radiusL * r) ∧
            (∀ r, S.entry true S.chain.index ≤ r → e.symm r = P.pair.radiusR * r) ∧
            (∀ n : ℕ, Set.Finite {m | Γ.reference.cellIndex m = n} ∧
              Set.ncard {m | Γ.reference.cellIndex m = n} ≤ 2 * N + 3) ∧
            Γ.reference.w = P.pair.profile ∧ Γ.reference.phi = P.pair.height ∧
            Γ.centralLeft = exp K.left ∧ Γ.centralRight = exp K.right ∧
            Γ.centralLeft < centralRadius (-T) ∧ centralRadius T < Γ.centralRight ∧
            referenceColumn Γ.reference = fixedCentralColumn B.chi ∧
            EqOn Γ.reference.w (centralRadialProfile 1)
              (Ioo Γ.centralLeft Γ.centralRight) ∧
            EqOn Γ.reference.phi centralKernelHeight
              (Ioo Γ.centralLeft Γ.centralRight) ∧
            Γ.reference.a = P.pair.radiusL * (S.family S.sigma).a ∧
            Γ.reference.b = P.pair.radiusR * (S.family S.sigma).b := by
  obtain ⟨S, hS, hCstar, hrequested, hlarge, hentry, horder, hfirst, hinitial,
    hretained, hangle, hregular, hsmall, hcutOrder, hcone, hconstruction⟩ :=
    exists_r10a_parameterized_selectedTail_with_data hR06 C hC1000 requestedIndex
  rcases hconstruction with
    ⟨cFirst, G, H, phi, _, _, _, hM, _, _, hfamily, hcut, hjoin⟩
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
    initial_bridge_positive := fun right _ hr =>
      selected_initial_bridge_deriv_pos hS hfirst hentry hcutOrder G hM hfamily right hr
    retained_entries := hretained
    later_cut := by
      intro right n hn
      rw [hcut]
      change (if n = S.chain.index then H.cut right
        else r07PreviousCellCut S.chain right (n - 1)) = _
      exact if_neg hn.ne'
    later_join := by
      intro right n hn
      rw [hjoin]
      change (if n = S.chain.index then H.join right
        else r07PreviousCellJoin S.chain right (n - 1)) = _
      exact if_neg hn.ne'
    regular := fun right n j hj heven hband =>
      ⟨(hregular right n j hj heven hband).1, (hregular right n j hj heven hband).2.1⟩
    later_join_state := fun right n j hj heven hn hband =>
      (hregular right n j hj heven hband).2.2 hn
    later_angle := by simpa only [hCstar] using hangle
    join_small := by simpa only [hCstar] using hsmall
    first_cut_order := hcutOrder
    first_cone := hcone }
  have hlabels : (S.family S.sigma).cellIndex =
      morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) :=
    congrArg (fun family : (ℕ → ℝ) → ReferenceData =>
      (family S.sigma).cellIndex) hfamily
  refine ⟨S, metadata, ?_⟩
  intro T q length hT hq hlength
  obtain ⟨K, P, Γ, hselected, hhead, hreal, hw, hphi, hleft, hright,
      hleftWindow, hrightWindow, hcolumn, hwCentral, hphiCentral, hconstruction,
      e, N, hN, hindex, hcells, hlocalizer, hleftDilation, hrightDilation, ha, hb⟩ :=
    exists_seedRetainedFixedBorderGeometry_with_transport B hS horder hfirst
      metadata.initial_bridge_positive hT hq hlength
  have hindex' : Γ.reference.cellIndex = (fun m =>
      max (morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) m) N) := by
    simpa only [hlabels] using hindex
  refine ⟨K, P, Γ, e, N, hN, hselected, hhead, hreal, hconstruction,
    hlabels, hindex', hcells, hlocalizer, hleftDilation, hrightDilation, ?_, hw, hphi,
    hleft, hright, hleftWindow, hrightWindow, hcolumn, hwCentral, hphiCentral, ha, hb⟩
  intro n
  simpa only [hindex'] using morseTwoTailAt_floor_level_fiber_bound S.chain.index N n

end ContinuousFlexibility.Radial
