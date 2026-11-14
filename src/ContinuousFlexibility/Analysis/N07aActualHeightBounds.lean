module

public import ContinuousFlexibility.Analysis.N07aActualForwardChartBounds
public import ContinuousFlexibility.Analysis.N07aStateJacobianJetBounds

/-!
# Height jets on the actual current physical domains

At a genuine physical point, height equals the canonical source factor
pulled back by the forward chart times the absolute forward Jacobian.
Both factors are estimated from canonical atoms and the proved actual
forward jets, with finitely many fixed-loss product operations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n07a_height_with_exists {α : Type*} {Condition : α → Prop} {P : Prop}
    (h : ∃ a, Condition a) (hP : ∀ a, Condition a → P) : P := by
  obtain ⟨a, ha⟩ := h
  exact hP a ha

private theorem n07a_height_from_forward_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ Z) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set Z) (W V : Z → ℕ → Set PolarPoint)
    (F : Z → ℕ → PolarPoint → PolarPoint) (SF H : Z → ℕ → PolarPoint → ℝ)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hV : ∀ z ∈ U, ∀ m, IsOpen (V z m))
    (hFs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (F z m) (W z m))
    (hSFs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (SF z m) (V z m))
    (hmap : ∀ z ∈ U, ∀ m, MapsTo (F z m) (W z m) (V z m))
    (hJne : ∀ z ∈ U, ∀ m x, x ∈ W z m → planeJacobian (F z m) x ≠ 0)
    (ds : ℕ) (hSF : N07aStateSampleJetBounds T K p U V ds SF)
    (hforward : ∃ lf df : ℕ, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, p lf z ≤ 1 → ∀ m x, x ∈ W z m →
          ‖iteratedFDeriv ℝ n (F z m) x‖ ≤ e m * (1 + p ((n - 1) + df) z))
    (hHeight : ∀ z ∈ U, ∀ m, EqOn
      (fun x => SF z m (F z m x) * |planeJacobian (F z m) x|) (H z m) (W z m)) :
    ∃ low loss : ℕ, N07aStateSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1}
      W loss H := by
  have hcomp_s (z : Z) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (SF z m ∘ F z m) (W z m) :=
    (hSFs z hz m).comp (hFs z hz m) (hmap z hz m)
  have hJs (z : Z) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (planeJacobian (F z m)) (W z m) := fun x hx =>
    (contDiffAt_planeJacobian ((hFs z hz m).contDiffAt
      ((hW z hz m).mem_nhds hx))).contDiffWithinAt
  have hJabs_s (z : Z) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (fun x => |planeJacobian (F z m) x|) (W z m) :=
    (hJs z hz m).abs (hJne z hz m)
  obtain ⟨lf, df, hforward⟩ := hforward
  let U₀ := {z | z ∈ U ∧ p lf z ≤ 1}
  have hF : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U₀, ∀ m x, x ∈ W z m →
          ‖iteratedFDeriv ℝ n (F z m) x‖ ≤ e m * (1 + p ((n - 1) + df) z) := by
    intro n hn
    obtain ⟨e, he, he0, heb⟩ := hforward n hn
    exact ⟨e, he, he0, fun z hz => heb z hz.1 hz.2⟩
  have hSF₀ : N07aStateSampleJetBounds T K p U₀ V ds SF :=
    hSF.restrict (fun _ hz => hz.1)
  obtain ⟨lc, dc, hcomp⟩ := n07a_stateSampleJetBounds_comp hD hT p hp hIp U₀ W V
    (fun z hz => hW z hz.1) (fun z hz => hV z hz.1)
    SF F ds df hSF₀ (fun z hz => hSFs z hz.1) (fun z hz => hFs z hz.1)
    (fun z hz => hmap z hz.1) hF
  obtain ⟨lj, dj, hJac⟩ := n07a_statePlaneJacobian_sampleJets hD hT p hp hIp U₀ W F df
    (fun z hz => hW z hz.1) (fun z hz => hFs z hz.1) hF
  have hJacAbs := hJac.abs
    (fun z hz m x hx => (hJs z hz.1.1 m).contDiffAt
      ((hW z hz.1.1 m).mem_nhds hx) |>.continuousAt)
    (fun z hz => hJne z hz.1.1)
  let l₀ := max lf (max lc lj)
  let U₁ := {z | z ∈ U ∧ p l₀ z ≤ 1}
  have hlf : lf ≤ l₀ := le_max_left _ _
  have hlc : lc ≤ l₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hlj : lj ≤ l₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hcomp₁ : N07aStateSampleJetBounds T K p U₁ W dc (fun z m => SF z m ∘ F z m) :=
    hcomp.restrict (fun z hz => ⟨⟨hz.1, (hp hlf z).trans hz.2⟩, (hp hlc z).trans hz.2⟩)
  have hJac₁ : N07aStateSampleJetBounds T K p U₁ W dj
      (fun z m x => |planeJacobian (F z m) x|) :=
    hJacAbs.restrict (fun z hz => ⟨⟨hz.1, (hp hlf z).trans hz.2⟩, (hp hlj z).trans hz.2⟩)
  obtain ⟨lm, dm, hmul⟩ := n07a_stateSampleJetBounds_mul hD hT p hp hIp U₁ W
    (fun z hz => hW z hz.1) (max dc dj)
    (fun z m => SF z m ∘ F z m) (fun z m x => |planeJacobian (F z m) x|)
    (hcomp₁.loss_mono hp (le_max_left _ _)) (hJac₁.loss_mono hp (le_max_right _ _))
    (fun z hz => hcomp_s z hz.1) (fun z hz => hJabs_s z hz.1)
  let low := max l₀ lm
  have hfinal := hmul.restrict
    (fun z (hz : z ∈ {z | z ∈ U ∧ p low z ≤ 1}) =>
      ⟨⟨hz.1, (hp (le_max_left _ _) z).trans hz.2⟩,
        (hp (le_max_right _ _) z).trans hz.2⟩)
  exact ⟨low, dm, hfinal.congr (fun z hz => hW z hz.1)
    (fun z hz => hHeight z hz.1)⟩

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_actualHeight_eq_sourceFactor_chart
    (hgeom : CanonicalGeometry D S C K base ε)
    (z : CanonicalGeometry.Parameter S)
    (hz : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m) :
    K.height (liftSectorParameter S C z) m x =
      n07aCanonicalAtomField D T S C L K .sourceFactor z m
        (K.chart (liftSectorParameter S C z) m x) *
          |planeJacobian (K.chart (liftSectorParameter S C z) m) x| := by
  have hc := hgeom.charts (liftSectorParameter S C z) hz hs m
  have hinv := hc.2.2.1 x hx
  have hunit := n07aCanonicalUnitPoint_inverse (hgeom.referenceBounds m).2.1
    (K.chart (liftSectorParameter S C z) m x)
  have hj := abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 x hx).2.1
  simp only [n07aCanonicalAtomField, Function.comp_apply, CanonicalGeometry.atom,
    hunit, canonicalSource, hinv, mul_one]
  field_simp [hj]

theorem n07a_actualHeight_sampleJetBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hFirst : N07aActualForwardFirstBound T S C K base ε) :
    ∃ low loss : ℕ,
      N07aStateSampleJetBounds T K (CanonicalGeometry.parameterGrading S)
        {z | z ∈ sectorNeighborhood S base ε ε ∧
          CanonicalGeometry.parameterGrading S low z ≤ 1}
        (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m) loss
        (fun z m => K.height (liftSectorParameter S C z) m) := by
  refine n07a_height_with_exists
    (n07a_canonicalAtomFields_sampleJetBounds hD hT href hcur
      (fun m => (hgeom.referenceBounds m).2.1)) ?_
  intro ds hSF
  exact n07a_height_from_forward_jets hD hT (CanonicalGeometry.parameterGrading S)
    (n07aParameterGrading_monotone S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
    (sectorNeighborhood S base ε ε)
    (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m)
    (fun _ => canonicalOpen S K)
    (fun z m => K.chart (liftSectorParameter S C z) m)
    (n07aCanonicalAtomField D T S C L K .sourceFactor)
    (fun z m => K.height (liftSectorParameter S C z) m)
    (fun z hz m => (hgeom.domains (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).1)
    (fun _ _ _ => isOpen_Ioo.prod isOpen_univ)
    (fun z hz m => (hgeom.charts (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.2.2.1)
    (n07a_canonicalAtomField_smooth hcur
      (fun m => (hgeom.referenceBounds m).2.1) .sourceFactor)
    (fun z hz m => (hgeom.charts (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).1)
    (fun z hz m x hx => ((hgeom.charts (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.2.2.2.2.2 x hx).2.1)
    ds (hSF .sourceFactor).to_state
    (n07a_actualForward_positive_jets hD hT hS hrefState hgeom href hcur hFirst)
    (fun z hz m x hx => (n07a_actualHeight_eq_sourceFactor_chart (L := L) hgeom z
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m hx).symm)

end ContinuousFlexibility.Analysis
