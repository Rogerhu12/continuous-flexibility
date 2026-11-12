import ContinuousFlexibility.Analysis.ActualReferenceNegativeRadialFields
import ContinuousFlexibility.Analysis.WholeReferenceGaugeRelativeFields

/-!
# Actual reference radiality of the whole reference-gauged atlas

The negative fields are radial on their original open components. The
positive fields are the constructed radial cylinder maps and heights.
The actual inverse inherits radiality from the genuine inverse laws on
the reference pieces; no property of a total inverse outside its domain
is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04_referenceRadial_of_forward
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    (hforward : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      K.chart (C.referenceState, 0) m p =
        ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
      K.height (C.referenceState, 0) m p = K.height (C.referenceState, 0) m (p.1, 0)) :
    CanonicalGeometry.ReferenceRadial S C K := by
  refine ⟨hforward, ?_⟩
  intro m p hp
  let G := K.inverseChart (C.referenceState, 0) m
  let F := K.chart (C.referenceState, 0) m
  have hi := hA.charts (C.referenceState, 0) hz₀ hs₀ m
  have hq : G p ∈ referencePhysicalPieceOpen S K m := by
    rw [← hA.referenceDomain m]
    exact hi.2.1 hp
  have hq₀ : ((G p).1, 0) ∈ referencePhysicalPieceOpen S K m :=
    ⟨hq.1, mem_univ _⟩
  have hshape : F (G p) = ((F ((G p).1, 0)).1, (G p).2) :=
    (hforward m (G p) hq).1
  have hFG : F (G p) = p := hi.2.2.2.1 p hp
  have hθ : (G p).2 = p.2 :=
    (congrArg Prod.snd hshape).symm.trans (congrArg Prod.snd hFG)
  have hr : (F ((G p).1, 0)).1 = p.1 :=
    (congrArg Prod.fst hshape).symm.trans (congrArg Prod.fst hFG)
  have hF₀ : F ((G p).1, 0) = (p.1, 0) := by
    calc
      _ = ((F ((G p).1, 0)).1, 0) := (hforward m _ hq₀).1
      _ = (p.1, 0) := by rw [hr]
  have hG₀ : G (p.1, 0) = ((G p).1, 0) := by
    rw [← hF₀]
    apply hi.2.2.1
    rw [hA.referenceDomain m]
    exact hq₀
  exact Prod.ext (congrArg Prod.fst hG₀).symm hθ

theorem n04WholeReferenceGaugeAtlasData_actual_referenceRadial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base newBase loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (hε' : 0 < ε')
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    (hA : CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N) newBase ε') :
    CanonicalGeometry.ReferenceRadial S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  apply n04_referenceRadial_of_forward hA
    (reference_mem_stateNeighborhood S C newBase hε') hN.1.1.2.2.1.stateSector
  intro m p hp
  cases hi : e m with
  | inl j =>
      obtain ⟨_, _, hl, hr, _, _, _, hF, _, hh, _, _⟩ :=
        n04WholeReferenceGaugeAtlasData_negative_fields C L K e cell ψ χ h₀ τ σ Q N
          (C.referenceState, 0) m j hi
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hk : k = e₀.symm (.inl j) := by
        rcases j with ⟨m, side⟩
        cases side <;> rfl
      have hpK : p ∈ referencePhysicalPieceOpen S K k := by
        simpa only [referencePhysicalPieceOpen, hl, hr] using hp
      rw [hk] at hpK
      have hpI : p ∈ Ioo (if j.2 then n04bActualReferenceCut hN j.1 else C.left j.1)
          (if j.2 then C.right j.1 else n04bActualReferenceCut hN j.1) ×ˢ
            (univ : Set ℝ) := by
        simpa only [K, n04bActualTypedAtlas,
          n04bTypedAtlasData_referencePhysicalPieceOpen, Equiv.apply_symm_apply,
          n04bReferenceTypedLeft, n04bReferenceTypedRight,
          n04bNegativeLeft, n04bNegativeRight] using hpK
      have hcut := n04bActualReferenceCut_mem hN j.1
      have hpΩ : p ∈ Ioo (C.left j.1) (C.right j.1) ×ˢ (univ : Set ℝ) := by
        refine ⟨?_, mem_univ _⟩
        rcases j with ⟨m, side⟩
        cases side
        · exact ⟨hpI.1.1, hpI.1.2.trans hcut.2⟩
        · exact ⟨hcut.1.trans hpI.1.1, hpI.1.2⟩
      have hn := n04Coordinates_actual_reference_negative_radial_fields
        hT hS hN hfield e₀ j.1 j.2
      change V.chart (C.referenceState, 0) m p =
        ((V.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
        V.height (C.referenceState, 0) m p = V.height (C.referenceState, 0) m (p.1, 0)
      rw [hF, hh, hk]
      exact ⟨hn.2.2.1 p hpΩ, hn.2.2.2.1 p hpΩ⟩
  | inr i =>
      obtain ⟨hF, _, hh⟩ :=
        n04WholeReferenceGaugeAtlasData_positive_reference_fields
          C L K e cell ψ χ h₀ τ σ Q N m i hi
          (href i).1 (href i).2.1 (href i).2.2
      change V.chart (C.referenceState, 0) m p =
        ((V.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
        V.height (C.referenceState, 0) m p = V.height (C.referenceState, 0) m (p.1, 0)
      rw [hF, hh]
      exact ⟨rfl, rfl⟩

end ContinuousFlexibility.Analysis
