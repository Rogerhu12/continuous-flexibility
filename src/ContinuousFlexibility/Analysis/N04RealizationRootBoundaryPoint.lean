module

public import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
public import ContinuousFlexibility.Analysis.CanonicalRootTransportBoundary
public import ContinuousFlexibility.Analysis.N01RootLabels
public import ContinuousFlexibility.Analysis.N04bReferenceCorrection

/-!
# The actual inverse point on a physical root circle

The closed chart retained by the typed atlas has the original N01 root
label. Its closed inverse is consequently the inverse of that same
label, with the physical radius fixed. At the reference state the label
is the identity, by the proved N01 reference-flow formulas.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private theorem inverse_at_root_of_label
    (F G : PolarPoint → PolarPoint) (h : ℝ → ℝ) (c : ℝ)
    (hh : Function.Surjective h)
    (hF : ∀ θ, F (c, θ) = (0, h θ))
    (hG : ∀ θ, G (F (c, θ)) = (c, θ)) (θ : ℝ) :
    G (0, θ) = (c, Function.invFun h θ) := by
  have hf := hF (Function.invFun h θ)
  rw [Function.rightInverse_invFun hh θ] at hf
  rw [← hf]
  exact hG _

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- The actual reference labels are fixed by the original N01 data. -/
theorem n04Realization_rootLabel_reference_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (side : Bool) (θ : ℝ) :
    n01RootLabel S C (C.referenceState, 0) m side θ = θ := by
  cases side with
  | false => exact n04b_referenceState_leftChart hN.2.2.1 m θ
  | true => exact (hN.n04b_reference_chart_identities hS hT m).2.1 θ

/-- The same stored negative chart has exactly its N01 angular label at
the true root, including the closed physical-domain membership. -/
theorem n04Realization_actualRoot_chart_data
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side)) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let c := if side then C.right m else C.left m
    (c, θ) ∈ physicalPieceClosed S K z k ∧
      K.chart z k (c, θ) = (0, n01RootLabel S C z m side θ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let c : ℝ := if side then C.right m else C.left m
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have hk : e.symm (.inl (m, side)) = k := by
    simpa only [Equiv.symm_apply_apply] using (congrArg e.symm hi).symm
  have hki : (if side then (K.cutPair m).2 else (K.cutPair m).1) = k := by
    cases side <;> simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_cutPair,
      Bool.false_eq_true, ↓reduceIte] using hk
  have hroot : (c, θ) ∈ physicalPieceClosed S K z k ∧
      (K.chart z k (c, θ)).1 = 0 := by
    simpa only [hki] using canonicalCutRoot_mem_closed_and_zero hA hcut hz hs m side θ
  have hfields := n04bTypedAtlasData_negative_fields (C := C) (L := L) (z := z)
    e (n04bActualNegativeChart hT hS hN hfield)
    (n04bActualNegativeHeight hT hS hN hfield)
    (n04bActualNegativeInverse hT hS hN hfield) (n04bActualReferenceCut hN)
    k m side hi
  have hΩ : physicalPieceOpen S K z k = n04bActualNegativeDomain S C L z m side :=
    hfields.1
  have hF : K.chart z k = n04bActualNegativeChart hT hS hN hfield z m side :=
    hfields.2.2.2.1
  have hp : (c, θ) ∈ closure (n04bActualNegativeDomain S C L z m side) := by
    simpa only [physicalPieceClosed, hΩ] using hroot.1
  have hraw : K.chart z k (c, θ) =
      n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side (c, θ) := by
    rw [hF]
    exact (n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side).closed_chart_eq hp
  have hlabel : (n04bActualTravelChart S C L z m (c, θ)).2 =
      n01RootLabel S C z m side θ := by
    have ht := n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ
    cases side with
    | false => exact congrArg Prod.snd ht.1
    | true => exact congrArg Prod.snd ht.2
  refine ⟨hroot.1, Prod.ext hroot.2 ?_⟩
  exact (congrArg Prod.snd hraw).trans hlabel

/-- The inverse is the stored actual inverse, at the original zero edge. -/
theorem n04Realization_actualRoot_inverse_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side)) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    K.inverseChart z k (0, θ) =
      (if side then C.right m else C.left m,
        Function.invFun (n01RootLabel S C z m side) θ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hroot := n04Realization_actualRoot_chart_data hT hS hN hfield e hz hs k m side hi
  have hb := n04b_actualTravel_endpoint_bijections hN hS hz hs m
  have hsurj : Function.Surjective (n01RootLabel S C z m side) := by
    cases side
    · exact hb.1.2
    · exact hb.2.2
  exact inverse_at_root_of_label (K.chart z k) (K.inverseChart z k)
    (n01RootLabel S C z m side) (if side then C.right m else C.left m) hsurj
    (fun η => (hroot η).2)
    (fun η => (hA.boundary z hz hs k).2.2.1 _ (hroot η).1) θ

/-- The actual relative point is evaluated at the same physical root.
Its reference angular argument is exactly the identity, as proved above. -/
theorem n04Realization_actualRoot_currentPoint_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side)) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    canonicalCurrentPoint C K z k (if side then C.right m else C.left m, θ) =
      (if side then C.right m else C.left m,
        Function.invFun (n01RootLabel S C z m side) θ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have href := n04b_reference_valid_of_through03 hN
  have hchart := (n04Realization_actualRoot_chart_data hT hS hN hfield e
    href.1 href.2 k m side hi θ).2
  rw [n04Realization_rootLabel_reference_eq hT hS hN.1.1] at hchart
  change K.inverseChart z k (K.chart (C.referenceState, 0) k
    (if side then C.right m else C.left m, θ)) = _
  rw [hchart]
  exact n04Realization_actualRoot_inverse_eq hT hS hN hfield e hz hs k m side hi θ

end ContinuousFlexibility.Analysis
