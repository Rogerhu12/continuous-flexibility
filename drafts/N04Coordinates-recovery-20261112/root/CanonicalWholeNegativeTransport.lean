import ContinuousFlexibility.Analysis.CanonicalActualEndpointFields

/-!
# The actual transport on one closed negative component

The two stored closed root fields agree with one common travel map in
the open component. Selecting the left field near the left root and the
right field near the right root therefore gives one ordinarily smooth
field on the entire closed component, including its artificial cut.
The values at true roots are the genuine closed inverse values.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def closedComponentField {E : Type*} (a b : ℝ)
    (F : Bool → PolarPoint → E) (p : PolarPoint) : E :=
  if p.1 ≤ (a + b) / 2 then F false p else F true p

theorem closedComponentField_root_germ {E : Type*} {a b : ℝ}
    (F : Bool → PolarPoint → E) (hab : a < b) (side : Bool) (θ : ℝ) :
    closedComponentField a b F =ᶠ[𝓝 (if side then b else a, θ)] F side := by
  cases side
  · have he : ∀ᶠ p : PolarPoint in 𝓝 (a, θ), p.1 < (a + b) / 2 :=
      continuousAt_fst.eventually_lt continuousAt_const (by linarith only [hab])
    filter_upwards [he] with p hp
    exact if_pos hp.le
  · have he : ∀ᶠ p : PolarPoint in 𝓝 (b, θ), (a + b) / 2 < p.1 :=
      continuousAt_const.eventually_lt continuousAt_fst (by linarith only [hab])
    filter_upwards [he] with p hp
    exact if_neg (not_le_of_gt hp)

theorem closedComponentField_eqOn {E : Type*} {a b : ℝ}
    {F : Bool → PolarPoint → E} {g : PolarPoint → E}
    (hF : ∀ side, EqOn (F side) g (Ioo a b ×ˢ (univ : Set ℝ))) :
    EqOn (closedComponentField a b F) g (Ioo a b ×ˢ (univ : Set ℝ)) := by
  intro p hp
  unfold closedComponentField
  split_ifs <;> exact hF _ p hp

theorem closedComponentField_contDiffAt_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {F : Bool → PolarPoint → E} {g : PolarPoint → E}
    (hab : a < b)
    (hg : ContDiffOn ℝ ∞ g (Ioo a b ×ˢ (univ : Set ℝ)))
    (hF : ∀ side, EqOn (F side) g (Ioo a b ×ˢ (univ : Set ℝ)))
    (hroot : ∀ side θ, ContDiffAt ℝ ∞ (F side) (if side then b else a, θ))
    {p : PolarPoint} (hp : p ∈ Icc a b ×ˢ (univ : Set ℝ)) :
    ContDiffAt ℝ ∞ (closedComponentField a b F) p := by
  by_cases ha : p.1 = a
  · have he : p = (a, p.2) := Prod.ext ha rfl
    rw [he]
    exact (hroot false p.2).congr_of_eventuallyEq
      (closedComponentField_root_germ F hab false p.2)
  by_cases hb : p.1 = b
  · have he : p = (b, p.2) := Prod.ext hb rfl
    rw [he]
    exact (hroot true p.2).congr_of_eventuallyEq
      (closedComponentField_root_germ F hab true p.2)
  have hpin : p ∈ Ioo a b ×ˢ (univ : Set ℝ) :=
    ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm ha), lt_of_le_of_ne hp.1.2 hb⟩, mem_univ _⟩
  have hU := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpin
  have he : closedComponentField a b F =ᶠ[𝓝 p] g := by
    filter_upwards [hU] with q hq
    exact closedComponentField_eqOn hF q hq
  exact (hg.contDiffAt hU).congr_of_eventuallyEq he

def canonicalWholeNegativeTransport {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : PolarPoint → PolarPoint :=
  closedComponentField (C.left m) (C.right m)
    (fun side => canonicalCurrentPoint C K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1))

def canonicalWholeNegativeHeightRatio {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : PolarPoint → ℝ :=
  closedComponentField (C.left m) (C.right m)
    (fun side => n04CoordinatesCurrentHeightRatio C K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hT hS hN hfield e hz hs

theorem canonicalWholeNegativeTransport_eq_travel :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    EqOn (canonicalWholeNegativeTransport C K z m)
      (n04CoordinatesNegativeTravelTransition S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) ∧
    EqOn (canonicalWholeNegativeHeightRatio C K z m)
      (n04CoordinatesNegativeTravelHeightRatio S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hi (side : Bool) :
      e (if side then (K.cutPair m).2 else (K.cutPair m).1) = .inl (m, side) := by
    have hp : K.cutPair m = (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl
    rw [hp]
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true, Equiv.apply_symm_apply]
  have hτ (side : Bool) := n04Coordinates_actualAtlas_currentPoint_eq_travel
    hT hS hN hfield hz hs m e _ side (hi side)
  constructor
  · exact closedComponentField_eqOn hτ
  · apply closedComponentField_eqOn
    intro side p hp
    unfold n04CoordinatesCurrentHeightRatio
    rw [hτ side p hp]
    exact n04Coordinates_actualAtlas_height_ratio_eq_travel
      hT hS hN hfield hz hs m e _ side (hi side) hp

theorem canonicalWholeNegativeTransport_closed_regular
    {p : PolarPoint} (hp : p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ContDiffAt ℝ ∞ (canonicalWholeNegativeTransport C K z m) p ∧
      ContDiffAt ℝ ∞ (canonicalWholeNegativeHeightRatio C K z m) p ∧
      0 < canonicalWholeNegativeHeightRatio C K z m p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hend (side : Bool) := n04Coordinates_actualAtlas_endpoint_fields
    hT hS hN hfield e hz hs m side
  have hi (side : Bool) :
      e (if side then (K.cutPair m).2 else (K.cutPair m).1) = .inl (m, side) := by
    have hp : K.cutPair m = (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl
    rw [hp]
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true, Equiv.apply_symm_apply]
  have hτ (side : Bool) := n04Coordinates_actualAtlas_currentPoint_eq_travel
    hT hS hN hfield hz hs m e _ side (hi side)
  have hq (side : Bool) : EqOn
      (n04CoordinatesCurrentHeightRatio C K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (n04CoordinatesNegativeTravelHeightRatio S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
    intro x hx
    unfold n04CoordinatesCurrentHeightRatio
    rw [hτ side x hx]
    exact n04Coordinates_actualAtlas_height_ratio_eq_travel
      hT hS hN hfield hz hs m e _ side (hi side) hx
  refine ⟨closedComponentField_contDiffAt_closed hab
    (n04CoordinatesNegativeTravelTransition_smooth hT hS hN hfield hz hs m)
    hτ (fun side θ => (hend side).root_smooth θ) hp,
    closedComponentField_contDiffAt_closed hab
      (n04CoordinatesNegativeTravelHeightRatio_smooth_pos hT hS hN hfield hz hs m).1
      hq (fun side θ => ((hend side).height_root θ).1) hp, ?_⟩
  by_cases ha : p.1 = C.left m
  · have he : p = (C.left m, p.2) := Prod.ext ha rfl
    rw [he]
    have hg := closedComponentField_root_germ
      (fun side => n04CoordinatesCurrentHeightRatio C K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1)) hab false p.2
    exact hg.eq_of_nhds.symm ▸ ((hend false).height_root p.2).2
  by_cases hb : p.1 = C.right m
  · have he : p = (C.right m, p.2) := Prod.ext hb rfl
    rw [he]
    have hg := closedComponentField_root_germ
      (fun side => n04CoordinatesCurrentHeightRatio C K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1)) hab true p.2
    exact hg.eq_of_nhds.symm ▸ ((hend true).height_root p.2).2
  have hpin : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm ha), lt_of_le_of_ne hp.1.2 hb⟩, mem_univ _⟩
  exact (closedComponentField_eqOn hq p hpin).symm ▸
    (n04CoordinatesNegativeTravelHeightRatio_smooth_pos hT hS hN hfield hz hs m).2 p hpin

end ContinuousFlexibility.Analysis
