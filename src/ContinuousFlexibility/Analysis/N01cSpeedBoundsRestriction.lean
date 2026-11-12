import ContinuousFlexibility.Analysis.N01cBoundsRestriction
import ContinuousFlexibility.Blueprint.N01c.Statements

/-!
# Restriction of the actual speed estimate

The same complete quantifier transport used for ordinary flows applies to
the speed family. It keeps the original parameter-order loss and actual
directional derivatives when a later construction raises the base or
shrinks the common state neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true in
theorem characteristicSpeedTameBounds_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (h : CharacteristicSpeedTameBounds D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    CharacteristicSpeedTameBounds D T S C base' loss' ε' := by
  refine ⟨fun z hz m => h.1 z (stateNeighborhood_subset hb hε hz) m, ?_⟩
  exact ordinaryFlowBounds_restrict
    (E := AnnularState S × ℝ)
    (U := stateNeighborhood S C base ε) (V := stateNeighborhood S C base' ε')
    (grading := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0))
    (family := fun _ => characteristicSpeedFamily D S C)
    (left := C.left) (right := C.right)
    (weight := fun B m => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B)
    (isOpen_stateNeighborhood S C base' ε') (stateNeighborhood_subset hb hε)
    (jointStateGrading_monotone S) hb hl
    (fun B hB m => n01_componentWeight_nonneg hT
      (materialSample_mem_radialCore hT hRef.choose_spec.2.1) hB.le (C.cell m)) h.2

end ContinuousFlexibility.Blueprint
