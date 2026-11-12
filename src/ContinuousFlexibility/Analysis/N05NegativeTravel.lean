import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05RootCutTransport
import ContinuousFlexibility.Analysis.N05PeriodicLiftRigidity

/-!
# Identification of the negative optical travel

The actual root angular map is a continuous odd degree-one pi lift.  Its
root-to-cut finite difference identifies each half travel with the common
Tricomi cut time.  Additivity of the actual optical integral then recovers
the original full return travel and its frozen irrationality margin.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

theorem n05_controlTravel_eq_opticalTravel
    (hC : controlGeometryConditions D S C) (m : ℕ) :
    C.travel m = opticalTravel D.w (C.left m) (C.right m) := by
  rcases hC with ⟨_, _, _, _, _, _, _, htravel, _⟩
  exact htravel m

theorem n05_controlTravel_quadraticIrrational
    (hD : IsRadialReference D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    QuadraticIrrational (C.travel m / Real.pi) := by
  have hc : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
      (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩
  obtain ⟨B, _, hmargin⟩ := hD.2.2.1.2
  rw [n05_controlTravel_eq_opticalTravel hC m]
  exact (hmargin (C.left m) (C.right m) hc).1

/-- The root angular map has the actual closed-chart symmetries. -/
theorem n05_cut_reference_root_lift
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let G : ℝ → ℝ := fun θ => (K.chart (C.referenceState, 0) i (root, θ)).2
    Continuous G ∧ (∀ θ, G (θ + Real.pi) = G θ + Real.pi) ∧
      (∀ θ, G (-θ) = -G θ) := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  have h01 := h.1.1.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hr : root ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    n05_cut_physical_root_mem h.2.2.2.2.1 m right
  have h04 := h.2.2.2.2.1
  have hclosed := n05_reference_closed_properties h04
  refine ⟨continuous_iff_continuousAt.mpr (fun θ => ?_), ?_, ?_⟩
  · exact (hclosed hmem hsector i (root, θ) hr).1.continuousAt.snd.comp
      (f := fun t : ℝ => (root, t))
      (continuousAt_const.prodMk continuousAt_id)
  · intro θ
    have hchart := (n05_reference_closed_periodicity h.2.2.2.2.1 hmem hsector i
      (p := (root, θ)) hr).1
    simpa only [Prod.mk_add_mk, Prod.snd_add, add_zero] using congrArg Prod.snd hchart
  · intro θ
    exact congrArg Prod.snd (n05_reference_closed_reflection h.2.2.2.2.1 hmem hsector i
      (p := (root, θ)) hr).1

theorem n05_cut_halfTravel_eq_time
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    opticalTravel D.w (K.physicalLeft i) (K.physicalRight i) =
      n05TricomiTime (K.cutRadius m) := by
  have hroot := n05_cut_reference_root_lift h m right
  exact (n05_lift_symmetric_difference hroot.1 Real.pi_pos.ne' hroot.2.1
    (fun θ => n05_cut_reference_root_difference hT hS h m right θ)).symm

/-- The original full optical travel is twice the time of the actual shared
canonical cut.  This is an equality of the frozen witnesses. -/
theorem n05_cut_totalTravel_eq_time
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) (m : ℕ) :
    C.travel m = 2 * n05TricomiTime (K.cutRadius m) := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hcuts := h04.2.1.1.1
  obtain ⟨_, _, hleft, hright, hmeet, _⟩ := hcuts m
  have hint (right : Bool) :
      IntervalIntegrable (opticalSpeed D.w) volume
        (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hpieces (if right then (K.cutPair m).2 else (K.cutPair m).1)).1.le]
    exact (n05_opticalSpeed_continuousOn_core h01.1.1).mono
      (n05_cut_physical_closed_subset_core h01.2.2.2.1 h.2.2.2.2.1 m right)
  have hintR : IntervalIntegrable (opticalSpeed D.w) volume
      (K.physicalRight (K.cutPair m).1) (K.physicalRight (K.cutPair m).2) := by
    simpa only [↓reduceIte, hmeet] using hint true
  have hL : opticalTravel D.w (K.physicalLeft (K.cutPair m).1)
      (K.physicalRight (K.cutPair m).1) = n05TricomiTime (K.cutRadius m) :=
    n05_cut_halfTravel_eq_time hT hS h m false
  have hR : opticalTravel D.w (K.physicalLeft (K.cutPair m).2)
      (K.physicalRight (K.cutPair m).2) = n05TricomiTime (K.cutRadius m) :=
    n05_cut_halfTravel_eq_time hT hS h m true
  calc
    C.travel m = opticalTravel D.w (C.left m) (C.right m) :=
      n05_controlTravel_eq_opticalTravel h01.2.2.2.1 m
    _ = opticalTravel D.w (K.physicalLeft (K.cutPair m).1)
        (K.physicalRight (K.cutPair m).2) := by rw [hleft, hright]
    _ = opticalTravel D.w (K.physicalLeft (K.cutPair m).1)
          (K.physicalRight (K.cutPair m).1) +
        opticalTravel D.w (K.physicalRight (K.cutPair m).1)
          (K.physicalRight (K.cutPair m).2) :=
      (intervalIntegral.integral_add_adjacent_intervals (hint false) hintR).symm
    _ = n05TricomiTime (K.cutRadius m) + n05TricomiTime (K.cutRadius m) := by
      rw [hL, hmeet, hR]
    _ = 2 * n05TricomiTime (K.cutRadius m) := by ring

end ContinuousFlexibility.Statements
