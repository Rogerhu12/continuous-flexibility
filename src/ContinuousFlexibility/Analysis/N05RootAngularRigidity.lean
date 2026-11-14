module

public import ContinuousFlexibility.Analysis.N05NegativeTravel

/-!
# The actual negative root chart is the identity

The root angular lift has periods pi and the original full optical return
time after subtracting the identity.  The frozen irrationality margin makes
these periods incommensurable.  Closed reflection fixes its additive
constant, yielding the actual identity chart at either physical root.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

theorem n05_cut_reference_root_angle
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) (θ : ℝ) :
    (K.chart (C.referenceState, 0)
      (if right then (K.cutPair m).2 else (K.cutPair m).1)
      (if right then C.right m else C.left m, θ)).2 = θ := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let G : ℝ → ℝ := fun t => (K.chart (C.referenceState, 0) i (root, t)).2
  let τ := n05TricomiTime (K.cutRadius m)
  have hG := n05_cut_reference_root_lift h m right
  have hhalf : opticalTravel D.w (K.physicalLeft i) (K.physicalRight i) = τ :=
    n05_cut_halfTravel_eq_time hT hS h m right
  have htravel : C.travel m = 2 * τ := n05_cut_totalTravel_eq_time hT hS h m
  have hshift (t : ℝ) : G (t + C.travel m) = G t + C.travel m := by
    have hdiff := n05_cut_reference_root_difference hT hS h m right (t + τ)
    change G (t + τ + opticalTravel D.w (K.physicalLeft i) (K.physicalRight i)) -
      G (t + τ - opticalTravel D.w (K.physicalLeft i) (K.physicalRight i)) = 2 * τ at hdiff
    rw [hhalf, add_sub_cancel_right, ← htravel] at hdiff
    have harg : t + τ + τ = t + C.travel m := by rw [htravel]; ring
    rw [harg] at hdiff
    linarith only [hdiff]
  have hirr : Irrational (C.travel m / Real.pi) :=
    (n05_controlTravel_quadraticIrrational h.1.1.1.1 h.1.1.1.2.2.2.1 m).1
  exact n05_odd_lift_eq_identity hG.1 hG.2.1 hshift hirr hG.2.2 θ

theorem n05_cut_reference_root_chart
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) (θ : ℝ) :
    K.chart (C.referenceState, 0)
      (if right then (K.cutPair m).2 else (K.cutPair m).1)
      (if right then C.right m else C.left m, θ) = (0, θ) :=
  Prod.ext (n05_cut_reference_root_image hT hS h m right θ)
    (n05_cut_reference_root_angle hT hS h m right θ)

end ContinuousFlexibility.Statements
