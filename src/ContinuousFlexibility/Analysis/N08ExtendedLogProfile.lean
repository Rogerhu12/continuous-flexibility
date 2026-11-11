import ContinuousFlexibility.Analysis.N08LogProfileLift
import ContinuousFlexibility.Analysis.N08ScalarHeightParameter
import ContinuousFlexibility.Analysis.TameLocalLinear

/-!
# The actual logarithmic profile with an independent weak control

Adding the realized weak control series to the actual state logarithm gives
one continuous linear map. On physical circle directions its affine lines
are exactly the original state-profile lines. This identification holds for
every circle direction, including directions outside the constant sector.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

def n08StateParameterGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (AnnularState S × ℝ) := pairGrading (stateGrading S) realGrading

def n08ExtendedControlGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ ((AnnularState S × ℝ) × ControlBanach) :=
  pairGrading (n08StateParameterGrading S) controlGrading

theorem n08StateParameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (n08StateParameterGrading S) :=
  tamePairGrading_monotone (solve_stateGrading_monotone S) weighted_realGrading_monotone

theorem n08StateParameterGrading_topology (S : PhysicalSpacesData) :
    WithSeminorms (n08StateParameterGrading S) :=
  withSeminorms_pairGrading (solve_stateGrading_withSeminorms S)
    weighted_realGrading_withSeminorms

theorem n08ExtendedControlGrading_monotone (S : PhysicalSpacesData) :
    Monotone (n08ExtendedControlGrading S) :=
  tamePairGrading_monotone (n08StateParameterGrading_monotone S)
    (show Monotone controlGrading from fun _ _ _ => le_rfl)

theorem n08ExtendedControlGrading_topology (S : PhysicalSpacesData) :
    WithSeminorms (n08ExtendedControlGrading S) :=
  withSeminorms_pairGrading (n08StateParameterGrading_topology S)
    n08_normGrading_topology

section LinearCombination

variable {E B F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F]

private def n08_extendedLinear (L : E →L[ℝ] F) (M : B →L[ℝ] F) :
    (E × ℝ) × B →L[ℝ] F :=
  (L.comp (ContinuousLinearMap.fst ℝ E ℝ)).comp
      (ContinuousLinearMap.fst ℝ (E × ℝ) B) +
    M.comp (ContinuousLinearMap.snd ℝ (E × ℝ) B)

private theorem n08_extendedLinear_tame
    {p : ℕ → Seminorm ℝ E} {b : ℕ → Seminorm ℝ B} {q : ℕ → Seminorm ℝ F}
    {L : E →L[ℝ] F} {M : B →L[ℝ] F}
    (hp : Monotone p) (hb : Monotone b)
    (hL : IsTameLinear p q L.toLinearMap 0 0)
    (hM : IsTameLinear b q M.toLinearMap 0 0) :
    IsTameLinear (pairGrading (pairGrading p realGrading) b) q
      (n08_extendedLinear L M).toLinearMap 0 0 := by
  have hleft := inverseTame_comp_zero
    (inverseTame_comp_zero hL (inverseTame_fst p realGrading))
    (inverseTame_fst (pairGrading p realGrading) b)
  have hright := inverseTame_comp_zero hM (inverseTame_snd (pairGrading p realGrading) b)
  simpa only [n08_extendedLinear, ContinuousLinearMap.toLinearMap_add, max_self] using
    hleft.add (tamePairGrading_monotone
      (tamePairGrading_monotone hp weighted_realGrading_monotone) hb) hright

end LinearCombination

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08ExtendedLogProfileLift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    (AnnularState S × ℝ) × ControlBanach →L[ℝ] (S.height n08WeakControlWeight).Space :=
  n08_extendedLinear (n08LogProfileLift hT hS hN) (n08WeakControlLift hT hS hN)

theorem n08ExtendedLogProfileLift_apply
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (z : (AnnularState S × ℝ) × ControlBanach) :
    n08ExtendedLogProfileLift hT hS hN z =
      n08LogProfileLift hT hS hN z.1.1 + n08WeakControlLift hT hS hN z.2 := rfl

theorem n08ExtendedLogProfileLift_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    IsTameLinear (n08ExtendedControlGrading S) (S.height n08WeakControlWeight).grading
      (n08ExtendedLogProfileLift hT hS hN).toLinearMap 0 0 :=
  n08_extendedLinear_tame (solve_stateGrading_monotone S)
    (show Monotone controlGrading from fun _ _ _ => le_rfl)
    (n08LogProfileLift_isTame hT hS hN) (n08WeakControlLift_isTame hT hS hN)

theorem n08ExtendedLogProfileLift_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    UniformTameGerm (n08ExtendedControlGrading S) (S.height n08WeakControlWeight).grading
      ((C.referenceState, 0), 0) (n08ExtendedLogProfileLift hT hS hN) :=
  uniformTameGerm_continuousLinear (n08ExtendedControlGrading_topology S)
    ((C.referenceState, 0), 0) (n08ExtendedLogProfileLift hT hS hN)
    (n08ExtendedLogProfileLift_isTame hT hS hN)

theorem n08ExtendedLogProfileLift_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    n08ExtendedLogProfileLift hT hS hN ((C.referenceState, 0), 0) = 0 := by
  rw [n08ExtendedLogProfileLift_apply, n08LogProfileLift_reference hT hS hN,
    map_zero, add_zero]

theorem n08LogProfileLift_kappaDirection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (u : CircleSpace S) :
    n08LogProfileLift hT hS hN (0, (0, (u, 0))) =
      n08WeakControlLift hT hS hN (n08ControlRestriction S u) := by
  rw [n08LogProfileLift_apply]
  change n08NuProfileLift hT hS hN 0 +
    n08WeakControlLift hT hS hN (n08ControlRestriction S u) = _
  rw [map_zero, zero_add]

theorem n08ExtendedLogProfileLift_controlLine
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (u : CircleSpace S) (t : ℝ) :
    n08ExtendedLogProfileLift hT hS hN (z, t • n08ControlRestriction S u) =
      n08LogProfileLift hT hS hN
        (z.1 + n08StateSMul S t (0, (0, (u, 0)))) := by
  rw [n08ExtendedLogProfileLift_apply]
  calc
    _ = n08LogProfileLift hT hS hN z.1 +
        t • n08WeakControlLift hT hS hN (n08ControlRestriction S u) :=
      congrArg (fun v => n08LogProfileLift hT hS hN z.1 + v)
        ((n08WeakControlLift hT hS hN).map_smul t (n08ControlRestriction S u))
    _ = _ := by
      rw [n08StateSMul, n08RealSMul, map_add, map_smul,
        n08LogProfileLift_kappaDirection hT hS hN]

theorem n08ScalarHeightParameter_controlLine (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (u : CircleSpace S) (t : ℝ) :
    n08ScalarHeightParameter S
      (z.1 + n08StateSMul S t (0, (0, (u, 0))), z.2) =
        n08ScalarHeightParameter S z := by
  rw [n08ScalarHeightParameter_apply, n08ScalarHeightParameter_apply]
  change (((0, z.1.1.1 + t • (0 : (S.height (3 / 4 : ℝ)).Space)),
      z.1.1.2 + t • (0 : ℝ)), z.2) = (((0, z.1.1.1), z.1.1.2), z.2)
  simp only [smul_zero, add_zero]

end ContinuousFlexibility.Statements
