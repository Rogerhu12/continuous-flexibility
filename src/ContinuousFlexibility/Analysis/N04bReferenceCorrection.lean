import ContinuousFlexibility.Analysis.N01RadialFlow
import ContinuousFlexibility.Analysis.ReturnCorrectedFlow

/-!
# The actual correction preserves the radial reference flow

The ordinary reference return is translation by minus the reference
optical travel. Its stored inverse, the transported right chart, and the
stored inverse right chart are therefore determined by the N01 inverse
identities. The actual initial-point correction is the identity, so the
explicit corrected flow agrees with the original flow for every cutoff.

This is a property of the actual optical construction. It introduces no
canonical-coordinate or normal-form hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Reference membership uses the positive radius already in N01. -/
theorem N01Properties.n04b_reference_mem
    (hN : N01Properties D T S C base loss ε) :
    (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
  constructor
  · have hz : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
      (congrArg (fun x : AnnularState S => stateGrading S base x)
        (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
    exact hz.trans_lt hN.2.1
  · simpa only [abs_zero] using hN.2.1

theorem N01Properties.n04b_reference_sector
    (hN : N01Properties D T S C base loss ε) :
    stateSector S C.referenceState := by
  have href : referenceStateConditions D S C := hN.2.2.1
  constructor
  · intro m θ φ
    simp [href.2.2.2.1]
  · intro m θ
    simp [href.2.2.2.2.1]

/-- The radial ODE in N01 fixes the actual reference flow, including
both endpoints. -/
theorem N01Properties.n04b_reference_flow_eq
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    C.minusFlow (C.referenceState, 0) m r θ =
      θ - opticalTravel D.w (C.left m) r := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hprofile : stateProfile D S C C.referenceState = D.w := by
    funext s
    simp [stateProfile, stateKappa, href.2.2.1, href.2.2.2.1, angularMean]
  simpa only [hprofile] using
    hN.minusFlow_zero_eq_opticalTravel hS hT hN.n04b_reference_mem m θ hr

/-- Both actual stored inverse maps are forced at the reference state. -/
theorem N01Properties.n04b_reference_chart_identities
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) :
    (∀ θ, C.minusReturnInverse (C.referenceState, 0) m θ = θ + C.travel m) ∧
    (∀ θ, rightChartCandidate S C (C.referenceState, 0) m θ = θ) ∧
    (∀ θ, C.rightChartInverse (C.referenceState, 0) m θ = θ) := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hleft (θ : ℝ) : stateLeftChart S C.referenceState m θ = θ := by
    simp [stateLeftChart, href.2.2.2.2.1]
  have htravel : opticalTravel D.w (C.left m) (C.right m) = C.travel m := by
    exact (hcontrol.2.2.2.2.2.2.2.1 m).symm
  have hreturn (θ : ℝ) :
      C.minusFlow (C.referenceState, 0) m (C.right m) θ = θ - C.travel m := by
    rw [hN.n04b_reference_flow_eq hS hT m
      (show C.right m ∈ Icc (C.left m) (C.right m) from
        ⟨(hcontrol.1 m).2.1.le, le_rfl⟩), htravel]
  have hI := N01Properties.return_inverse_and_positive S C (C.referenceState, 0)
    m hN hN.n04b_reference_mem hN.n04b_reference_sector
  have hinv (θ : ℝ) :
      C.minusReturnInverse (C.referenceState, 0) m θ = θ + C.travel m := by
    have h := (hI θ).1
    rw [hreturn] at h
    linarith only [h]
  have hright (θ : ℝ) :
      rightChartCandidate S C (C.referenceState, 0) m θ = θ := by
    simp only [rightChartCandidate, oddPart, hleft, hinv]
    ring
  refine ⟨hinv, hright, fun θ => ?_⟩
  simpa only [hright] using (hI θ).2.2.1

theorem N01Properties.n04b_returnCorrectionInitialMap_reference
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) (θ : ℝ) :
    returnCorrectionInitialMap S C (C.referenceState, 0) m θ = θ := by
  have href : referenceStateConditions D S C := hN.2.2.1
  obtain ⟨hinv, _, hrightInv⟩ := hN.n04b_reference_chart_identities hS hT m
  simp [returnCorrectionInitialMap, stateLeftChart, href.2.2.2.2.1,
    hrightInv, hinv]

/-- This equality holds at every radius and for an arbitrary cutoff
family, because its interpolated initial point is exactly unchanged. -/
theorem N01Properties.n04b_returnCorrectedMinusFlow_reference_eq_original
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (r θ : ℝ) :
    returnCorrectedMinusFlow S C χ (C.referenceState, 0) m r θ =
      C.minusFlow (C.referenceState, 0) m r θ := by
  simp only [returnCorrectedMinusFlow, returnInterpolation,
    hN.n04b_returnCorrectionInitialMap_reference hS hT, sub_self, mul_zero, add_zero]

/-- The explicit corrected witness has the actual radial reference
flow required to identify its reference travel domains. -/
theorem N01Properties.n04b_returnCorrectedMinusFlow_reference
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    returnCorrectedMinusFlow S C χ (C.referenceState, 0) m r θ =
      θ - opticalTravel D.w (C.left m) r := by
  rw [hN.n04b_returnCorrectedMinusFlow_reference_eq_original hS hT,
    hN.n04b_reference_flow_eq hS hT m hr]

/-- The pointwise velocity correction also vanishes identically at the
reference state, with no regularity or support assumption on the cutoff. -/
theorem N01Properties.n04b_returnCorrectedMinusSpeed_reference
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (p : PolarPoint) :
    returnCorrectedMinusSpeed D S C χ (C.referenceState, 0) m p =
      minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0)) p := by
  simp only [returnCorrectedMinusSpeed,
    hN.n04b_returnCorrectionInitialMap_reference hS hT, sub_self, mul_zero, add_zero]

end ContinuousFlexibility.Statements
