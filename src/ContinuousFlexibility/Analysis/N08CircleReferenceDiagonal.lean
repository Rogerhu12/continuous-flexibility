import ContinuousFlexibility.Analysis.N08CircleDiagonal
import ContinuousFlexibility.Analysis.N08ControlProfileModes
import ContinuousFlexibility.Analysis.N08RadialFlow
import ContinuousFlexibility.Analysis.SpacesCompactHeights

/-!
# The actual control diagonal at the reference state

On the genuine weighted single-control line the zero-parameter flow is
the optical rotation of the perturbed profile.  The normalization of the
control in N01 therefore computes its return derivative.  The physical
input and output weights cancel exactly, giving diagonal entry one.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08_returnResidualField_zero_trivialChart
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S x) (m : ℕ)
    (hchart : ∀ θ, stateLeftChart S x m θ = θ) (θ : ℝ) :
    returnResidualField S C (x, 0) m θ =
      opticalTravel (stateProfile D S C x) (C.left m) (C.right m) - C.travel m := by
  simp only [returnResidualField, evenPart,
    n08_minusReturnInverse_zero_parameter hS hT hN x hx hs, hchart]
  ring

theorem n08ControlBasis_direction_sector (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    stateSector S (0, 0, n08ControlBasis hS m, 0) := by
  constructor
  · intro n θ φ
    change (S.circle (3 / 4 : ℝ)).decode (n08ControlBasis hS m) n θ =
      (S.circle (3 / 4 : ℝ)).decode (n08ControlBasis hS m) n φ
    rw [n08ControlBasis_decode]
    rfl
  · intro n θ
    change (S.circle (3 / 4 : ℝ)).decode 0 n (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode 0 n θ
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem n08_controlBasis_reference_profile
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hC : controlGeometryConditions D S C) (m : ℕ) (t : ℝ) :
    stateProfile D S C
        (C.referenceState + n08StateSMul S t (0, 0, n08ControlBasis hS m, 0)) =
      opticalLogPerturbation D.w (C.control m) (t * T.H (T.sample m) ^ (3 / 4 : ℝ)) := by
  funext r
  rw [n08_stateProfile_affine hS hC, n08_stateProfile_reference href,
    n08_logProfile_controlBasis hS]
  simp only [n08WeightedControlProfile, opticalLogPerturbation, mul_assoc]

theorem n08CircleDiagonal_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) (m : ℕ) :
    n08CircleDiagonal hS hR (C.referenceState, 0) m = 1 := by
  let v : AnnularState S := (0, 0, n08ControlBasis hS m, 0)
  let x : ℝ → AnnularState S := fun t => C.referenceState + n08StateSMul S t v
  let A : ℝ := T.H (T.sample m) ^ (3 / 4 : ℝ)
  let B : ℝ := T.H (T.sample m) ^ (-(3 / 4 : ℝ))
  let τ : ℝ → ℝ := fun t =>
    opticalTravel (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m)
  let f : ℝ → ℝ := fun t =>
    n08ControlMeanCoordinate S m (n08CircleResidual hS hR (x t, 0)).val
  have href := hN.2.2.1
  have hC := hN.2.2.2.1
  have hzero : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      simpa only [sub_self, map_zero] using hN.2.1
    · exact (abs_zero : |(0 : ℝ)| = 0).trans_lt hN.2.1
  have hs (t : ℝ) : stateSector S (x t) :=
    (stateSectorSubmodule S).add_mem href.stateSector
      ((stateSectorSubmodule S).smul_mem t (n08ControlBasis_direction_sector hS m))
  have hchart (t θ : ℝ) : stateLeftChart S (x t) m θ = θ := by
    have he : (x t).2.2.2 = C.referenceState.2.2.2 :=
      (n08_kappaLine_fixed_coordinates S C.referenceState (n08ControlBasis hS m) t).2.2
    simp only [stateLeftChart, he, href.2.2.2.2.1, map_zero, Pi.zero_apply, add_zero]
  have hev : ∀ᶠ t : ℝ in 𝓝 0, (x t, 0) ∈ stateNeighborhood S C base ε :=
    n08_affine_parameter_eventually C.referenceState v 0
      (n08_isOpen_stateNeighborhood S C base ε) hzero
  have heq : f =ᶠ[𝓝 0] fun t => B * (τ (t * A) - C.travel m) := by
    filter_upwards [hev] with t ht
    dsimp only [f]
    rw [n08ControlMeanCoordinate_apply, n08ControlRestriction_apply hS,
      n08CircleResidual_coe hS hR ht (hs t)]
    have hd : (S.circle (3 / 4 : ℝ)).decode (R.residual (x t, 0)) m =
        fun _ => τ (t * A) - C.travel m := by
      funext θ
      rw [hR.2.1 (x t, 0) ht (hs t),
        n08_returnResidualField_zero_trivialChart hS hT hN (x t) ht (hs t) m (hchart t)]
      exact congrArg (fun w => opticalTravel w (C.left m) (C.right m) - C.travel m)
        (n08_controlBasis_reference_profile hS href hC m t)
    rw [hd, spaces_angularMean_const]
  have hτ : HasDerivAt τ 1 0 := hC.2.2.2.2.2.2.2.2 m
  have hlin : HasDerivAt (fun t : ℝ => t * A) A 0 := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const A
  have hτ' : HasDerivAt τ 1 ((0 : ℝ) * A) := by simpa only [zero_mul] using hτ
  have hcomp : HasDerivAt (fun t : ℝ => τ (t * A)) A 0 := by
    have hc := hτ'.comp 0 hlin
    change HasDerivAt (fun t : ℝ => τ (t * A)) (1 * A) 0 at hc
    simpa only [one_mul] using hc
  have hBA : B * A = 1 := by
    dsimp only [A, B]
    rw [← Real.rpow_add (n08_materialSample_H_pos hT hN.1.1 m),
      neg_add_cancel, Real.rpow_zero]
  have hf : HasDerivAt f 1 0 := by
    have hformula := (hcomp.sub_const (C.travel m)).const_mul B
    rw [hBA] at hformula
    exact hformula.congr_of_eventuallyEq heq
  have hd : HasDerivAt f (n08CircleDiagonal hS hR (C.referenceState, 0) m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS href hR hzero href.stateSector
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  exact hd.unique hf

end ContinuousFlexibility.Statements
