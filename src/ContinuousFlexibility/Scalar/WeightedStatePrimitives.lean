import ContinuousFlexibility.Scalar.WeightedHeightAlgebra
import ContinuousFlexibility.Scalar.WeightedDifferentiation
import ContinuousFlexibility.Scalar.WeightedAngularDifferentiation
import ContinuousFlexibility.Scalar.WeightedAngularMean
import ContinuousFlexibility.Scalar.WeightedCutoffDerivative
import ContinuousFlexibility.Scalar.WeightedStateJetFormulas

/-!
# Actual linear ingredients of the finite scalar formulas

The state projections, angular mean, radial derivatives and normalized
angular primitives are genuine continuous linear maps in the original
weighted model. Their fixed tame losses are recorded before any nonlinear
state formula is assembled.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def scalarStateProfileProjection (S : PhysicalSpacesData) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S where
  toFun := fun x => x.1.1.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_fst.fst.fst

theorem scalarStateProfileProjection_isTame (S : PhysicalSpacesData) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateProfileProjection S).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  change scalarHeightGrading S s x.1.1.1 ≤ (1 : ℝ) * scalarStateGrading S (s + 0) x
  rw [Nat.add_zero, one_mul, scalarStateGrading_apply]
  have h₁ := apply_nonneg (scalarHeightGrading S s) x.1.1.1
  have h₂ := apply_nonneg (scalarHeightGrading S s) x.1.1.2
  have h₃ := norm_nonneg x.1.2
  have h₄ := norm_nonneg x.2
  linarith only [h₁, h₂, h₃, h₄]

def scalarStateHeightProjection (S : PhysicalSpacesData) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S where
  toFun := fun x => x.1.1.2
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_fst.fst.snd

theorem scalarStateHeightProjection_isTame (S : PhysicalSpacesData) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateHeightProjection S).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  change scalarHeightGrading S s x.1.1.2 ≤ (1 : ℝ) * scalarStateGrading S (s + 0) x
  rw [Nat.add_zero, one_mul, scalarStateGrading_apply]
  have h₁ := apply_nonneg (scalarHeightGrading S s) x.1.1.1
  have h₂ := apply_nonneg (scalarHeightGrading S s) x.1.1.2
  have h₃ := norm_nonneg x.1.2
  have h₄ := norm_nonneg x.2
  linarith only [h₁, h₂, h₃, h₄]

def scalarStateLeftProjection (S : PhysicalSpacesData) :
    ScalarWeightedState S →L[ℝ] ℝ where
  toFun := fun x => x.1.2
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_fst.snd

theorem scalarStateLeftProjection_isTame (S : PhysicalSpacesData) :
    IsTameLinear (scalarStateGrading S) (realGrading)
      (scalarStateLeftProjection S).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  change ‖x.1.2‖ ≤ (1 : ℝ) * scalarStateGrading S (s + 0) x
  rw [Nat.add_zero, one_mul, scalarStateGrading_apply]
  have h₁ := apply_nonneg (scalarHeightGrading S s) x.1.1.1
  have h₂ := apply_nonneg (scalarHeightGrading S s) x.1.1.2
  have h₃ := norm_nonneg x.1.2
  have h₄ := norm_nonneg x.2
  linarith only [h₁, h₂, h₃, h₄]

def scalarStateQProjection (S : PhysicalSpacesData) :
    ScalarWeightedState S →L[ℝ] ℝ where
  toFun := fun x => x.2
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_snd

theorem scalarStateQProjection_isTame (S : PhysicalSpacesData) :
    IsTameLinear (scalarStateGrading S) (realGrading)
      (scalarStateQProjection S).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  change ‖x.2‖ ≤ (1 : ℝ) * scalarStateGrading S (s + 0) x
  rw [Nat.add_zero, one_mul, scalarStateGrading_apply]
  have h₁ := apply_nonneg (scalarHeightGrading S s) x.1.1.1
  have h₂ := apply_nonneg (scalarHeightGrading S s) x.1.1.2
  have h₃ := norm_nonneg x.1.2
  have h₄ := norm_nonneg x.2
  linarith only [h₁, h₂, h₃, h₄]

def scalarStateCutoffCLM
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (scalarCutoffDerivativeHeight hT hS scalarBeta)).comp
    (scalarStateLeftProjection S)

theorem scalarStateCutoffCLM_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateCutoffCLM hT hS).toLinearMap 0 0 := by
  intro s _
  refine ⟨⟨scalarHeightGrading S s (scalarCutoffDerivativeHeight hT hS scalarBeta),
    apply_nonneg _ _⟩, fun x => ?_⟩
  change scalarHeightGrading S s (x.1.2 • scalarCutoffDerivativeHeight hT hS scalarBeta) ≤
    scalarHeightGrading S s (scalarCutoffDerivativeHeight hT hS scalarBeta) *
      scalarStateGrading S (s + 0) x
  rw [map_smul_eq_mul, Nat.add_zero, mul_comm ‖x.1.2‖]
  apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
  rw [scalarStateGrading_apply]
  have h₁ := apply_nonneg (scalarHeightGrading S s) x.1.1.1
  have h₂ := apply_nonneg (scalarHeightGrading S s) x.1.1.2
  have h₄ := norm_nonneg x.2
  linarith only [h₁, h₂, h₄]

def scalarStateMeanCLM
    (_hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.angularMeanCLM hT (hS.1 scalarBeta)).comp (scalarStateProfileProjection S)

def scalarStateRadialCLM
    (_hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.radialCLM hT (hS.1 scalarBeta)).comp (scalarStateHeightProjection S) +
    scalarStateCutoffCLM hT hS

def scalarStateAngularPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvRadiusCLM hD hT hS).comp (scalarStateHeightProjection S)

def scalarStateRadialSecondCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.radialCLM hT (hS.1 scalarBeta)).comp (scalarStateRadialCLM hD hT hS)

def scalarStateAngularRadialPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.radialCLM hT (hS.1 scalarBeta)).comp (scalarStateAngularPrimitiveCLM hD hT hS)

def scalarStateAngularSecondCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)).comp (scalarStateAngularPrimitiveCLM hD hT hS)

def scalarStateMeanDerivCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarWeightedState S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.radialCLM hT (hS.1 scalarBeta)).comp (scalarStateMeanCLM hD hT hS)

theorem scalarStateMeanCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateMeanCLM hD hT hS).toLinearMap 0 0 := by
  exact (SobolevModelData.angularMeanCLM_isTame hT (hS.1 scalarBeta)).comp
    (scalarStateProfileProjection_isTame S)

theorem scalarStateRadialCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateRadialCLM hD hT hS).toLinearMap 2 0 := by
  exact ((SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta)).comp
    (scalarStateHeightProjection_isTame S)).add (scalarStateGrading_monotone S)
      (scalarStateCutoffCLM_isTame hT hS)

theorem scalarStateAngularPrimitiveCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateAngularPrimitiveCLM hD hT hS).toLinearMap 1 0 := by
  exact (scalarReferenceInvRadiusCLM_isTame hD hT hS).comp
    (scalarStateHeightProjection_isTame S)

theorem scalarStateRadialSecondCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateRadialSecondCLM hD hT hS).toLinearMap 4 0 := by
  exact (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta)).comp
    (scalarStateRadialCLM_isTame hD hT hS)

theorem scalarStateAngularRadialPrimitiveCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateAngularRadialPrimitiveCLM hD hT hS).toLinearMap 3 0 := by
  exact (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta)).comp
    (scalarStateAngularPrimitiveCLM_isTame hD hT hS)

theorem scalarStateAngularSecondCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateAngularSecondCLM hD hT hS).toLinearMap 3 0 := by
  exact (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta)).comp
    (scalarStateAngularPrimitiveCLM_isTame hD hT hS)

theorem scalarStateMeanDerivCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateMeanDerivCLM hD hT hS).toLinearMap 2 0 := by
  exact (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta)).comp
    (scalarStateMeanCLM_isTame hD hT hS)

theorem decode_scalarStateMeanCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    (S.height scalarBeta).decode (scalarStateMeanCLM hD hT hS x) =
      fun p => scalarStateProfileMean S x p.1 := by
  exact SobolevModelData.decode_angularMeanCLM hT (hS.1 scalarBeta) x.1.1.1

theorem decode_scalarStateRadialCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    (S.height scalarBeta).decode (scalarStateRadialCLM hD hT hS x) =
      radialPartial (scalarStateIncrement S x) := by
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS x.1.1.2).1
  have hχ := hS.2.2.1.1
  have hχfield := hχ.comp contDiff_fst
  have hsum (p : PolarPoint) :
      radialPartial (scalarStateIncrement S x) p =
        radialPartial ((S.height scalarBeta).decode x.1.1.2) p + x.1.2 * deriv S.chiLeft p.1 := by
    unfold scalarStateIncrement scalarCommonHeightDecode
    rw [radialPartial_add (hf.differentiable (by simp) p)
      ((contDiff_const.mul hχfield).differentiable (by simp) p),
      radialPartial_mul (differentiableAt_const x.1.2) (hχfield.differentiable (by simp) p),
      radialPartial_const, zero_mul, zero_add,
      Radial.radialPartial_radialHeightField (hχ.differentiable (by simp) p.1)]
  change (S.height scalarBeta).decode
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta) x.1.1.2 +
      x.1.2 • scalarCutoffDerivativeHeight hT hS scalarBeta) = _
  rw [map_add, SobolevModelData.decode_radialCLM, map_smul, decode_scalarCutoffDerivativeHeight]
  funext p
  exact (hsum p).symm

theorem decode_scalarStateRadialSecondCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    (S.height scalarBeta).decode (scalarStateRadialSecondCLM hD hT hS x) =
      radialPartial (radialPartial (scalarStateIncrement S x)) := by
  change (S.height scalarBeta).decode
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta) (scalarStateRadialCLM hD hT hS x)) = _
  rw [SobolevModelData.decode_radialCLM, decode_scalarStateRadialCLM]

theorem decode_scalarStateAngularPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarStateAngularPrimitiveCLM hD hT hS x) p =
      p.1⁻¹ * (S.height scalarBeta).decode x.1.1.2 p :=
  decode_scalarReferenceInvRadiusCLM hD hT hS x.1.1.2 p

theorem angularPartial_decode_scalarStateAngularPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    angularPartial ((S.height scalarBeta).decode (scalarStateAngularPrimitiveCLM hD hT hS x)) =
      heightAngular (scalarStateIncrement S x) := by
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS x.1.1.2).1
  have hP := (scalarHeight_decode_contDiff_and_flatJets hT hS
    (scalarStateAngularPrimitiveCLM hD hT hS x)).1
  funext p
  have hleft := Radial.hasDerivAt_angularSlice (hP.differentiable (by simp) p)
  have hright := (hasDerivAt_const p.2 p.1⁻¹).mul
    (Radial.hasDerivAt_angularSlice (hf.differentiable (by simp) p))
  have hslice : (fun θ => (S.height scalarBeta).decode
      (scalarStateAngularPrimitiveCLM hD hT hS x) (p.1, θ)) =
      fun θ => p.1⁻¹ * (S.height scalarBeta).decode x.1.1.2 (p.1, θ) :=
    funext (fun θ => decode_scalarStateAngularPrimitiveCLM hD hT hS x (p.1, θ))
  have hangular : angularPartial ((S.height scalarBeta).decode
      (scalarStateAngularPrimitiveCLM hD hT hS x)) p =
      p.1⁻¹ * angularPartial ((S.height scalarBeta).decode x.1.1.2) p := by
    have he := hleft.deriv
    rw [hslice, hright.deriv] at he
    simpa only [zero_mul, zero_add] using he.symm
  have hχfield := hS.2.2.1.1.comp contDiff_fst
  have hincrement : angularPartial (scalarStateIncrement S x) p =
      angularPartial ((S.height scalarBeta).decode x.1.1.2) p := by
    unfold scalarStateIncrement scalarCommonHeightDecode
    rw [angularPartial_add (hf.differentiable (by simp) p)
      ((contDiff_const.mul hχfield).differentiable (by simp) p),
      angularPartial_mul (differentiableAt_const x.1.2) (hχfield.differentiable (by simp) p),
      angularPartial_const, zero_mul, zero_add,
      Radial.angularPartial_radialHeightField (hS.2.2.1.1.differentiable (by simp) p.1),
      mul_zero, add_zero]
  rw [hangular, heightAngular, hincrement, div_eq_mul_inv, mul_comm]

theorem angularPartial_decode_scalarStateAngularRadialPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    angularPartial ((S.height scalarBeta).decode (scalarStateAngularRadialPrimitiveCLM hD hT hS x)) =
      radialPartial (heightAngular (scalarStateIncrement S x)) := by
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS
    (scalarStateAngularPrimitiveCLM hD hT hS x)).1
  change angularPartial ((S.height scalarBeta).decode
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta) (scalarStateAngularPrimitiveCLM hD hT hS x))) = _
  rw [SobolevModelData.decode_radialCLM,
    ← angularPartial_decode_scalarStateAngularPrimitiveCLM hD hT hS x]
  funext p
  exact (radial_angular_commute (hf.contDiffAt.of_le (by simp))).symm

theorem decode_scalarStateAngularSecondCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    (S.height scalarBeta).decode (scalarStateAngularSecondCLM hD hT hS x) =
      angularPartial (heightAngular (scalarStateIncrement S x)) := by
  change (S.height scalarBeta).decode
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)
      (scalarStateAngularPrimitiveCLM hD hT hS x)) = _
  rw [SobolevModelData.decode_angularSecondCLM,
    angularPartial_decode_scalarStateAngularPrimitiveCLM]

theorem decode_scalarStateMeanDerivCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    (S.height scalarBeta).decode (scalarStateMeanDerivCLM hD hT hS x) =
      fun p => deriv (scalarStateProfileMean S x) p.1 := by
  change (S.height scalarBeta).decode
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta) (scalarStateMeanCLM hD hT hS x)) = _
  rw [SobolevModelData.decode_radialCLM, decode_scalarStateMeanCLM]
  funext p
  exact Radial.radialPartial_radialHeightField
    ((scalarStateProfileMean_contDiff hT hS x).differentiable (by simp) p.1)

end ContinuousFlexibility.Statements
