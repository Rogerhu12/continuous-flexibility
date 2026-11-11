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

/-- Abstract map algebra keeps the concrete decoder implementation out of
the tame estimate elaboration. -/
private theorem weightedState_clm_comp_add_zero
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    [IsTopologicalAddGroup G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    (L : F →L[ℝ] G) (P : E →L[ℝ] F) (K : E →L[ℝ] G) {loss : ℕ}
    (hp : Monotone p)
    (hL : IsTameLinear q r L.toLinearMap loss 0)
    (hP : IsTameLinear p q P.toLinearMap 0 0)
    (hK : IsTameLinear p r K.toLinearMap 0 0) :
    IsTameLinear p r (L.comp P + K).toLinearMap loss 0 := by
  have hmap : (L.comp P + K).toLinearMap =
      L.toLinearMap.comp P.toLinearMap + K.toLinearMap := by
    ext x
    rfl
  rw [hmap]
  have hl : max loss 0 = loss := max_eq_left (Nat.zero_le loss)
  simpa only [Nat.add_zero, Nat.zero_add, max_self, hl] using
    ((hL.comp hP).add hp hK)

/-- The cutoff contributes its actual ordinary radial derivative. -/
private theorem weightedState_radialPartial_cutoff
    {f : PolarPoint → ℝ} {k : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) (c : ℝ) :
    radialPartial (fun p => f p + c * k p.1) =
      fun p => radialPartial f p + c * deriv k p.1 := by
  have hkf : ContDiff ℝ ∞ (fun p : PolarPoint => k p.1) := hk.comp contDiff_fst
  funext p
  have hrad : radialPartial (fun q : PolarPoint => k q.1) p = deriv k p.1 :=
    Radial.radialPartial_radialHeightField (hk.differentiable (by simp) p.1)
  rw [radialPartial_add (hf.differentiable (by simp) p)
    ((contDiff_const.mul hkf).differentiable (by simp) p),
    radialPartial_mul (differentiableAt_const c) (hkf.differentiable (by simp) p),
    radialPartial_const, zero_mul, zero_add, hrad]

private theorem weightedState_angularPartial_cutoff
    {f : PolarPoint → ℝ} {k : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) (c : ℝ) :
    angularPartial (fun p => f p + c * k p.1) = angularPartial f := by
  have hkf : ContDiff ℝ ∞ (fun p : PolarPoint => k p.1) := hk.comp contDiff_fst
  funext p
  have hang : angularPartial (fun q : PolarPoint => k q.1) p = 0 :=
    Radial.angularPartial_radialHeightField (hk.differentiable (by simp) p.1)
  rw [angularPartial_add (hf.differentiable (by simp) p)
    ((contDiff_const.mul hkf).differentiable (by simp) p),
    angularPartial_mul (differentiableAt_const c) (hkf.differentiable (by simp) p),
    angularPartial_const, zero_mul, zero_add, hang, mul_zero, add_zero]

/-- An angular slice sees a radial multiplier as a constant, including at
a radius where that multiplier has no ordinary radial derivative. -/
private theorem weightedState_angularPartial_radialProduct
    {f g : PolarPoint → ℝ} {k : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (heq : ∀ p, g p = k p.1 * f p) :
    angularPartial g = fun p => k p.1 * angularPartial f p := by
  funext p
  have hleft := Radial.hasDerivAt_angularSlice (hg.differentiable (by simp) p)
  have hright : HasDerivAt (fun θ => g (p.1, θ))
      (k p.1 * angularPartial f p) p.2 := by
    apply ((Radial.hasDerivAt_angularSlice
      (hf.differentiable (by simp) p)).const_mul (k p.1)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun θ => heq (p.1, θ))
  exact hleft.unique hright

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
  exact weightedState_clm_comp_add_zero
    (p := scalarStateGrading S) (q := scalarHeightGrading S) (r := scalarHeightGrading S)
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta))
    (scalarStateHeightProjection S) (scalarStateCutoffCLM hT hS)
    (scalarStateGrading_monotone S)
    (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta))
    (scalarStateHeightProjection_isTame S) (scalarStateCutoffCLM_isTame hT hS)

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
  have hsum : radialPartial (scalarStateIncrement S x) =
      fun p => radialPartial ((S.height scalarBeta).decode x.1.1.2) p +
        x.1.2 * deriv S.chiLeft p.1 :=
    weightedState_radialPartial_cutoff hf hS.2.2.1.1 x.1.2
  change (S.height scalarBeta).decode
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta) x.1.1.2 +
      x.1.2 • scalarCutoffDerivativeHeight hT hS scalarBeta) = _
  rw [map_add, SobolevModelData.decode_radialCLM, map_smul, decode_scalarCutoffDerivativeHeight]
  funext p
  exact (congrFun hsum p).symm

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
  have hangular : angularPartial ((S.height scalarBeta).decode
      (scalarStateAngularPrimitiveCLM hD hT hS x)) =
      fun p => p.1⁻¹ * angularPartial ((S.height scalarBeta).decode x.1.1.2) p :=
    weightedState_angularPartial_radialProduct hf hP
      (fun p => decode_scalarStateAngularPrimitiveCLM hD hT hS x p)
  have hincrement : angularPartial (scalarStateIncrement S x) =
      angularPartial ((S.height scalarBeta).decode x.1.1.2) :=
    weightedState_angularPartial_cutoff hf hS.2.2.1.1 x.1.2
  funext p
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
