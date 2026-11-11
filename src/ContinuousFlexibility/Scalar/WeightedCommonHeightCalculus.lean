import ContinuousFlexibility.Scalar.WeightedStatePrimitives

/-!
# Actual linear calculus on the common height domain

The free endpoint constant enters the radial derivative through the actual
cutoff derivative. It has no angular derivative. The reference corrected
coefficient acts through two proved physical radial multiplier maps.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarCommonHeightGrading_apply (S : PhysicalSpacesData) (s : ℕ)
    (u : ScalarCommonHeight S) :
    scalarCommonHeightGrading S s u = scalarHeightGrading S s u.1 + ‖u.2‖ := by
  simp only [scalarCommonHeightGrading, pairGrading, realGrading, add_apply,
    Seminorm.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, coe_normSeminorm]

def scalarCommonDirectionCLM (S : PhysicalSpacesData) :
    ScalarCommonHeight S →L[ℝ] ScalarWeightedState S where
  toFun := scalarHeightDirection S
  map_add' := by intro u v; simp [scalarHeightDirection]
  map_smul' := by intro c u; simp [scalarHeightDirection]
  cont := ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).prodMk continuous_const

theorem scalarCommonDirectionCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarStateGrading S)
      (scalarCommonDirectionCLM S).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun u => ?_⟩
  change scalarStateGrading S s (scalarHeightDirection S u) ≤
    (1 : ℝ) * scalarCommonHeightGrading S (s + 0) u
  rw [Nat.add_zero, one_mul, scalarStateGrading_apply, scalarCommonHeightGrading_apply]
  simp only [scalarHeightDirection, map_zero, norm_zero, zero_add, add_zero, le_refl]

def scalarCommonProjectionCLM (S : PhysicalSpacesData) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  ContinuousLinearMap.fst ℝ _ _

theorem scalarCommonProjectionCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      (scalarCommonProjectionCLM S).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun u => ?_⟩
  change scalarHeightGrading S s u.1 ≤
    (1 : ℝ) * scalarCommonHeightGrading S (s + 0) u
  rw [Nat.add_zero, one_mul, scalarCommonHeightGrading_apply]
  exact le_add_of_nonneg_right (norm_nonneg _)

def scalarCommonRadialCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (scalarStateRadialCLM hD hT hS).comp (scalarCommonDirectionCLM S)

theorem scalarCommonRadialCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      (scalarCommonRadialCLM hD hT hS).toLinearMap 2 0 :=
  (scalarStateRadialCLM_isTame hD hT hS).comp (scalarCommonDirectionCLM_isTame S)

theorem decode_scalarCommonRadialCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarCommonRadialCLM hD hT hS u) =
      radialPartial (scalarCommonHeightDecode S u) := by
  change (S.height scalarBeta).decode
    (scalarStateRadialCLM hD hT hS (scalarHeightDirection S u)) = _
  rw [decode_scalarStateRadialCLM] <;> rfl

theorem scalarCommonHeightDecode_angularPartial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) :
    angularPartial (scalarCommonHeightDecode S u) =
      angularPartial ((S.height scalarBeta).decode u.1) := by
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS u.1).1
  have hχ := hS.2.2.1.1.comp contDiff_fst
  funext p
  unfold scalarCommonHeightDecode
  rw [angularPartial_add (hf.differentiable (by simp) p)
    ((contDiff_const.mul hχ).differentiable (by simp) p),
    angularPartial_mul (differentiableAt_const u.2) (hχ.differentiable (by simp) p),
    angularPartial_const, zero_mul, zero_add,
    Radial.angularPartial_radialHeightField (hS.2.2.1.1.differentiable (by simp) p.1),
    mul_zero, add_zero]

/-- Angular differentiation of a globally smooth radial product only uses
the two smooth fields, and needs no global radial regularity of its multiplier. -/
theorem angularPartial_radialProduct_of_contDiff
    {k : ℝ → ℝ} {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hprod : ContDiff ℝ ∞ (fun p => k p.1 * f p)) :
    angularPartial (fun p => k p.1 * f p) =
      fun p => k p.1 * angularPartial f p := by
  funext p
  have hl : HasDerivAt (fun θ => k p.1 * f (p.1, θ))
      (angularPartial (fun q => k q.1 * f q) p) p.2 := by
    simpa only using! Radial.hasDerivAt_angularSlice
      (hprod.differentiable (by simp) p)
  have hr : HasDerivAt (fun θ => k p.1 * f (p.1, θ))
      (k p.1 * angularPartial f p) p.2 := by
    simpa only using! (Radial.hasDerivAt_angularSlice
      (hf.differentiable (by simp) p)).const_mul (k p.1)
  exact hl.unique hr

def scalarReferenceCorrectedCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvRadiusCLM hD hT hS).comp (scalarReferenceWDerivCLM hD hT hS)

theorem scalarReferenceCorrectedCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceCorrectedCLM hD hT hS).toLinearMap 2 0 :=
  (scalarReferenceInvRadiusCLM_isTame hD hT hS).comp
    (scalarReferenceWDerivCLM_isTame hD hT hS)

theorem decode_scalarReferenceCorrectedCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (scalarReferenceCorrectedCLM hD hT hS u) =
      fun p => (deriv D.w p.1 / p.1) * (S.height scalarBeta).decode u p := by
  funext p
  change (S.height scalarBeta).decode
    (scalarReferenceInvRadiusCLM hD hT hS (scalarReferenceWDerivCLM hD hT hS u)) p = _
  rw [decode_scalarReferenceInvRadiusCLM, decode_scalarReferenceWDerivCLM]
  simp only [div_eq_mul_inv]
  ring

theorem angularPartial_decode_scalarReferenceCorrectedCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) :
    angularPartial ((S.height scalarBeta).decode (scalarReferenceCorrectedCLM hD hT hS u)) =
      fun p => (deriv D.w p.1 / p.1) * angularPartial ((S.height scalarBeta).decode u) p := by
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  have hprod := (scalarHeight_decode_contDiff_and_flatJets hT hS
    (scalarReferenceCorrectedCLM hD hT hS u)).1
  rw [decode_scalarReferenceCorrectedCLM] at hprod ⊢
  exact angularPartial_radialProduct_of_contDiff hf hprod

end ContinuousFlexibility.Statements
