module

public import ContinuousFlexibility.Scalar.WeightedStatePrimitives
public import ContinuousFlexibility.Scalar.WeightedFieldRegularity

/-!
# Global finite-jet identities and the actual exterior coefficient values

The even angular primitive supplies smoothness of the normalized angular
jet also at radius zero. This removes the coordinate restriction from the
finite jet formulas. All actual coefficients vanish outside the annulus by
the actual decoded first and second derivatives of the increment.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
theorem scalarStateIncrement_heightAngular_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) :
    ContDiff ℝ ∞ (heightAngular (scalarStateIncrement S x)) := by
  rw [← angularPartial_decode_scalarStateAngularPrimitiveCLM hD hT hS x]
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS
    (scalarStateAngularPrimitiveCLM hD hT hS x)).1
  exact contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hf.contDiffAt (by simp)

theorem scalarStateHeight_radialPartial_heightAngular_global
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    radialPartial (heightAngular (scalarStateHeight D S x)) p =
      x.2 * radialPartial (heightAngular (scalarStateIncrement S x)) p := by
  have he : heightAngular (scalarStateHeight D S x) =
      fun q => x.2 * heightAngular (scalarStateIncrement S x) q :=
    funext (scalarStateHeight_heightAngular hD hT hS x)
  rw [he, radialPartial_mul (differentiableAt_const x.2)
    ((scalarStateIncrement_heightAngular_contDiff hD hT hS x).differentiable (by simp) p),
    radialPartial_const, zero_mul, zero_add]

theorem scalarStateHeight_angularPartial_heightAngular_global
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    angularPartial (heightAngular (scalarStateHeight D S x)) p =
      x.2 * angularPartial (heightAngular (scalarStateIncrement S x)) p := by
  have he : heightAngular (scalarStateHeight D S x) =
      fun q => x.2 * heightAngular (scalarStateIncrement S x) q :=
    funext (scalarStateHeight_heightAngular hD hT hS x)
  rw [he, angularPartial_mul (differentiableAt_const x.2)
    ((scalarStateIncrement_heightAngular_contDiff hD hT hS x).differentiable (by simp) p),
    angularPartial_const, zero_mul, zero_add]

theorem scalarStateHeight_radialPartial_heightRadial_global
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    radialPartial (heightRadial (scalarStateHeight D S x)) p =
      deriv (scalarStateProfile D S x) p.1 +
        x.2 * radialPartial (radialPartial (scalarStateIncrement S x)) p := by
  have he : heightRadial (scalarStateHeight D S x) = fun q =>
      scalarStateProfile D S x q.1 + x.2 * radialPartial (scalarStateIncrement S x) q :=
    funext (scalarStateHeight_heightRadial hD hT hS x)
  have hw := scalarStateProfile_contDiff hD hT hS x
  have hu : ContDiff ℝ ∞ (radialPartial (scalarStateIncrement S x)) :=
    contDiff_iff_contDiffAt.mpr fun p =>
      contDiffAt_radialPartial (scalarStateIncrement_contDiff hT hS x).contDiffAt (by simp)
  have hwfield : ContDiff ℝ ∞ (fun q : PolarPoint => scalarStateProfile D S x q.1) :=
    hw.comp contDiff_fst
  have huscaled : ContDiff ℝ ∞
      (fun q : PolarPoint => x.2 * radialPartial (scalarStateIncrement S x) q) :=
    contDiff_const.mul hu
  have hwr : radialPartial (fun q : PolarPoint => scalarStateProfile D S x q.1) p =
      deriv (scalarStateProfile D S x) p.1 := by
    change radialPartial (Radial.radialHeightField (scalarStateProfile D S x)) p = _
    exact Radial.radialPartial_radialHeightField (hw.differentiable (by simp) p.1)
  rw [he, radialPartial_add (hwfield.differentiable (by simp) p)
    (huscaled.differentiable (by simp) p),
    radialPartial_mul (differentiableAt_const x.2) (hu.differentiable (by simp) p),
    radialPartial_const, zero_mul, zero_add, hwr]

theorem scalarJetComponent_eq_finiteFormula_global
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (i : Fin 7) (p : PolarPoint) :
    scalarJetComponent D S x i p = scalarJetFiniteFormula D S x i p := by
  have hk := scalarStateHeight_heightRadial hD hT hS x p
  have hp := scalarStateHeight_heightAngular hD hT hS x p
  have hpr := scalarStateHeight_radialPartial_heightAngular_global hD hT hS x p
  have hpt := scalarStateHeight_angularPartial_heightAngular_global hD hT hS x p
  have hd := scalarState_discriminant_eq_one_add_defect hD hT hS x p
  have hw := scalarStateProfile_eq_mean (D := D) x p.1
  fin_cases i <;> simp only [scalarJetComponent, scalarJetFiniteFormula]
  · rw [hk]
    ring
  · exact hp
  · simp only [heightCoframeOne, coframeAField, coframeAValue]
    change Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p) /
      Real.sqrt (1 - heightAngular (scalarStateHeight D S x) p ^ 2) - 1 = _
    rw [hd, hp]
  · simp only [heightCoframeTwo, coframeBField, coframeBValue]
    rw [hk, hp, hw]
  · simp only [heightCoframeTwo, coframeCField, coframeCValue]
    rw [hp]
    ring
  · simp only [heightConnectionForm, connectionRadialField, connectionRadialValue, connectionB1]
    change heightRadial (scalarStateHeight D S x) p /
      ((1 - heightAngular (scalarStateHeight D S x) p ^ 2) *
        Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p)) *
      radialPartial (heightAngular (scalarStateHeight D S x)) p = _
    rw [hd, hk, hp, hpr, hw]
  · simp only [heightConnectionForm, connectionAngularField, connectionAngularValue,
      connectionInverseRoot, connectionB1]
    change (1 / Real.sqrt
      (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p) +
      heightRadial (scalarStateHeight D S x) p /
        ((1 - heightAngular (scalarStateHeight D S x) p ^ 2) *
          Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p)) *
      angularPartial (heightAngular (scalarStateHeight D S x)) p) - 1 = _
    rw [hd, hk, hp, hpt, hw]
    ring


theorem scalarHeight_angularPartial_eq_zero_outside
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) {p : PolarPoint} (hp : p ∉ annularOpen D) :
    angularPartial ((S.height scalarBeta).decode u) p = 0 := by
  simpa only [scalarFieldDecode, map_zero, Pi.zero_apply, zero_add] using
    scalarFieldDecode_eq_zero_outside hT hS (0, u) hp

theorem scalarStateCoefficients_eq_zero_outside
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hp : p ∉ annularOpen D) :
    scalarStateA D S x p = 0 ∧ scalarStateB D S x p = 0 ∧
      scalarStateCorrectedC D S x p = 0 := by
  have hr : p.1 ≤ D.a ∨ D.b ≤ p.1 := by
    by_contra h
    have ha : D.a < p.1 := lt_of_not_ge (fun ha => h (Or.inl ha))
    have hb : p.1 < D.b := lt_of_not_ge (fun hb => h (Or.inr hb))
    exact hp ⟨⟨ha, hb⟩, mem_univ _⟩
  have hw := scalarStateProfile_eq_zero_outside (S := S) hD x hr
  have hw' : deriv (scalarStateProfile D S x) p.1 = 0 := by
    simpa only [iteratedDeriv_one] using
      ((scalarStateProfile_endpointFlat hD hT hS x).iteratedDeriv 1).2 p.1 hr
  have hu : radialPartial (scalarStateIncrement S x) p = 0 := by
    rw [← decode_scalarStateRadialCLM hD hT hS x]
    exact scalarHeight_decode_eq_zero_outside hS _ hp
  have huu : radialPartial (radialPartial (scalarStateIncrement S x)) p = 0 := by
    rw [← decode_scalarStateRadialSecondCLM hD hT hS x]
    exact scalarHeight_decode_eq_zero_outside hS _ hp
  have hut : radialPartial (heightAngular (scalarStateIncrement S x)) p = 0 := by
    rw [← angularPartial_decode_scalarStateAngularRadialPrimitiveCLM hD hT hS x]
    exact scalarHeight_angularPartial_eq_zero_outside hT hS _ hp
  have htt : angularPartial (heightAngular (scalarStateIncrement S x)) p = 0 := by
    rw [← decode_scalarStateAngularSecondCLM hD hT hS x]
    exact scalarHeight_decode_eq_zero_outside hS _ hp
  have hk : heightRadial (scalarStateHeight D S x) p = 0 := by
    rw [scalarStateHeight_heightRadial hD hT hS x p, hw, hu, mul_zero, add_zero]
  have hkr : radialPartial (heightRadial (scalarStateHeight D S x)) p = 0 := by
    rw [scalarStateHeight_radialPartial_heightRadial_global hD hT hS x p,
      hw', huu, mul_zero, add_zero]
  have hpr : radialPartial (heightAngular (scalarStateHeight D S x)) p = 0 := by
    rw [scalarStateHeight_radialPartial_heightAngular_global hD hT hS x p, hut, mul_zero]
  have hpt : angularPartial (heightAngular (scalarStateHeight D S x)) p = 0 := by
    rw [scalarStateHeight_angularPartial_heightAngular_global hD hT hS x p, htt, mul_zero]
  constructor
  · simp only [scalarStateA, polarLinearA, linearRadial, heightQ, hk, hpt,
      mul_zero, zero_add, zero_mul]
  constructor
  · simp only [scalarStateB, polarLinearB, linearMixed, hpr, mul_zero, zero_mul]
  · simp only [scalarStateCorrectedC, polarCorrectedC, correctedAngular, linearAngular,
      hk, hkr, hpt, heightQ, mul_zero, zero_mul, sub_zero, add_zero,
      zero_div, div_zero]

theorem scalarCoefficientComponent_eq_zero_outside
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (i : Fin 3) {p : PolarPoint} (hp : p ∉ annularOpen D) :
    scalarCoefficientComponent D S x i p = 0 := by
  have hr : p.1 ≤ D.a ∨ D.b ≤ p.1 := by
    by_contra h
    have ha : D.a < p.1 := lt_of_not_ge (fun ha => h (Or.inl ha))
    have hb : p.1 < D.b := lt_of_not_ge (fun hb => h (Or.inr hb))
    exact hp ⟨⟨ha, hb⟩, mem_univ _⟩
  obtain ⟨B, hB⟩ := hD
  have hw := hB.1.2.2.1.2 p.1 hr
  have hw' : deriv D.w p.1 = 0 := by
    simpa only [iteratedDeriv_one] using (hB.1.2.2.1.iteratedDeriv 1).2 p.1 hr
  obtain ⟨hA, hC, hK⟩ := scalarStateCoefficients_eq_zero_outside ⟨B, hB⟩ hT hS x hp
  fin_cases i <;>
    simp only [scalarCoefficientComponent, hA, hC, hK, hw, hw', zero_div, sub_zero]

end ContinuousFlexibility.Statements
