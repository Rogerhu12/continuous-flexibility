import ContinuousFlexibility.Scalar.WeightedCandidateFieldDecoding
import ContinuousFlexibility.Scalar.WeightedGlobalStateJets

/-!
# Exact global decoders of the concrete scalar candidates

All seven jet outputs, the removable residual, and the three coefficient
differences are identified with the frozen physical expressions. The type
perturbation has its required identity on the open annulus, where it is
subsequently multiplied by an actual supported source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)

theorem scalarFieldDecode_even (S : PhysicalSpacesData) (u : ScalarHeightSpace S) (p : PolarPoint) :
    scalarFieldDecode S (u, 0) p = (S.height scalarBeta).decode u p := by
  simp only [scalarFieldDecode, angularPartial_decode_height_zero, add_zero]

theorem scalarFieldDecode_odd (S : PhysicalSpacesData) (u : ScalarHeightSpace S) (p : PolarPoint) :
    scalarFieldDecode S (0, u) p = angularPartial ((S.height scalarBeta).decode u) p := by
  simp only [scalarFieldDecode, map_zero, Pi.zero_apply, zero_add]

theorem decode_scalarJetCoframeRadialHeight_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarJetCoframeRadialHeight hD hT hS x) p =
      scalarJetFiniteFormula D S x 2 p := by
  simp only [scalarJetCoframeRadialHeight, decode_scalarHeightUnitalMul,
    decode_scalarStateDPower_half hD hT hS x hb,
    decode_scalarStateAngularPower_neg_half hD hT hS x hb,
    scalarJetFiniteFormula, div_eq_mul_inv]
  ring

theorem angularPartial_decode_scalarJetCoframeMixedPrimitive_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarJetCoframeMixedPrimitive hD hT hS x)) p =
      scalarJetFiniteFormula D S x 3 p := by
  simp only [scalarJetCoframeMixedPrimitive, angularPartial_decode_height_neg,
    angularPartial_decode_scalarHeightOddUnitalAct,
    decode_scalarStateAngularPower_neg_half hD hT hS x hb,
    angularPartial_decode_scalarStateSlopeOddAct,
    angularPartial_decode_scalarStateAngularPrimitive,
    scalarJetFiniteFormula, scalarStateProfile_eq_mean, div_eq_mul_inv]
  ring

theorem decode_scalarJetCoframeAngularHeight_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarJetCoframeAngularHeight hD hT hS x) p =
      scalarJetFiniteFormula D S x 4 p := by
  simp only [scalarJetCoframeAngularHeight, decode_scalarReferenceRadiusCLM,
    decode_scalarStateAngularPower_half hD hT hS x hb, scalarJetFiniteFormula]

theorem angularPartial_decode_scalarJetConnectionRadialPrimitive_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarJetConnectionRadialPrimitive hD hT hS x)) p =
      scalarJetFiniteFormula D S x 5 p := by
  simp only [scalarJetConnectionRadialPrimitive, angularPartial_decode_scalarHeightOddUnitalAct,
    decode_scalarStateConnectionFactor hD hT hS x hb,
    angularPartial_decode_scalarStateSlopeOddAct,
    angularPartial_decode_scalarStateMixedPrimitive,
    scalarJetFiniteFormula, scalarStateProfile_eq_mean, div_eq_mul_inv, mul_inv_rev]
  ring

theorem decode_scalarJetConnectionAngularHeight_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarJetConnectionAngularHeight hD hT hS x) p =
      scalarJetFiniteFormula D S x 6 p := by
  simp only [scalarJetConnectionAngularHeight, map_add, Pi.add_apply,
    decode_scalarStateDPower_neg_half hD hT hS x hb,
    decode_scalarHeightUnitalAct, decode_scalarStateConnectionFactor hD hT hS x hb,
    decode_scalarStateSlopeAct, decode_scalarStateAngularHeight,
    scalarJetFiniteFormula, scalarStateProfile_eq_mean, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem decode_scalarCandidateJets_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (i : Fin 7) (p : PolarPoint) :
    scalarFieldDecode S (scalarCandidateJets hD hT hS x i) p =
      scalarJetFiniteFormula D S x i p := by
  fin_cases i <;> simp only [scalarCandidateJets, Matrix.cons_val_zero, Matrix.cons_val_succ,
    scalarFieldDecode_even, scalarFieldDecode_odd]
  · simpa only [scalarJetFiniteFormula] using decode_scalarStateRadialHeight hD hT hS x p
  · simpa only [scalarJetFiniteFormula] using
      angularPartial_decode_scalarStateAngularPrimitive hD hT hS x p
  · exact decode_scalarJetCoframeRadialHeight_finite hD hT hS x hb p
  · exact angularPartial_decode_scalarJetCoframeMixedPrimitive_finite hD hT hS x hb p
  · exact decode_scalarJetCoframeAngularHeight_finite hD hT hS x hb p
  · exact angularPartial_decode_scalarJetConnectionRadialPrimitive_finite hD hT hS x hb p
  · exact decode_scalarJetConnectionAngularHeight_finite hD hT hS x hb p

theorem decode_scalarCandidateJets
    (hb : ScalarCandidatePowerBounds hD hT hS x) (i : Fin 7) (p : PolarPoint) :
    scalarFieldDecode S (scalarCandidateJets hD hT hS x i) p =
      scalarJetComponent D S x i p :=
  (decode_scalarCandidateJets_finite hD hT hS x hb i p).trans
    (scalarJetComponent_eq_finiteFormula_global hD hT hS x i p).symm

theorem decode_scalarCandidateCoefficients_finite
    (hb : ScalarCandidatePowerBounds hD hT hS x) (i : Fin 3) (p : PolarPoint) :
    scalarFieldDecode S (scalarCandidateCoefficients hD hT hS x i) p =
      scalarCoefficientFiniteFormula D S x i p := by
  fin_cases i <;> simp only [scalarCandidateCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ,
    scalarFieldDecode_even, scalarFieldDecode_odd]
  · exact decode_scalarCoefficientAHeight_finite hD hT hS x hb p
  · exact angularPartial_decode_scalarCoefficientBPrimitive_finite hD hT hS x hb p
  · exact decode_scalarCoefficientCHeight_finite hD hT hS x hb p

theorem decode_scalarCandidateCoefficients
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x)
    (i : Fin 3) (p : PolarPoint) :
    scalarFieldDecode S (scalarCandidateCoefficients hD hT hS x i) p =
      scalarCoefficientComponent D S x i p := by
  by_cases hp : p ∈ annularOpen D
  · exact (decode_scalarCandidateCoefficients_finite hD hT hS x hb i p).trans
      (scalarCoefficientComponent_eq_finiteFormula hD hT hS x hg i hp).symm
  · rw [scalarFieldDecode_eq_zero_outside hT hS _ hp,
      scalarCoefficientComponent_eq_zero_outside hD hT hS x i hp]

theorem decode_scalarCoefficientAHeight
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCoefficientAHeight hD hT hS x) p =
      scalarStateA D S x p - D.w p.1 := by
  simpa only [scalarCandidateCoefficients, Matrix.cons_val_zero, scalarFieldDecode_even,
    scalarCoefficientComponent] using decode_scalarCandidateCoefficients hD hT hS x hb hg 0 p

theorem angularPartial_decode_scalarCoefficientBPrimitive
    (hb : ScalarCandidatePowerBounds hD hT hS x)
    (hg : ScalarStateGeometry D S x) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarCoefficientBPrimitive hD hT hS x)) p =
      scalarStateB D S x p := by
  simpa only [scalarCandidateCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ,
    scalarFieldDecode_odd, scalarCoefficientComponent] using
    decode_scalarCandidateCoefficients hD hT hS x hb hg 1 p

theorem decode_scalarCoefficientCHeight
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCoefficientCHeight hD hT hS x) p =
      scalarStateCorrectedC D S x p - deriv D.w p.1 / p.1 := by
  simpa only [scalarCandidateCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ,
    scalarFieldDecode_even, scalarCoefficientComponent] using
    decode_scalarCandidateCoefficients hD hT hS x hb hg 2 p

theorem decode_scalarCandidateResidual
    (hb : ScalarCandidatePowerBounds hD hT hS x) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarCandidateResidual hD hT hS x) p =
      scalarStateResidual D S x p := by
  by_cases hr : p.1 = 0
  · have hp : p ∉ annularOpen D := by
      intro hp
      have ha : 0 < D.a := hD.choose_spec.1.1
      have hpos := ha.trans hp.1.1
      rw [hr] at hpos
      exact (lt_irrefl 0) hpos
    rw [scalarHeight_decode_eq_zero_outside hS _ hp, scalarStateResidual_eq_zero_at_origin x hr]
  · exact (decode_scalarCandidateResidual_finite hD hT hS x hb p).trans
      (scalarStateResidual_eq_finiteFormula hD hT hS x hr).symm

theorem decode_scalarTypePerturbationHeight
    (hb : ScalarCandidatePowerBounds hD hT hS x) (hg : ScalarStateGeometry D S x)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height scalarBeta).decode (scalarTypePerturbationHeight hD hT hS x) p =
      D.w p.1 * scalarStateTypeB D S x p - (1 + D.w p.1 ^ 2) / p.1 := by
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hwref : D.w p.1 ≠ 0 := (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1).ne'
  have hdata := hg
  obtain ⟨_, _, _, _, _, _, _, _, _, hgeometry⟩ := hdata
  have hw : scalarStateProfile D S x p.1 ≠ 0 := (hgeometry p.1 hp.1).1.ne'
  have ht : D.w p.1 * scalarStateTypeB D S x p =
      (1 + D.w p.1 ^ 2 * (1 + scalarStateProfileMean S x p.1) ^ 2) / p.1 *
        (1 + scalarStateProfileMean S x p.1)⁻¹ *
          (1 + scalarStateQDefect D S x p)⁻¹ := by
    rw [scalarStateTypeB_eq_finiteFormula hD hT hS x hr hw]
    calc
      _ = (D.w p.1 * (D.w p.1)⁻¹) *
          ((1 + D.w p.1 ^ 2 * (1 + scalarStateProfileMean S x p.1) ^ 2) / p.1 *
            (1 + scalarStateProfileMean S x p.1)⁻¹ *
              (1 + scalarStateQDefect D S x p)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hwref, one_mul]
  rw [ht]
  simp only [scalarTypePerturbationHeight, decode_scalarReferenceInvRadiusCLM,
    map_add, Pi.add_apply, decode_scalarReferenceWCLM, decode_scalarHeightUnitalMul,
    decode_scalarStateInverseMeanHeight hD hT hS x hb,
    decode_scalarStateQPower_neg_one hD hT hS x hb, decode_scalarStateMeanSquare,
    div_eq_mul_inv]
  ring

end ContinuousFlexibility.Statements
