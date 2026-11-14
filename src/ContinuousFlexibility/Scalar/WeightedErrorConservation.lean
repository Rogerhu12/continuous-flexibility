module

public import ContinuousFlexibility.Scalar.WeightedStateRegularity
public import ContinuousFlexibility.Scalar.WeightedStateFlatness
public import ContinuousFlexibility.Scalar.S05StateDerivative

/-!
# Physical source compatibility of the independent correction error

The type coefficient need only be smooth on the open physical annulus.
For each interior radius, the angular flux is smooth and periodic, so its
angular derivative has zero integral.  The radial integral is unchanged
by the two endpoint values.  Thus no extension of the singular type
coefficient across a flat endpoint is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarStateTypeB_periodic
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    Function.Periodic (scalarStateTypeB D S x) (0, Real.pi) := by
  have hz := scalarStateHeight_periodic hS x
  have hp : Function.Periodic (heightAngular (scalarStateHeight D S x)) (0, Real.pi) := by
    intro p
    simp only [heightAngular, periodic_angularPartial hz p, Prod.fst_add, add_zero]
  intro p
  simp only [scalarStateTypeB, polarTypeB, profileEnergy, heightQ, heightRadial,
    Prod.fst_add, add_zero, periodic_radialPartial hz p, periodic_angularPartial hp p]

theorem scalarStateTypeB_contDiffOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) :
    ContDiffOn ℝ ∞ (scalarStateTypeB D S x) (annularOpen D) := by
  have hz := scalarStateHeight_contDiff hD hT hS x
  obtain ⟨hw, _, _, _, _, _, _, _, _, hpositive⟩ := hg
  intro p hp
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hdisc : 0 < polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p :=
    lt_of_lt_of_le (by norm_num) ((hpositive p.1 hp.1).2 p.2).1
  have hQ : heightQ (profileEnergy (scalarStateProfile D S x) p)
      (heightRadial (scalarStateHeight D S x) p)
      (angularPartial (heightAngular (scalarStateHeight D S x)) p) ≠ 0 :=
    (lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) (hpositive p.1 hp.1).1)
      ((hpositive p.1 hp.1).2 p.2).2).ne'
  obtain ⟨_, _, _, _, htype, _⟩ :=
    contDiffAt_heightLinearCoefficients hw.contDiffAt hz.contDiffAt hr hdisc hQ
  exact htype.contDiffWithinAt

/-- The circle integral only uses smoothness on the actual open annulus. -/
theorem integral_angularPartial_eq_zero_of_contDiffOn
    {F : PolarPoint → ℝ} (hF : ContDiffOn ℝ ∞ F (annularOpen D))
    (hFp : Function.Periodic F (0, Real.pi)) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    (∫ θ in (0 : ℝ)..Real.pi, angularPartial F (r, θ)) = 0 := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hat (θ : ℝ) : ContDiffAt ℝ ∞ F (r, θ) :=
    hF.contDiffAt (hU.mem_nhds ⟨hr, mem_univ _⟩)
  have hslice : Continuous (fun θ : ℝ => angularPartial F (r, θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (contDiffAt_angularPartial (hat θ) (m := 0) (by simp)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hperiod : F (r, Real.pi) = F (r, 0) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hFp (r, 0)
  have hderiv (θ : ℝ) : HasDerivAt (fun t : ℝ => F (r, t))
      (angularPartial F (r, θ)) θ := by
    simpa only using! Radial.hasDerivAt_angularSlice ((hat θ).differentiableAt (by simp))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hderiv θ)
    (hslice.intervalIntegrable 0 Real.pi), hperiod, sub_self]

theorem physicalSourceIntegral_angularPartial_eq_zero
    (hab : D.a ≤ D.b) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F (annularOpen D))
    (hFp : Function.Periodic F (0, Real.pi)) :
    physicalSourceIntegral D (angularPartial F) = 0 := by
  unfold physicalSourceIntegral
  calc
    _ = ∫ _ in D.a..D.b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro r hr
      dsimp only
      rw [angularMean, integral_angularPartial_eq_zero_of_contDiffOn hF hFp hr, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

theorem scalarCorrectionError_physicalSourceIntegral_eq_zero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) (R : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    physicalSourceIntegral D
      (scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
        (scalarCommonHeightDecode S u)) = 0 := by
  let flux : PolarPoint → ℝ := fun p => scalarStateTypeB D S x p *
    (S.height scalarBeta).decode R p * angularPartial (scalarCommonHeightDecode S u) p
  have hR := (scalarHeight_decode_contDiff_and_flatJets hT hS R).1
  have hu := scalarCommonHeightDecode_contDiff hT hS u
  have hut : ContDiff ℝ ∞ (angularPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hu.contDiffAt (by simp)
  have hflux : ContDiffOn ℝ ∞ flux (annularOpen D) :=
    ((scalarStateTypeB_contDiffOn hD hT hS hg).mul hR.contDiffOn).mul hut.contDiffOn
  have hRp := ((hS.1 scalarBeta).2.2.2.1 R).2.2.1
  have hperiod : Function.Periodic flux (0, Real.pi) := by
    intro p
    simp only [flux, scalarStateTypeB_periodic hS x p, hRp p,
      periodic_angularPartial (scalarCommonHeightDecode_periodic hS u) p]
  exact physicalSourceIntegral_angularPartial_eq_zero hD.choose_spec.1.2.1.le hflux hperiod

theorem scalarCorrectionError_compatible_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) (R : ScalarHeightSpace S) (u : ScalarCommonHeight S)
    (f : ScalarHeightSpace S)
    (hf : ∀ p, (S.height scalarBeta).decode f p =
      scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
        (scalarCommonHeightDecode S u) p) : S.Q f = 0 := by
  have hQ : S.Q f = physicalSourceIntegral D ((S.height scalarBeta).decode f) := by
    rcases hS with ⟨_, _, _, _, _, _, _, hQ, _⟩
    exact hQ f
  rw [hQ, funext hf]
  exact scalarCorrectionError_physicalSourceIntegral_eq_zero hD hT hS hg R u

theorem weightedScalar_error_conservation_clause
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (W : WeightedScalarData S)
    {U : Set (ScalarWeightedState S)} (hgeometry : ∀ x ∈ U, ScalarStateGeometry D S x)
    (herror : ∀ x ∈ U, ∀ R u p,
      (S.height scalarBeta).decode (W.error x R u) p =
        scalarCorrectionError (scalarStateTypeB D S x) ((S.height scalarBeta).decode R)
          (scalarCommonHeightDecode S u) p) :
    ∀ x ∈ U, ∀ R u, S.Q (W.error x R u) = 0 := by
  intro x hx R u
  exact scalarCorrectionError_compatible_of_decode hD hT hS (hgeometry x hx) R u
    (W.error x R u) (herror x hx R u)

end ContinuousFlexibility.Statements
