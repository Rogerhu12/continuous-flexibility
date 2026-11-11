import ContinuousFlexibility.Scalar.WeightedStateJetFormulas

/-!
# Reference-separated formulas for the three scalar coefficients

Every coefficient difference is written using the fixed reference functions,
the profile mean and its first radial derivative, the mixed height jet, and
smooth functions of the normalized discriminant and `Q/w` defects. The type
coefficient is factored on the open annulus, without extending it by itself.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

def scalarCoefficientFiniteFormula (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (i : Fin 3) (p : PolarPoint) : ℝ :=
  let w := D.w p.1
  let m := scalarStateProfileMean S x p.1
  let m' := deriv (scalarStateProfileMean S x) p.1
  let c := x.2 * radialPartial (heightAngular (scalarStateIncrement S x)) p
  let d := scalarStateDDefect D S x p
  let h := scalarStateQDefect D S x p
  let t := inverseDThreeHalves (1 + d)
  let σ := (1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹
  match i.val with
  | 0 => w * ((1 + m) * (1 + h) * t - 1)
  | 1 => -(1 + w ^ 2 * (1 + m) ^ 2) * c * t
  | _ => (deriv D.w p.1 / p.1) * ((1 + m) * σ - 1) +
      (w / p.1) * m' * σ +
      (w⁻¹ + 2 * w * (1 + m) ^ 2 + w ^ 3 * (1 + m) ^ 4) * c ^ 2 *
        (1 + m)⁻¹ * (1 + h)⁻¹ * t

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The only possibly singular factor of the type coefficient is the fixed
reference reciprocal; both state denominators are normalized near one. -/
theorem scalarStateTypeB_eq_finiteFormula
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0)
    (hw : scalarStateProfile D S x p.1 ≠ 0) :
    scalarStateTypeB D S x p =
      (1 + (D.w p.1) ^ 2 * (1 + scalarStateProfileMean S x p.1) ^ 2) / p.1 *
        (D.w p.1)⁻¹ * (1 + scalarStateProfileMean S x p.1)⁻¹ *
          (1 + scalarStateQDefect D S x p)⁻¹ := by
  unfold scalarStateTypeB polarTypeB
  rw [scalarState_Q_eq_profile_mul_one_add_defect hD hT hS x hr hw]
  simp only [profileEnergy, radialEnergy, scalarStateProfile_eq_mean,
    mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The frozen coefficient outputs have these reference-separated formulas
at every interior point of every actual geometric state. -/
theorem scalarCoefficientComponent_eq_finiteFormula
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (hg : ScalarStateGeometry D S x)
    (i : Fin 3) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    scalarCoefficientComponent D S x i p = scalarCoefficientFiniteFormula D S x i p := by
  have hdata := hD
  obtain ⟨_, hdata⟩ := hdata
  have hr : p.1 ≠ 0 := (hdata.1.1.trans hp.1.1).ne'
  rcases hg with ⟨hw, _, _, _, _, _, _, _, _, hgeometry⟩
  have hgeometry := hgeometry p.1 hp.1
  have hwp := hgeometry.1.ne'
  have hdisc : 0 < polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p :=
    lt_of_lt_of_le (by norm_num) (hgeometry.2 p.2).1
  have hQ : heightQ (profileEnergy (scalarStateProfile D S x) p)
      (heightRadial (scalarStateHeight D S x) p)
      (angularPartial (heightAngular (scalarStateHeight D S x)) p) ≠ 0 :=
    (lt_of_lt_of_le (mul_pos (by norm_num) hgeometry.1) (hgeometry.2 p.2).2).ne'
  have hd := scalarState_discriminant_eq_one_add_defect hD hT hS x p
  have hq := scalarState_Q_eq_profile_mul_one_add_defect hD hT hS x hr hwp
  have hpr := scalarStateHeight_radialPartial_heightAngular hD hT hS x hr
  have hmean := scalarStateProfile_eq_mean (D := D) x p.1
  have hQratio : heightQ (profileEnergy (scalarStateProfile D S x) p)
      (heightRadial (scalarStateHeight D S x) p)
      (angularPartial (heightAngular (scalarStateHeight D S x)) p) /
      scalarStateProfile D S x p.1 = 1 + scalarStateQDefect D S x p := by
    rw [hq]
    field_simp [hwp]
  have hprod : D.w p.1 * (1 + scalarStateProfileMean S x p.1) ≠ 0 := by
    rwa [hmean] at hwp
  have hwref : D.w p.1 ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hm : 1 + scalarStateProfileMean S x p.1 ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hE : (profileEnergy (scalarStateProfile D S x) p) ^ 2 /
      scalarStateProfile D S x p.1 =
      ((D.w p.1)⁻¹ + 2 * D.w p.1 * (1 + scalarStateProfileMean S x p.1) ^ 2 +
        D.w p.1 ^ 3 * (1 + scalarStateProfileMean S x p.1) ^ 4) *
          (1 + scalarStateProfileMean S x p.1)⁻¹ := by
    simp only [profileEnergy, radialEnergy, hmean]
    field_simp [hwref, hm]
    <;> ring
  have hderiv : deriv (scalarStateProfile D S x) p.1 / p.1 =
      (deriv D.w p.1 / p.1) * (1 + scalarStateProfileMean S x p.1) +
        (D.w p.1 / p.1) * deriv (scalarStateProfileMean S x) p.1 := by
    rw [scalarStateProfile_deriv_expansion hD hT hS x p.1]
    ring
  fin_cases i <;> simp only [scalarCoefficientComponent, scalarCoefficientFiniteFormula]
  · unfold scalarStateA polarLinearA linearRadial polarScale
    rw [hq, hd, hmean]
    ring
  · unfold scalarStateB polarLinearB linearMixed polarScale
    rw [hpr, hd]
    simp only [profileEnergy, radialEnergy, hmean, mul_pow]
  · rw [scalarStateCorrectedC,
      polarCorrectedC_eq_normalized_profile (hw.differentiable (by simp) p.1) hr hwp hdisc hQ,
      hE, hQratio, hd, hpr, hderiv]
    ring

end ContinuousFlexibility.Statements
