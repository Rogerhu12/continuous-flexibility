import ContinuousFlexibility.Analysis.CoupledScalarTypeCoefficient
import ContinuousFlexibility.Analysis.CoupledNeighborhoodRestriction

/-!
# The actual normalized coefficient of the coupled scalar error

N01 supplies the logarithmic profile and the normalized denominator bounds.
They identify the weak-height construction with the literal coefficient
`w₀ B - (1 + w₀²) / r`. Its actual directional tower is smooth tame on one
smaller sector neighborhood. No additional coefficient realization is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def coupledActualQDefect
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    CoupledWeakHeight S :=
  coupledWeakQDefect hN.1.1 hT hS (coupledLogProfileLift hT hS hN z.1) z.1.1 z.2

private theorem coupled_q_defect_real {w : ℝ} (hw : w ≠ 0) (a b q : ℝ) :
    q * w⁻¹ * (a + (1 + w ^ 2) * b) =
      (w + q * a + (1 + w ^ 2) * (q * b)) / w - 1 := by
  field_simp [hw]
  ring

theorem coupledActualQDefect_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height coupledWeakProfileWeight).decode (coupledActualQDefect hT hS hN z) p =
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) /
          stateProfile D S C z.1 p.1 - 1 := by
  have hD := hN.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hwp : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hdecoded := coupledWeakQDefect_decode hD hT hS
    (coupledLogProfileLift hT hS hN z.1) z.1.1 z.2 p
  rw [coupledLogProfileLift_decode] at hdecoded
  change (S.height coupledWeakProfileWeight).decode (coupledActualQDefect hT hS hN z) p =
    z.2 * (stateProfile D S C z.1 p.1)⁻¹ *
      (radialPartial (stateU S z.1) p + (1 + stateProfile D S C z.1 p.1 ^ 2) *
        angularPartial (heightAngular (stateU S z.1)) p) at hdecoded
  rw [stateHeight_heightRadial_of_contDiff_profile hT hS hw p,
    stateHeight_angularPartial_heightAngular_of_contDiff_profile hT hS hw hr]
  exact hdecoded.trans (coupled_q_defect_real hwp.ne' _ _ _)

theorem coupledActualQDefect_small
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    |(S.height coupledWeakProfileWeight).decode (coupledActualQDefect hT hS hN z) p| ≤
      1 / 2 := by
  have hb := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  rw [coupledActualQDefect_decode hT hS hN z hp]
  apply abs_le.mpr
  constructor <;> linarith only [hb.2.2.1, hb.2.2.2.1]

def coupledScalarErrorCoefficient
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    CoupledWeakHeight S :=
  coupledWeakTypeCoefficient hN.1.1 hT hS (coupledLogProfileLift hT hS hN z.1)
    (coupledActualQDefect hT hS hN z)

private theorem coupled_type_coefficient_real {r w e Q d : ℝ}
    (hr : r ≠ 0) (he : e ≠ 0) (hQ : Q ≠ 0) (hd : 1 + d = Q / (w * e)) :
    r⁻¹ * ((e⁻¹ * (1 + d)⁻¹ - 1) + w ^ 2 * (e * (1 + d)⁻¹ - 1)) =
      w * ((1 + (w * e) ^ 2) / (r * Q)) - (1 + w ^ 2) / r := by
  rw [hd, inv_div]
  field_simp [hr, he, hQ]
  ring

/-- The coefficient has the actual normalized type decode on the N01 domain. -/
theorem coupledScalarErrorCoefficient_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height coupledWeakProfileWeight).decode (coupledScalarErrorCoefficient hT hS hN z) p =
      D.w p.1 * residualErrorCoefficient D S C z p - (1 + D.w p.1 ^ 2) / p.1 := by
  have hD := hN.1.1
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hwp : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hb := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hQ : heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0 :=
    ((div_pos_iff_of_pos_right hwp).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.2.2.1)).ne'
  have hd : 1 + (S.height coupledWeakProfileWeight).decode (coupledActualQDefect hT hS hN z) p =
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) /
          stateProfile D S C z.1 p.1 := by
    rw [coupledActualQDefect_decode hT hS hN z hp]
    ring
  have hvalue := coupledWeakTypeCoefficient_decode hD hT hS
    (coupledLogProfileLift hT hS hN z.1) (coupledActualQDefect hT hS hN z) p
    (coupledActualQDefect_small hT hS hN hz hs hp)
  rw [coupledLogProfileLift_decode, Real.exp_neg] at hvalue
  exact hvalue.trans (coupled_type_coefficient_real hr
    (Real.exp_ne_zero (coupled_stateLogProfile D S C z.1 p.1)) hQ hd)

end ContinuousFlexibility.Statements
