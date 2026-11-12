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
open scoped ContDiff

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

private theorem coupled_q_defect_values {v E k c w a b q : ℝ}
    (hw : w ≠ 0) (hE : E = 1 + w ^ 2) (hk : k = w + q * a) (hc : c = q * b)
    (hv : v = q * w⁻¹ * (a + (1 + w ^ 2) * b)) :
    v = heightQ E k c / w - 1 := by
  rw [hE, hk, hc, hv]
  exact coupled_q_defect_real hw a b q

private theorem coupled_actualQDefect_decode_raw
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledActualQDefect hT hS hN z) p =
      z.2 * (stateProfile D S C z.1 p.1)⁻¹ *
        (radialPartial (stateU S z.1) p + (1 + stateProfile D S C z.1 p.1 ^ 2) *
          angularPartial (heightAngular (stateU S z.1)) p) := by
  exact (coupledWeakQDefect_decode hN.1.1 hT hS
    (coupledLogProfileLift hT hS hN z.1) z.1.1 z.2 p).trans
      (congrArg (fun l : ℝ => z.2 * (D.w p.1 * Real.exp l)⁻¹ *
        (radialPartial (stateU S z.1) p + (1 + (D.w p.1 * Real.exp l) ^ 2) *
          angularPartial (heightAngular (stateU S z.1)) p))
        (coupledLogProfileLift_decode hT hS hN z.1 p))

theorem coupledActualQDefect_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height coupledWeakProfileWeight).decode (coupledActualQDefect hT hS hN z) p =
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) /
          stateProfile D S C z.1 p.1 - 1 := by
  let hD : IsAccumulatingProfile D := hN.1.1
  have hw : ContDiff ℝ ∞ (stateProfile D S C z.1) :=
    contDiff_stateProfile_of_n01 hS hT hN z.1
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hwp : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  exact coupled_q_defect_values hwp.ne' rfl
    (stateHeight_heightRadial_of_contDiff_profile hT hS hw p)
    (stateHeight_angularPartial_heightAngular_of_contDiff_profile hT hS hw hr)
    (coupled_actualQDefect_decode_raw hT hS hN z p)

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

private theorem coupled_type_coefficient_decode_real {r w l l' d Q v : ℝ}
    (hr : r ≠ 0) (hQ : Q ≠ 0) (hl : l = l') (hd : d = Q / (w * Real.exp l') - 1)
    (hv : v = r⁻¹ * ((Real.exp (-l) * (1 + d)⁻¹ - 1) +
      w ^ 2 * (Real.exp l * (1 + d)⁻¹ - 1))) :
    v = w * ((1 + (w * Real.exp l') ^ 2) / (r * Q)) - (1 + w ^ 2) / r := by
  have hd' : 1 + d = Q / (w * Real.exp l') := by rw [hd]; ring
  rw [hl, Real.exp_neg] at hv
  exact hv.trans (coupled_type_coefficient_real hr (Real.exp_ne_zero l') hQ hd')

private theorem coupled_actualQ_ne_zero
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0 := by
  have hwp : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hN.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hb : (7 / 8 : ℝ) ≤
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) /
          stateProfile D S C z.1 p.1 :=
    (hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp).2.2.1
  exact ((div_pos_iff_of_pos_right hwp).mp
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb)).ne'

/-- The coefficient has the actual normalized type decode on the N01 domain. -/
theorem coupledScalarErrorCoefficient_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height coupledWeakProfileWeight).decode (coupledScalarErrorCoefficient hT hS hN z) p =
      D.w p.1 * residualErrorCoefficient D S C z p - (1 + D.w p.1 ^ 2) / p.1 := by
  have hr : p.1 ≠ 0 := (hN.1.1.choose_spec.1.1.trans hp.1.1).ne'
  exact coupled_type_coefficient_decode_real (r := p.1) (w := D.w p.1) hr
    (coupled_actualQ_ne_zero hN hz hs hp)
    (coupledLogProfileLift_decode hT hS hN z.1 p)
    (coupledActualQDefect_decode hT hS hN z hp)
    (coupledWeakTypeCoefficient_decode hN.1.1 hT hS
      (coupledLogProfileLift hT hS hN z.1) (coupledActualQDefect hT hS hN z) p
      (coupledActualQDefect_small hT hS hN hz hs hp))

end ContinuousFlexibility.Statements
