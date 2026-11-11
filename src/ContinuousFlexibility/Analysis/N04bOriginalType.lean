import ContinuousFlexibility.Analysis.N04bStateProfileType
import ContinuousFlexibility.Scalar.TypeCorrection

/-!
# Strict type of the actual original field on every negative component

The scalar type correction has an exact determinant identity. Its sign
depends on the controlled profile slope and therefore follows from the
N01 flow tower throughout the full state and residual neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.n04b_original_negative_type
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    0 < (originalCoefficients D S C z).a p ∧
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1, hp.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hrpos : 0 < p.1 := hgeom.1.1.trans hpD.1.1
  have hwpos : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hgeom.1.2.2.2.2.1 p.1 hpD.1) (Real.exp_pos _)
  have hcoeff := hN.2.2.2.2.2.2.2.2.2.1 z hz hsector p hpD
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hwpos).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hcoeff.2.2.1)
  have hDisc : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcoeff.2.2.2.2.1
  have hderiv := hN.n04b_stateProfile_deriv_neg hS hT hz.1 m hp
  have hdet := (polar_corrected_determinant_neg_iff (stateHeight D S C z)
    ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) p.1)
    hrpos hwpos hDisc hQ.ne').mpr hderiv
  constructor
  · change 0 < polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p
    unfold polarLinearA linearRadial polarScale inverseDThreeHalves
    exact mul_pos hQ (one_div_pos.mpr (mul_pos hDisc (Real.sqrt_pos.mpr hDisc)))
  · change 0 < polarLinearB (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 -
      polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p *
        polarCorrectedC (stateProfile D S C z.1) (stateHeight D S C z) p
    linarith only [hdet]

end ContinuousFlexibility.Statements
