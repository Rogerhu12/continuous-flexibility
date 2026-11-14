module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Tactic.NormNum

/-!
# Positivity already supplied by the cumulative N03 witness

The radial coefficient is fixed by N03. Its positivity follows from
the actual N01 profile, height-Q and polar-discriminant inequalities,
without a regularity assumption on the stored mixed or angular field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem n04b_through03_radialCoefficient_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (L.coefficients z).a p := by
  have hN01 : N01Properties D T S C base loss ε := h03.1.1
  have hsame : (L.coefficients z).a p = (originalCoefficients D S C z).a p :=
    h03.2.1 z hz hsector p
  rw [hsame]
  obtain ⟨bounds, hbounds⟩ := hN01.1.1
  have hw : 0 < D.w p.1 := hbounds.1.2.2.2.2.1 p.1 hp.1
  have hstatew : 0 < stateProfile D S C z.1 p.1 := by
    change 0 < D.w p.1 * Real.exp _
    exact mul_pos hw (Real.exp_pos _)
  rcases hN01 with ⟨_, _, _, _, _, _, _, _, _, hcoeff, _⟩
  have hb := hcoeff z hz hsector p hp
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hstatew).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.2.2.1)
  have hDisc : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2.2.2.2.1
  change 0 < polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p
  unfold polarLinearA linearRadial polarScale inverseDThreeHalves
  exact mul_pos hQ (one_div_pos.mpr (mul_pos hDisc (Real.sqrt_pos.mpr hDisc)))

end ContinuousFlexibility.Statements
