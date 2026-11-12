import ContinuousFlexibility.Analysis.N01cSectorProjection
import ContinuousFlexibility.Blueprint.Statements

/-!
# Actual coefficient denominators on the full N01 neighbourhood

The sector projection preserves the profile and height and contracts all
state seminorms. Consequently the denominator bounds supplied by N01b hold
on its entire neighbourhood, with the same base and radius. These are
bounds for the actual scalar formulas; no differentiability or tame bound
is added as a hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- N01b's exact six geometric inequalities hold for every state, not only
for states in the symmetry sector. -/
theorem n01PartB_denominator_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (1 / 2 : ℝ) ≤ stateProfile D S C z.1 p.1 / D.w p.1 ∧
    stateProfile D S C z.1 p.1 / D.w p.1 ≤ 2 ∧
    (7 / 8 : ℝ) ≤ heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ∧
    heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ≤ (9 / 8 : ℝ) ∧
    (1 / 2 : ℝ) ≤ polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
    polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ≤ (3 / 2 : ℝ) := by
  let P : (ℝ → ℝ) → (PolarPoint → ℝ) → Prop := fun w h =>
    (1 / 2 : ℝ) ≤ w p.1 / D.w p.1 ∧ w p.1 / D.w p.1 ≤ 2 ∧
    (7 / 8 : ℝ) ≤ heightQ (profileEnergy w p) (heightRadial h p)
      (angularPartial (heightAngular h) p) / w p.1 ∧
    heightQ (profileEnergy w p) (heightRadial h p)
      (angularPartial (heightAngular h) p) / w p.1 ≤ (9 / 8 : ℝ) ∧
    (1 / 2 : ℝ) ≤ polarDiscriminant w h p ∧
      polarDiscriminant w h p ≤ (3 / 2 : ℝ)
  exact stateGeometry_property_of_sector hS href P
    (fun y hy hsector => hB.2.2.2.1 y hy hsector p hp) z hz

/-- The actual profile, curvature denominator and discriminant are
positive throughout that same full neighbourhood. -/
theorem n01PartB_denominators_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < stateProfile D S C z.1 p.1 ∧
    0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ∧
    0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hb := n01PartB_denominator_bounds hS href hB hz hp
  have hw₀ : 0 < D.w p.1 := hD.2.2.2.2.1 p.1 hp.1
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    (div_pos_iff_of_pos_right hw₀).mp (lt_of_lt_of_le (by norm_num) hb.1)
  refine ⟨hw, ?_, lt_of_lt_of_le (by norm_num) hb.2.2.2.2.1⟩
  exact (div_pos_iff_of_pos_right hw).mp (lt_of_lt_of_le (by norm_num) hb.2.2.1)

/-- A numerical bound for the actual square-root scale factor. -/
theorem inverseDThreeHalves_bounds_of_half {d : ℝ}
    (hlo : (1 / 2 : ℝ) ≤ d) (hhi : d ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ inverseDThreeHalves d ∧ inverseDThreeHalves d ≤ 4 := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hlo
  have hs₀ := Real.sqrt_nonneg d
  have hs₂ := Real.sq_sqrt hd.le
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt d := by nlinarith
  have hshi : Real.sqrt d ≤ 2 := by nlinarith
  have hprod : 0 < d * Real.sqrt d := mul_pos hd (Real.sqrt_pos.mpr hd)
  have hprodlo : (1 / 4 : ℝ) ≤ d * Real.sqrt d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hslo)]
  have hprodhi : d * Real.sqrt d ≤ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hs₀,
      mul_nonneg (sub_nonneg.mpr hshi) (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  constructor
  · exact (le_div_iff₀ hprod).mpr (by nlinarith)
  · exact (div_le_iff₀ hprod).mpr (by nlinarith)

/-- The radial coefficient has the same strictly positive sign as the
profile on the full neighbourhood. -/
theorem n01PartB_originalCoefficients_a_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (originalCoefficients D S C z).a p := by
  have h := n01PartB_denominators_pos hD hS href hB hz hp
  exact mul_pos h.2.1 (inverseDThreeHalves_pos _ h.2.2)

/-- A uniform reciprocal bound available before parameter differentiation. -/
theorem n01PartB_polarScale_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (1 / 3 : ℝ) ≤ polarScale (stateProfile D S C z.1) (stateHeight D S C z) p ∧
    polarScale (stateProfile D S C z.1) (stateHeight D S C z) p ≤ 4 := by
  have hb := n01PartB_denominator_bounds hS href hB hz hp
  exact inverseDThreeHalves_bounds_of_half hb.2.2.2.2.1 hb.2.2.2.2.2

end ContinuousFlexibility.Statements
