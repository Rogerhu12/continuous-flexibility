import ContinuousFlexibility.Analysis.N01cControlledFields
import ContinuousFlexibility.Analysis.N01cNormalizedCoefficients

/-!
# Actual coefficient fields with one common distributed spatial bound

The controlled-field algebra is performed with an abstract parameter
space. Its scalar value identities are definitionally the original
normalized formulas. The final specialization retains the actual state
profile and physical polar inputs on the same neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def normalizedPowerDiscriminantValue (w k p : ℝ) : ℝ :=
  1 + ((-2) * (w * k) + (-1) * (k * k + (1 + w * w) * (p * p)))

def normalizedPowerQuotientValue (w wi k pt : ℝ) : ℝ :=
  1 + (k + (1 + w * w) * pt) * wi

private def coefficientPowerFormula
    (i : Fin 3) (w wr wi k p pr pt ri : ℝ) : ℝ :=
  let E := 1 + w * w
  let d := normalizedPowerDiscriminantValue w k p
  let Q := normalizedPowerQuotientValue w wi k pt
  if i = 0 then (w * Q) * inverseDThreeHalves d
  else if i = 1 then ((-1) * E) * (pr * inverseDThreeHalves d)
  else ((E * E * wi * pr * pr) * inverseDThreeHalves d +
    (wr * ri) * (1 / Real.sqrt d)) * Q⁻¹

section ControlledAlgebra

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
  {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
  (hU : IsOpen U) (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
  {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH)

def normalizedPowerEnergy
    (w : PowerControlledField p center base loss U Ω H E) :
    PowerControlledField p center base loss U Ω H E :=
  (PowerControlledField.const hU hΩ (fun q hq => (hH q hq).1) hE 1).add
    (w.mul w hU hΩ hE hH) hU hΩ (fun q hq => (hH q hq).1) hE

theorem normalizedPowerEnergy_value
    (w : PowerControlledField p center base loss U Ω H E) (x : X) (q : PolarPoint) :
    (normalizedPowerEnergy hU hΩ hE hH w).value x q =
      1 + w.value x q * w.value x q := rfl

def normalizedPowerQuotient
    (w wi k pt : PowerControlledField p center base loss U Ω H E) :
    PowerControlledField p center base loss U Ω H E :=
  (PowerControlledField.const hU hΩ (fun q hq => (hH q hq).1) hE 1).add
    ((k.add ((normalizedPowerEnergy hU hΩ hE hH w).mul pt hU hΩ hE hH)
      hU hΩ (fun q hq => (hH q hq).1) hE).mul wi hU hΩ hE hH)
    hU hΩ (fun q hq => (hH q hq).1) hE

theorem normalizedPowerQuotient_value
    (w wi k pt : PowerControlledField p center base loss U Ω H E)
    (x : X) (q : PolarPoint) :
    (normalizedPowerQuotient hU hΩ hE hH w wi k pt).value x q =
      normalizedPowerQuotientValue (w.value x q) (wi.value x q) (k.value x q) (pt.value x q) :=
  rfl

def normalizedPowerDiscriminant
    (w k pp : PowerControlledField p center base loss U Ω H E) :
    PowerControlledField p center base loss U Ω H E := by
  let cn : ℝ → PowerControlledField p center base loss U Ω H E :=
    PowerControlledField.const hU hΩ (fun q hq => (hH q hq).1) hE
  let plus := fun F G : PowerControlledField p center base loss U Ω H E =>
    F.add G hU hΩ (fun q hq => (hH q hq).1) hE
  let times := fun F G : PowerControlledField p center base loss U Ω H E =>
    F.mul G hU hΩ hE hH
  exact plus (cn 1) (plus (times (cn (-2)) (times w k))
    (times (cn (-1)) (plus (times k k)
      (times (normalizedPowerEnergy hU hΩ hE hH w) (times pp pp)))))

theorem normalizedPowerDiscriminant_value
    (w k pp : PowerControlledField p center base loss U Ω H E) (x : X) (q : PolarPoint) :
    (normalizedPowerDiscriminant hU hΩ hE hH w k pp).value x q =
      normalizedPowerDiscriminantValue (w.value x q) (k.value x q) (pp.value x q) := rfl

variable (w wr wi k pp pr pt ri : PowerControlledField p center base loss U Ω H E)
  (hDmap : ∀ x ∈ U, MapsTo (fun q => normalizedPowerDiscriminantValue
    (w.value x q) (k.value x q) (pp.value x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
  (hQmap : ∀ x ∈ U, MapsTo (fun q => normalizedPowerQuotientValue
    (w.value x q) (wi.value x q) (k.value x q) (pt.value x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))

private def normalizedCoefficientPowerField (i : Fin 3) :
    PowerControlledField p center base loss U Ω H E := by
  let cn : ℝ → PowerControlledField p center base loss U Ω H E :=
    PowerControlledField.const hU hΩ (fun q hq => (hH q hq).1) hE
  let plus := fun F G : PowerControlledField p center base loss U Ω H E =>
    F.add G hU hΩ (fun q hq => (hH q hq).1) hE
  let times := fun F G : PowerControlledField p center base loss U Ω H E =>
    F.mul G hU hΩ hE hH
  let en := normalizedPowerEnergy hU hΩ hE hH w
  let qn := normalizedPowerQuotient hU hΩ hE hH w wi k pt
  let dd := normalizedPowerDiscriminant hU hΩ hE hH w k pp
  let K : Set ℝ := Icc (1 / 2) (3 / 2)
  have hKV : K ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by norm_num) hy.1
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Ioi 0) :=
    fun y hy => (contDiffAt_id.inv hy.ne').contDiffWithinAt
  have hsqrt : ContDiffOn ℝ ∞ (fun y : ℝ => 1 / Real.sqrt y) (Ioi 0) :=
    fun y hy => (contDiffAt_const.div (contDiffAt_id.sqrt hy.ne')
      (Real.sqrt_pos.mpr hy).ne').contDiffWithinAt
  have hthree : ContDiffOn ℝ ∞ inverseDThreeHalves (Ioi 0) :=
    fun y hy => (contDiffAt_const.div
      (contDiffAt_id.mul (contDiffAt_id.sqrt hy.ne'))
      (mul_ne_zero hy.ne' (Real.sqrt_pos.mpr hy).ne')).contDiffWithinAt
  let ti := dd.scalarComp hU hΩ hE hH isOpen_Ioi isCompact_Icc hKV
    inverseDThreeHalves hthree hDmap
  let si := dd.scalarComp hU hΩ hE hH isOpen_Ioi isCompact_Icc hKV
    (fun y => 1 / Real.sqrt y) hsqrt hDmap
  let qi := qn.scalarComp hU hΩ hE hH isOpen_Ioi isCompact_Icc hKV
    (fun y => y⁻¹) hinv hQmap
  let ca := times (times w qn) ti
  let cb := times (times (cn (-1)) en) (times pr ti)
  let cc := times (plus
    (times (times (times (times (times en en) wi) pr) pr) ti)
    (times (times wr ri) si)) qi
  exact if i = 0 then ca else if i = 1 then cb else cc

private theorem normalizedCoefficientPowerField_value
    (i : Fin 3) (x : X) (q : PolarPoint) :
    (normalizedCoefficientPowerField hU hΩ hE hH w wr wi k pp pr pt ri hDmap hQmap i).value x q =
      coefficientPowerFormula i (w.value x q) (wr.value x q) (wi.value x q)
        (k.value x q) (pp.value x q) (pr.value x q) (pt.value x q) (ri.value x q) := by
  by_cases h0 : i = 0
  · simp only [normalizedCoefficientPowerField, coefficientPowerFormula, if_pos h0] <;> rfl
  · by_cases h1 : i = 1
    · simp only [normalizedCoefficientPowerField, coefficientPowerFormula, if_neg h0, if_pos h1] <;> rfl
    · simp only [normalizedCoefficientPowerField, coefficientPowerFormula, if_neg h0, if_neg h1] <;> rfl

/-- Package the actual input families and perform the final transport
with an abstract source, before specializing to the projective state. -/
private theorem coefficientPowerBounds_of_inputs
    (hHbounded : ∃ R : ℝ, ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ R)
    (rad : Fin 3 → X → PolarPoint → ℝ) (pol : Fin 5 → X → PolarPoint → ℝ)
    (radReg : ∀ j, MixedJetRegularity U Ω (rad j))
    (radBound : ∀ j, MixedPowerBounds p center base loss U Ω H E (rad j))
    (polReg : ∀ j, MixedJetRegularity U Ω (pol j))
    (polBound : ∀ j, MixedPowerBounds p center base loss U Ω H E (pol j))
    (radiusInverse : PowerControlledField p center base loss U Ω H E)
    (f : Fin 3 → X → PolarPoint → ℝ) (fReg : ∀ i, MixedJetRegularity U Ω (f i))
    (hDcompact : ∀ x ∈ U, MapsTo (fun q => normalizedPowerDiscriminantValue
      (rad 0 x q) (pol 0 x q) (pol 1 x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (hQcompact : ∀ x ∈ U, MapsTo (fun q => normalizedPowerQuotientValue
      (rad 0 x q) (rad 2 x q) (pol 0 x q) (pol 4 x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (hformula : ∀ i x, x ∈ U → ∀ q, q ∈ Ω →
      coefficientPowerFormula i (rad 0 x q) (rad 1 x q) (rad 2 x q)
        (pol 0 x q) (pol 1 x q) (pol 3 x q) (pol 4 x q) (radiusInverse.value x q) =
          f i x q) (i : Fin 3) :
    MixedPowerBounds p center base loss U Ω H E (f i) := by
  obtain ⟨R, hR⟩ := hHbounded
  let rd : Fin 3 → PowerControlledField p center base loss U Ω H E :=
    fun j => ⟨rad j, radReg j, radBound j⟩
  let pl : Fin 5 → PowerControlledField p center base loss U Ω H E :=
    fun j => ⟨pol j, polReg j, polBound j⟩
  let F := normalizedCoefficientPowerField hU hΩ hE hR
    (rd 0) (rd 1) (rd 2) (pl 0) (pl 1) (pl 3) (pl 4) radiusInverse hDcompact hQcompact i
  apply F.bounds.congr F.regular (fReg i) hΩ
  intro x hx q hq
  exact (normalizedCoefficientPowerField_value hU hΩ hE hR
    (rd 0) (rd 1) (rd 2) (pl 0) (pl 1) (pl 3) (pl 4)
      radiusInverse hDcompact hQcompact i x q).trans (hformula i x hx q hq)

end ControlledAlgebra

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

theorem stateNormalizedPowerDiscriminant_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (z : AnnularState S × ℝ) (q : PolarPoint) :
    normalizedPowerDiscriminantValue (stateProfile D S C z.1 q.1)
      (z.2 * heightRadial (stateU S z.1) q) (z.2 * heightAngular (stateU S z.1) q) =
      polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q := by
  rw [n01_polarDiscriminant_stateHeight hS hT hA]
  simp only [normalizedPowerDiscriminantValue, profileEnergy, radialEnergy, pow_two]
  ring

theorem stateNormalizedPowerQuotient_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {q : PolarPoint} (hq : q ∈ annularOpen D) :
    normalizedPowerQuotientValue (stateProfile D S C z.1 q.1)
      (stateProfile D S C z.1 q.1)⁻¹ (z.2 * heightRadial (stateU S z.1) q)
      (z.2 * angularPartial (heightAngular (stateU S z.1)) q) =
      heightQ (profileEnergy (stateProfile D S C z.1) q)
        (heightRadial (stateHeight D S C z) q)
        (angularPartial (heightAngular (stateHeight D S C z)) q) /
          stateProfile D S C z.1 q.1 := by
  rw [n01_heightQ_div_profile hS hT hA hB hz hq]
  simp only [normalizedPowerQuotientValue, profileEnergy, radialEnergy, pow_two, div_eq_mul_inv]
  ring

private theorem stateCoefficientPowerFormula_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {q : PolarPoint} (hq : q ∈ annularOpen D) (i : Fin 3) :
    coefficientPowerFormula i (stateProfile D S C z.1 q.1)
      (deriv (stateProfile D S C z.1) q.1) (stateProfile D S C z.1 q.1)⁻¹
      (z.2 * heightRadial (stateU S z.1) q) (z.2 * heightAngular (stateU S z.1) q)
      (z.2 * radialPartial (heightAngular (stateU S z.1)) q)
      (z.2 * angularPartial (heightAngular (stateU S z.1)) q) q.1⁻¹ =
      coefficientOriginalField D S C i z q := by
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  have hd := stateNormalizedPowerDiscriminant_eq hS hT hA z q
  have hqn := stateNormalizedPowerQuotient_eq hS hT hA hB hz hq
  have he : 1 + stateProfile D S C z.1 q.1 * stateProfile D S C z.1 q.1 =
      profileEnergy (stateProfile D S C z.1) q := by
    simp only [profileEnergy, radialEnergy, pow_two]
  by_cases h0 : i = 0
  · simp only [coefficientPowerFormula, if_pos h0, coefficientOriginalField, hd, hqn]
    have hw := (n01PartB_denominators_pos hD hS hA.2.1 hB hz hq).1.ne'
    change (stateProfile D S C z.1 q.1 * (_ / stateProfile D S C z.1 q.1)) *
      inverseDThreeHalves _ = heightQ _ _ _ * inverseDThreeHalves _
    field_simp [hw] <;> ring
  · by_cases h1 : i = 1
    · simp only [coefficientPowerFormula, if_neg h0, if_pos h1,
        coefficientOriginalField, hd, hqn, he]
      change _ = -profileEnergy (stateProfile D S C z.1) q *
        radialPartial (heightAngular (stateHeight D S C z)) q *
          inverseDThreeHalves (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q)
      rw [radialPartial_heightAngular_stateHeight hS hT hA z (hD.1.trans hq.1.1).ne']
      ring
    · simp only [coefficientPowerFormula, if_neg h0, if_neg h1,
        coefficientOriginalField, hd, hqn, he]
      rw [n01_originalCoefficientC_normalized hS hT hA hB hz hq,
        radialPartial_heightAngular_stateHeight hS hT hA z (hD.1.trans hq.1.1).ne']
      simp only [div_eq_mul_inv, pow_two]
      ring


private theorem materialHeight_threeQuarter_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ R : ℝ, ∀ q ∈ annularOpen D,
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) ∧ T.H q.1 ^ (3 / 4 : ℝ) ≤ R := by
  obtain ⟨R, hR, hb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  refine ⟨R, fun q hq => ⟨Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _, ?_⟩⟩
  simpa only [Real.rpow_zero, mul_one] using hb q.1 hq.1

private theorem stateCoefficientInputs_discriminant_mem
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hB : N01PartB D S C base ε) :
    ∀ z ∈ stateNeighborhood S C base ε, MapsTo (fun q => normalizedPowerDiscriminantValue
      (coefficientRadialInput D S C 0 z.1 q.1)
      (z.2 * stateUPolarInput S 0 z.1 q) (z.2 * stateUPolarInput S 1 z.1 q))
        (annularOpen D) (Icc (1 / 2 : ℝ) (3 / 2)) := by
  intro z hz q hq
  change normalizedPowerDiscriminantValue (stateProfile D S C z.1 q.1)
    (z.2 * heightRadial (stateU S z.1) q) (z.2 * heightAngular (stateU S z.1) q) ∈ _
  rw [stateNormalizedPowerDiscriminant_eq hS hT hA z q]
  exact (n01PartB_denominator_bounds hS hA.2.1 hB hz hq).2.2.2.2

private theorem stateCoefficientInputs_quotient_mem
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hB : N01PartB D S C base ε) :
    ∀ z ∈ stateNeighborhood S C base ε, MapsTo (fun q => normalizedPowerQuotientValue
      (coefficientRadialInput D S C 0 z.1 q.1) (coefficientRadialInput D S C 2 z.1 q.1)
      (z.2 * stateUPolarInput S 0 z.1 q) (z.2 * stateUPolarInput S 4 z.1 q))
        (annularOpen D) (Icc (1 / 2 : ℝ) (3 / 2)) := by
  intro z hz q hq
  change normalizedPowerQuotientValue (stateProfile D S C z.1 q.1)
    (stateProfile D S C z.1 q.1)⁻¹ (z.2 * heightRadial (stateU S z.1) q)
    (z.2 * angularPartial (heightAngular (stateU S z.1)) q) ∈ _
  rw [stateNormalizedPowerQuotient_eq hS hT hA hB hz hq]
  have hb := n01PartB_denominator_bounds hS hA.2.1 hB hz hq
  constructor <;> linarith [hb.2.2.1, hb.2.2.2.1]

private theorem stateCoefficientInputs_formula_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hB : N01PartB D S C base ε) :
    ∀ i z, z ∈ stateNeighborhood S C base ε → ∀ q, q ∈ annularOpen D →
      coefficientPowerFormula i
        (coefficientRadialInput D S C 0 z.1 q.1)
        (coefficientRadialInput D S C 1 z.1 q.1)
        (coefficientRadialInput D S C 2 z.1 q.1)
        (z.2 * stateUPolarInput S 0 z.1 q) (z.2 * stateUPolarInput S 1 z.1 q)
        (z.2 * stateUPolarInput S 3 z.1 q) (z.2 * stateUPolarInput S 4 z.1 q) q.1⁻¹ =
          coefficientOriginalField D S C i z q := by
  intro i z hz q hq
  exact stateCoefficientPowerFormula_eq hS hT hA hB hz hq i

theorem originalCoefficient_mixedPowerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) (i : Fin 3) :
    MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
      (coefficientOriginalField D S C i) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact coefficientPowerBounds_of_inputs
    (X := AnnularState S × ℝ) (p := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0)) (base := base) (loss := loss)
    (U := stateNeighborhood S C base ε) (Ω := annularOpen D)
    (H := fun q => T.H q.1 ^ (3 / 4 : ℝ)) (E := fun q => T.E0 q.1)
    (isOpen_stateNeighborhood S C base ε) (isOpen_Ioo.prod isOpen_univ)
    (fun q hq => hE q.1 hq.1) (materialHeight_threeQuarter_bounded hT)
    (fun j z q => coefficientRadialInput D S C j z.1 q.1)
    (fun j z q => z.2 * stateUPolarInput S j z.1 q)
    (fun j => coefficientRadialInput_regular hS hT hA hB j)
    (fun j => coefficientRadialInput_powerBounds hS hT hA hε hB hE hloc hχloc j)
    (fun j => coefficientPolarInput_regular hS hT hA.1.1.choose_spec.1.1 C base ε j)
    (fun j => coefficientPolarInput_powerBounds
      hS hT hA.1.1.choose_spec.1.1 C base loss hε1 hE hI j)
    (coefficientRadiusInverse_controlled hT hA.1.1.choose_spec.1 C base loss ε hE)
    (coefficientOriginalField D S C)
    (fun j => ⟨fun z hz => contDiffOn_coefficientOriginalField hS hT hA hB j hz,
      n01_originalCoefficientMixedSmoothDirections hS hT hA hB j⟩)
    (stateCoefficientInputs_discriminant_mem hS hT hA hB)
    (stateCoefficientInputs_quotient_mem hS hT hA hB)
    (stateCoefficientInputs_formula_eq hS hT hA hB) i

end ContinuousFlexibility.Statements
