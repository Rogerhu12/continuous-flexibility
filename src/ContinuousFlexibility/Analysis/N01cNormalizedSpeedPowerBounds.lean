module

public import ContinuousFlexibility.Analysis.N01cOriginalCoefficientPowerBounds
public import ContinuousFlexibility.Analysis.N01cSpeedNormalization

/-!
# Actual normalized speed factors before one-high normalization

The rational drift and the multiplier of the optical square root use the
same actual profile and polar inputs as the coefficients. Their spatial
orders remain distributed in the power bound. The endpoint-weighted
optical factor is estimated separately before the complete speed jet is
normalized once.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private def normalizedSpeedPowerFormula (i : Fin 2) (w wi k pp pr pt : ℝ) : ℝ :=
  let E := 1 + w * w
  let Q := normalizedPowerQuotientValue w wi k pt
  let d := normalizedPowerDiscriminantValue w k pp
  if i = 0 then ((E * pr) * wi) * Q⁻¹ else Real.sqrt d * Q⁻¹

private theorem normalizedSpeedPowerFormula_scalar
    (i : Fin 2) (w wi k pp pr pt E Q d pr₀ : ℝ)
    (hwi : wi = w⁻¹) (he : E = 1 + w * w)
    (hq : normalizedPowerQuotientValue w wi k pt = Q / w)
    (hd : normalizedPowerDiscriminantValue w k pp = d) (hpr : pr = pr₀) :
    normalizedSpeedPowerFormula i w wi k pp pr pt =
      if i = 0 then E * pr₀ / (w * (Q / w)) else Real.sqrt d / (Q / w) := by
  subst wi
  subst E
  subst pr₀
  by_cases hi : i = 0
  · simp only [normalizedSpeedPowerFormula, if_pos hi, hq, hd,
      div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [normalizedSpeedPowerFormula, if_neg hi, hq, hd, div_eq_mul_inv]

section AbstractInputs

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
  {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}

private def normalizedSpeedPowerField
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH)
    (w wi k pp pr pt : PowerControlledField p center base loss U Ω H E)
    (hDmap : ∀ x ∈ U, MapsTo (fun q => normalizedPowerDiscriminantValue
      (w.value x q) (k.value x q) (pp.value x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (hQmap : ∀ x ∈ U, MapsTo (fun q => normalizedPowerQuotientValue
      (w.value x q) (wi.value x q) (k.value x q) (pt.value x q))
        Ω (Icc (1 / 2 : ℝ) (3 / 2))) (i : Fin 2) :
    PowerControlledField p center base loss U Ω H E := by
  let en := normalizedPowerEnergy hU hΩ hE hH w
  let qn := normalizedPowerQuotient hU hΩ hE hH w wi k pt
  let dd := normalizedPowerDiscriminant hU hΩ hE hH w k pp
  let K : Set ℝ := Icc (1 / 2) (3 / 2)
  have hKV : K ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by norm_num) hy.1
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Ioi 0) :=
    fun y hy => (contDiffAt_id.inv hy.ne').contDiffWithinAt
  have hsqrt : ContDiffOn ℝ ∞ Real.sqrt (Ioi 0) :=
    fun y hy => (contDiffAt_id.sqrt hy.ne').contDiffWithinAt
  let qi := qn.scalarComp hU hΩ hE hH isOpen_Ioi isCompact_Icc hKV
    (fun y : ℝ => y⁻¹) hinv hQmap
  let sd := dd.scalarComp hU hΩ hE hH isOpen_Ioi isCompact_Icc hKV
    Real.sqrt hsqrt hDmap
  let times := fun F G : PowerControlledField p center base loss U Ω H E =>
    F.mul G hU hΩ hE hH
  exact if i = 0 then times (times (times en pr) wi) qi else times sd qi

private theorem normalizedSpeedPowerField_value
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH)
    (w wi k pp pr pt : PowerControlledField p center base loss U Ω H E)
    (hDmap : ∀ x ∈ U, MapsTo (fun q => normalizedPowerDiscriminantValue
      (w.value x q) (k.value x q) (pp.value x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (hQmap : ∀ x ∈ U, MapsTo (fun q => normalizedPowerQuotientValue
      (w.value x q) (wi.value x q) (k.value x q) (pt.value x q))
        Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (i : Fin 2) (x : X) (q : PolarPoint) :
    (normalizedSpeedPowerField hU hΩ hE hH w wi k pp pr pt hDmap hQmap i).value x q =
      normalizedSpeedPowerFormula i (w.value x q) (wi.value x q)
        (k.value x q) (pp.value x q) (pr.value x q) (pt.value x q) := by
  by_cases hi : i = 0
  · simp only [normalizedSpeedPowerField, normalizedSpeedPowerFormula, if_pos hi] <;> rfl
  · simp only [normalizedSpeedPowerField, normalizedSpeedPowerFormula, if_neg hi] <;> rfl

/-- The full field construction and final equality transport are made
before specializing the abstract parameter space. -/
private def normalizedSpeedPowerControl_of_inputs
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    (hHbounded : ∃ R : ℝ, ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ R)
    (rad : Fin 3 → X → PolarPoint → ℝ) (pol : Fin 5 → X → PolarPoint → ℝ)
    (radReg : ∀ j, MixedJetRegularity U Ω (rad j))
    (radBound : ∀ j, MixedPowerBounds p center base loss U Ω H E (rad j))
    (polReg : ∀ j, MixedJetRegularity U Ω (pol j))
    (polBound : ∀ j, MixedPowerBounds p center base loss U Ω H E (pol j))
    (f : Fin 2 → X → PolarPoint → ℝ)
    (hDcompact : ∀ x ∈ U, MapsTo (fun q => normalizedPowerDiscriminantValue
      (rad 0 x q) (pol 0 x q) (pol 1 x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (hQcompact : ∀ x ∈ U, MapsTo (fun q => normalizedPowerQuotientValue
      (rad 0 x q) (rad 2 x q) (pol 0 x q) (pol 4 x q)) Ω (Icc (1 / 2 : ℝ) (3 / 2)))
    (hformula : ∀ i x, x ∈ U → ∀ q, q ∈ Ω →
      normalizedSpeedPowerFormula i (rad 0 x q) (rad 2 x q)
        (pol 0 x q) (pol 1 x q) (pol 3 x q) (pol 4 x q) = f i x q)
    (i : Fin 2) : PowerControlledField p center base loss U Ω H E := by
  let RH : ℝ := Classical.choose hHbounded
  have hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH := by
    simpa only [RH] using Classical.choose_spec hHbounded
  let rd : Fin 3 → PowerControlledField p center base loss U Ω H E :=
    fun j => ⟨rad j, radReg j, radBound j⟩
  let pl : Fin 5 → PowerControlledField p center base loss U Ω H E :=
    fun j => ⟨pol j, polReg j, polBound j⟩
  let F := normalizedSpeedPowerField hU hΩ hE hH
    (rd 0) (rd 2) (pl 0) (pl 1) (pl 3) (pl 4) hDcompact hQcompact i
  have heq : ∀ x ∈ U, EqOn (F.value x) (f i x) Ω := by
    intro x hx q hq
    exact (normalizedSpeedPowerField_value hU hΩ hE hH
      (rd 0) (rd 2) (pl 0) (pl 1) (pl 3) (pl 4)
        hDcompact hQcompact i x q).trans (hformula i x hx q hq)
  let G : MixedJetRegularity U Ω (f i) :=
    F.regular.congr hΩ
      (fun x hx => (F.regular.spatial x hx).congr
        (fun q hq => (heq x hx hq).symm)) heq
  exact ⟨f i, G, F.bounds.congr F.regular G hΩ heq⟩

end AbstractInputs

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

/-- The positive rational drift and the actual optical-root multiplier. -/
def normalizedSpeedFactor (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 2)
    (z : AnnularState S × ℝ) (q : PolarPoint) : ℝ :=
  let w := stateProfile D S C z.1
  let h := stateHeight D S C z
  let E := profileEnergy w q
  let Q := heightQ E (heightRadial h q) (angularPartial (heightAngular h) q)
  if i = 0 then E * radialPartial (heightAngular h) q / (w q.1 * (Q / w q.1))
  else Real.sqrt (polarDiscriminant w h q) / (Q / w q.1)

private theorem speedMaterialHeight_threeQuarter_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ R : ℝ, ∀ q ∈ annularOpen D,
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) ∧ T.H q.1 ^ (3 / 4 : ℝ) ≤ R := by
  obtain ⟨R, hR, hb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  refine ⟨R, fun q hq => ⟨Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _, ?_⟩⟩
  simpa only [Real.rpow_zero, mul_one] using hb q.1 hq.1

private theorem stateSpeedInputs_discriminant_mem
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

private theorem stateSpeedInputs_quotient_mem
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

private theorem stateSpeedPowerFormula_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hB : N01PartB D S C base ε) :
    ∀ i z, z ∈ stateNeighborhood S C base ε → ∀ q, q ∈ annularOpen D →
      normalizedSpeedPowerFormula i
        (coefficientRadialInput D S C 0 z.1 q.1)
        (coefficientRadialInput D S C 2 z.1 q.1)
        (z.2 * stateUPolarInput S 0 z.1 q) (z.2 * stateUPolarInput S 1 z.1 q)
        (z.2 * stateUPolarInput S 3 z.1 q) (z.2 * stateUPolarInput S 4 z.1 q) =
          normalizedSpeedFactor D S C i z q := by
  intro i z hz q hq
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  exact normalizedSpeedPowerFormula_scalar i
    (stateProfile D S C z.1 q.1) (stateProfile D S C z.1 q.1)⁻¹
    (z.2 * heightRadial (stateU S z.1) q) (z.2 * heightAngular (stateU S z.1) q)
    (z.2 * radialPartial (heightAngular (stateU S z.1)) q)
    (z.2 * angularPartial (heightAngular (stateU S z.1)) q)
    (profileEnergy (stateProfile D S C z.1) q)
    (heightQ (profileEnergy (stateProfile D S C z.1) q)
      (heightRadial (stateHeight D S C z) q)
      (angularPartial (heightAngular (stateHeight D S C z)) q))
    (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q)
    (radialPartial (heightAngular (stateHeight D S C z)) q) rfl
    (by simp only [profileEnergy, radialEnergy, pow_two])
    (stateNormalizedPowerQuotient_eq hS hT hA hB hz hq)
    (stateNormalizedPowerDiscriminant_eq hS hT hA z q)
    (radialPartial_heightAngular_stateHeight hS hT hA z (hD.1.trans hq.1.1).ne').symm

/-- A genuine controlled field for each actual normalized factor. -/
def normalizedSpeedFactor_controlled
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
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) (i : Fin 2) :
    PowerControlledField (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact normalizedSpeedPowerControl_of_inputs
    (X := AnnularState S × ℝ) (p := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0)) (base := base) (loss := loss)
    (U := stateNeighborhood S C base ε) (Ω := annularOpen D)
    (H := fun q => T.H q.1 ^ (3 / 4 : ℝ)) (E := fun q => T.E0 q.1)
    (isOpen_stateNeighborhood S C base ε) (isOpen_Ioo.prod isOpen_univ)
    (fun q hq => hE q.1 hq.1) (speedMaterialHeight_threeQuarter_bounded hT)
    (fun j z q => coefficientRadialInput D S C j z.1 q.1)
    (fun j z q => z.2 * stateUPolarInput S j z.1 q)
    (fun j => coefficientRadialInput_regular hS hT hA hB j)
    (fun j => coefficientRadialInput_powerBounds hS hT hA hε hB hE hloc hχloc j)
    (fun j => coefficientPolarInput_regular hS hT hA.1.1.choose_spec.1.1 C base ε j)
    (fun j => coefficientPolarInput_powerBounds
      hS hT hA.1.1.choose_spec.1.1 C base loss hε1 hE hI j)
    (normalizedSpeedFactor D S C)
    (stateSpeedInputs_discriminant_mem hS hT hA hB)
    (stateSpeedInputs_quotient_mem hS hT hA hB)
    (stateSpeedPowerFormula_eq hS hT hA hB) i

/-- The controlled field retains the exact original normalized factor. -/
theorem normalizedSpeedFactor_controlled_value
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
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) (i : Fin 2) :
    (normalizedSpeedFactor_controlled hS hT hA hε hε1 hB hE hloc hχloc hI i).value =
      normalizedSpeedFactor D S C i := rfl

/-- At the actual reference point, the drift vanishes and the multiplier
is one on the physical annulus. -/
theorem normalizedSpeedFactor_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    {q : PolarPoint} (hq : q ∈ annularOpen D) :
    normalizedSpeedFactor D S C 0 (C.referenceState, 0) q = 0 ∧
      normalizedSpeedFactor D S C 1 (C.referenceState, 0) q = 1 := by
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  have href := reference_mem_stateNeighborhood S C base hε
  have hqn := n01_heightQ_div_profile hS hT hA hB
    (z := (C.referenceState, 0)) href (p := q) hq
  have hdd := n01_polarDiscriminant_stateHeight hS hT hA (C.referenceState, 0) q
  have hpr := radialPartial_heightAngular_stateHeight hS hT hA
    (C.referenceState, 0) (p := q) (hD.1.trans hq.1.1).ne'
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)] at hqn hdd hpr
  constructor
  · simp only [normalizedSpeedFactor, if_pos rfl, ite_true, hpr, mul_zero, zero_div]
  · simp only [normalizedSpeedFactor, if_neg (by decide : (1 : Fin 2) ≠ 0),
      hdd, hqn, Real.sqrt_one, div_one]

/-- The normalized factors occur in the unchanged original minus speed. -/
theorem minusCharacteristicSpeed_normalized_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {q : PolarPoint} (hq : q ∈ annularOpen D) :
    minusCharacteristicSpeed (originalCoefficients D S C z) q =
      -normalizedSpeedFactor D S C 0 z q -
        normalizedSpeedFactor D S C 1 z q *
          Real.sqrt (-deriv (stateProfile D S C z.1) q.1 /
            (q.1 * stateProfile D S C z.1 q.1)) := by
  rw [n01_minusCharacteristicSpeed_normalized hS hT hA hB hz hq]
  simp only [normalizedSpeedFactor, if_pos rfl, ite_true,
    if_neg (by decide : (1 : Fin 2) ≠ 0), neg_mul, neg_div]

end ContinuousFlexibility.Statements
