import ContinuousFlexibility.Analysis.N01cOriginalCoefficientPowerBounds
import ContinuousFlexibility.Analysis.N01cSpeedNormalization

/-!
# Actual normalized speed factors before one-high normalization

The rational drift and the multiplier of the optical square root use the
same actual profile and polar inputs as the coefficients. Their spatial
orders remain distributed in the power bound. The endpoint-weighted
optical factor is estimated separately before the complete speed jet is
normalized once.
-/

noncomputable section

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
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  let U := stateNeighborhood S C base ε
  let Ω := annularOpen D
  have hU : IsOpen U := isOpen_stateNeighborhood S C base ε
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hEq (q : PolarPoint) (hq : q ∈ Ω) : 1 ≤ T.E0 q.1 := hE q.1 hq.1
  let hmaterial := materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let RH : ℝ := Classical.choose hmaterial
  have hRH : 0 < RH := (Classical.choose_spec hmaterial).1
  have hRHb := (Classical.choose_spec hmaterial).2
  have hH (q : PolarPoint) (hq : q ∈ Ω) :
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) ∧ T.H q.1 ^ (3 / 4 : ℝ) ≤ RH := by
    refine ⟨Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _, ?_⟩
    simpa only [Real.rpow_zero, mul_one] using hRHb q.1 hq.1
  let PC := PowerControlledField (pairGrading (stateGrading S) realGrading)
    (C.referenceState, 0) base loss U Ω
    (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
  let rd : Fin 3 → PC := fun j =>
    ⟨fun z q => coefficientRadialInput D S C j z.1 q.1,
      coefficientRadialInput_regular hS hT hA hB j,
      coefficientRadialInput_powerBounds hS hT hA hε hB hE hloc hχloc j⟩
  let pl : Fin 5 → PC := fun j =>
    ⟨fun z q => z.2 * stateUPolarInput S j z.1 q,
      coefficientPolarInput_regular hS hT hD.1 C base ε j,
      coefficientPolarInput_powerBounds hS hT hD.1 C base loss hε1 hE hI j⟩
  let times : PC → PC → PC := fun F G => F.mul G hU hΩ hEq hH
  let en := normalizedPowerEnergy hU hΩ hEq hH (rd 0)
  let qn := normalizedPowerQuotient hU hΩ hEq hH (rd 0) (rd 2) (pl 0) (pl 4)
  let dd := normalizedPowerDiscriminant hU hΩ hEq hH (rd 0) (pl 0) (pl 1)
  have h3 (z : AnnularState S × ℝ) (q : PolarPoint) :
      (pl 3).value z q = z.2 * radialPartial (heightAngular (stateU S z.1)) q := by
    have hi : (0 : Fin 2).succ.succ.succ = (3 : Fin 5) := by decide
    change z.2 * stateUPolarInput S 3 z.1 q = _
    rw [← hi]
    simp only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero]
  have he (z : AnnularState S × ℝ) (q : PolarPoint) :
      en.value z q = profileEnergy (stateProfile D S C z.1) q := by
    calc
      en.value z q = 1 + (rd 0).value z q * (rd 0).value z q :=
        normalizedPowerEnergy_value hU hΩ hEq hH (rd 0) z q
      _ = profileEnergy (stateProfile D S C z.1) q := by
        change 1 + stateProfile D S C z.1 q.1 * stateProfile D S C z.1 q.1 = _
        rw [profileEnergy, radialEnergy, pow_two]
  have hdd (z : AnnularState S × ℝ) (q : PolarPoint) :
      dd.value z q = polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q :=
    (normalizedPowerDiscriminant_value hU hΩ hEq hH (rd 0) (pl 0) (pl 1) z q).trans
      (stateNormalizedPowerDiscriminant_eq hS hT hA z q)
  have hqn (z : AnnularState S × ℝ) (hz : z ∈ U) (q : PolarPoint) (hq : q ∈ Ω) :
      qn.value z q =
        heightQ (profileEnergy (stateProfile D S C z.1) q)
          (heightRadial (stateHeight D S C z) q)
          (angularPartial (heightAngular (stateHeight D S C z)) q) /
            stateProfile D S C z.1 q.1 :=
    (normalizedPowerQuotient_value hU hΩ hEq hH (rd 0) (rd 2) (pl 0) (pl 4) z q).trans
      (stateNormalizedPowerQuotient_eq hS hT hA hB hz hq)
  let K : Set ℝ := Icc (1 / 2) (3 / 2)
  have hKV : K ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by norm_num) hy.1
  have hdmap : ∀ z ∈ U, MapsTo (dd.value z) Ω K := by
    intro z hz q hq
    rw [hdd]
    exact (n01PartB_denominator_bounds hS hA.2.1 hB hz hq).2.2.2.2
  have hqmap : ∀ z ∈ U, MapsTo (qn.value z) Ω K := by
    intro z hz q hq
    rw [hqn z hz q hq]
    have hb := n01PartB_denominator_bounds hS hA.2.1 hB hz hq
    constructor <;> linarith [hb.2.2.1, hb.2.2.2.1]
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Ioi 0) :=
    fun y hy => (contDiffAt_id.inv hy.ne').contDiffWithinAt
  have hsqrt : ContDiffOn ℝ ∞ Real.sqrt (Ioi 0) :=
    fun y hy => (contDiffAt_id.sqrt hy.ne').contDiffWithinAt
  let qi := qn.scalarComp hU hΩ hEq hH isOpen_Ioi isCompact_Icc hKV
    (fun y => y⁻¹) hinv hqmap
  let sd := dd.scalarComp hU hΩ hEq hH isOpen_Ioi isCompact_Icc hKV
    Real.sqrt hsqrt hdmap
  let fa := times (times (times en (pl 3)) (rd 2)) qi
  let fb := times sd qi
  let F : PC := if i = 0 then fa else fb
  have heq : ∀ z ∈ U, EqOn (F.value z) (normalizedSpeedFactor D S C i z) Ω := by
    intro z hz q hq
    by_cases hi : i = 0
    · simp only [F, if_pos hi, normalizedSpeedFactor, if_pos hi]
      change ((en.value z q * (pl 3).value z q) *
        (stateProfile D S C z.1 q.1)⁻¹) * (qn.value z q)⁻¹ = _
      rw [he, h3, hqn z hz q hq,
        radialPartial_heightAngular_stateHeight hS hT hA z (hD.1.trans hq.1.1).ne']
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp only [F, if_neg hi, normalizedSpeedFactor, if_neg hi]
      change Real.sqrt (dd.value z q) * (qn.value z q)⁻¹ = _
      rw [hdd, hqn z hz q hq, div_eq_mul_inv]
  let G : MixedJetRegularity U Ω (normalizedSpeedFactor D S C i) :=
    F.regular.congr hΩ
      (fun z hz => (F.regular.spatial z hz).congr
        (fun q hq => (heq z hz q hq).symm)) heq
  exact ⟨normalizedSpeedFactor D S C i, G, F.bounds.congr F.regular G hΩ heq⟩

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
  · simp only [normalizedSpeedFactor, if_pos rfl, hpr, mul_zero, zero_div]
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
  simp only [normalizedSpeedFactor, if_pos rfl,
    if_neg (by decide : (1 : Fin 2) ≠ 0), neg_mul, neg_div]

end ContinuousFlexibility.Statements
