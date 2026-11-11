import ContinuousFlexibility.Analysis.N01cControlledFields
import ContinuousFlexibility.Analysis.N01cNormalizedCoefficients

/-!
# Actual coefficient fields with one common distributed spatial bound

All inputs below are the actual state profile, inverse profile, and
q-dependent physical polar jets. The normalized denominators lie in the
fixed compact interval supplied by N01b. No coefficient estimate is an
input to the construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

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
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  let U := stateNeighborhood S C base ε
  let Ω := annularOpen D
  have hU : IsOpen U := isOpen_stateNeighborhood S C base ε
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hEq (q : PolarPoint) (hq : q ∈ Ω) : 1 ≤ T.E0 q.1 := hE q.1 hq.1
  obtain ⟨RH, hRH, hRHb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
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
  let cn : ℝ → PC := PowerControlledField.const hU hΩ (fun q hq => (hH q hq).1) hEq
  let plus : PC → PC → PC := fun F G => F.add G hU hΩ (fun q hq => (hH q hq).1) hEq
  let times : PC → PC → PC := fun F G => F.mul G hU hΩ hEq hH
  let en := plus (cn 1) (times (rd 0) (rd 0))
  let qn := plus (cn 1) (times (plus (pl 0) (times en (pl 4))) (rd 2))
  let dd := plus (cn 1) (plus
    (times (cn (-2)) (times (rd 0) (pl 0)))
    (times (cn (-1)) (plus (times (pl 0) (pl 0)) (times en (times (pl 1) (pl 1))))))
  have h0 (z : AnnularState S × ℝ) (q : PolarPoint) :
      (pl 0).value z q = z.2 * heightRadial (stateU S z.1) q := rfl
  have h1 (z : AnnularState S × ℝ) (q : PolarPoint) :
      (pl 1).value z q = z.2 * heightAngular (stateU S z.1) q := rfl
  have h3 (z : AnnularState S × ℝ) (q : PolarPoint) :
      (pl 3).value z q = z.2 * radialPartial (heightAngular (stateU S z.1)) q := by
    have hi : (0 : Fin 2).succ.succ.succ = (3 : Fin 5) := by decide
    change z.2 * stateUPolarInput S 3 z.1 q = _
    rw [← hi]
    simp only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero]
  have h4 (z : AnnularState S × ℝ) (q : PolarPoint) :
      (pl 4).value z q = z.2 * angularPartial (heightAngular (stateU S z.1)) q := by
    have hi : (0 : Fin 1).succ.succ.succ.succ = (4 : Fin 5) := by decide
    change z.2 * stateUPolarInput S 4 z.1 q = _
    rw [← hi]
    simp only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero]
  have he (z : AnnularState S × ℝ) (q : PolarPoint) :
      en.value z q = profileEnergy (stateProfile D S C z.1) q := by
    change 1 + stateProfile D S C z.1 q.1 * stateProfile D S C z.1 q.1 = _
    rw [profileEnergy, radialEnergy, pow_two]
  have hdd (z : AnnularState S × ℝ) (q : PolarPoint) :
      dd.value z q = polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q := by
    rw [n01_polarDiscriminant_stateHeight hS hT hA]
    change 1 + ((-2) * (stateProfile D S C z.1 q.1 * (pl 0).value z q) +
      (-1) * ((pl 0).value z q * (pl 0).value z q +
        en.value z q * ((pl 1).value z q * (pl 1).value z q))) = _
    rw [h0, h1, he]
    ring
  have hqn (z : AnnularState S × ℝ) (hz : z ∈ U) (q : PolarPoint) (hq : q ∈ Ω) :
      qn.value z q =
        heightQ (profileEnergy (stateProfile D S C z.1) q)
          (heightRadial (stateHeight D S C z) q)
          (angularPartial (heightAngular (stateHeight D S C z)) q) /
            stateProfile D S C z.1 q.1 := by
    rw [n01_heightQ_div_profile hS hT hA hB hz hq]
    change 1 + ((pl 0).value z q + en.value z q * (pl 4).value z q) *
      (stateProfile D S C z.1 q.1)⁻¹ = _
    rw [h0, h4, he, div_eq_mul_inv]
    ring
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
  have hsqrt : ContDiffOn ℝ ∞ (fun y : ℝ => 1 / Real.sqrt y) (Ioi 0) :=
    fun y hy => (contDiffAt_const.div (contDiffAt_id.sqrt hy.ne')
      (Real.sqrt_pos.mpr hy).ne').contDiffWithinAt
  have hthree : ContDiffOn ℝ ∞ inverseDThreeHalves (Ioi 0) :=
    fun y hy => (contDiffAt_const.div
      (contDiffAt_id.mul (contDiffAt_id.sqrt hy.ne'))
      (mul_ne_zero hy.ne' (Real.sqrt_pos.mpr hy).ne')).contDiffWithinAt
  let ti := dd.scalarComp hU hΩ hEq hH isOpen_Ioi isCompact_Icc hKV
    inverseDThreeHalves hthree hdmap
  let si := dd.scalarComp hU hΩ hEq hH isOpen_Ioi isCompact_Icc hKV
    (fun y => 1 / Real.sqrt y) hsqrt hdmap
  let qi := qn.scalarComp hU hΩ hEq hH isOpen_Ioi isCompact_Icc hKV
    (fun y => y⁻¹) hinv hqmap
  let ri : PC := coefficientRadiusInverse_controlled hT hD C base loss ε hE
  let ca := times (times (rd 0) qn) ti
  let cb := times (times (cn (-1)) en) (times (pl 3) ti)
  let cc := times (plus
    (times (times (times (times (times en en) (rd 2)) (pl 3)) (pl 3)) ti)
    (times (times (rd 1) ri) si)) qi
  have ha (z : AnnularState S × ℝ) (hz : z ∈ U) (q : PolarPoint) (hq : q ∈ Ω) :
      ca.value z q = (originalCoefficients D S C z).a q := by
    have hw := (n01PartB_denominators_pos hD hS hA.2.1 hB hz hq).1.ne'
    change (stateProfile D S C z.1 q.1 * qn.value z q) *
      inverseDThreeHalves (dd.value z q) = _
    rw [hqn z hz q hq, hdd]
    change _ = heightQ _ _ _ * inverseDThreeHalves _
    field_simp [hw]
  have hb (z : AnnularState S × ℝ) (hz : z ∈ U) (q : PolarPoint) (hq : q ∈ Ω) :
      cb.value z q = (originalCoefficients D S C z).b q := by
    change ((-1) * en.value z q) * ((pl 3).value z q *
      inverseDThreeHalves (dd.value z q)) = _
    rw [he, h3, hdd]
    change _ = -profileEnergy (stateProfile D S C z.1) q *
      radialPartial (heightAngular (stateHeight D S C z)) q *
        inverseDThreeHalves (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q)
    rw [radialPartial_heightAngular_stateHeight hS hT hA z (hD.1.trans hq.1.1).ne']
    ring
  have hc (z : AnnularState S × ℝ) (hz : z ∈ U) (q : PolarPoint) (hq : q ∈ Ω) :
      cc.value z q = (originalCoefficients D S C z).c q := by
    rw [n01_originalCoefficientC_normalized hS hT hA hB hz hq]
    change ((en.value z q * en.value z q * (stateProfile D S C z.1 q.1)⁻¹ *
        (pl 3).value z q * (pl 3).value z q * inverseDThreeHalves (dd.value z q) +
      deriv (stateProfile D S C z.1) q.1 * q.1⁻¹ * (1 / Real.sqrt (dd.value z q))) *
        (qn.value z q)⁻¹) = _
    rw [he, h3, hdd, hqn z hz q hq,
      radialPartial_heightAngular_stateHeight hS hT hA z (hD.1.trans hq.1.1).ne']
    simp only [div_eq_mul_inv, pow_two]
    ring
  let F : MixedJetRegularity U Ω (coefficientOriginalField D S C i) :=
    ⟨fun z hz => contDiffOn_coefficientOriginalField hS hT hA hB i hz,
      n01_originalCoefficientMixedSmoothDirections hS hT hA hB i⟩
  fin_cases i
  · exact ca.bounds.congr ca.regular F hΩ (fun z hz q hq => by
      simpa only [coefficientOriginalField, if_pos rfl] using ha z hz q hq)
  · exact cb.bounds.congr cb.regular F hΩ (fun z hz q hq => by
      simpa only [coefficientOriginalField, if_neg one_ne_zero, if_pos rfl] using hb z hz q hq)
  · exact cc.bounds.congr cc.regular F hΩ (fun z hz q hq => by
      simpa only [coefficientOriginalField,
        if_neg (by decide : (2 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 1)] using hc z hz q hq)

end ContinuousFlexibility.Statements
