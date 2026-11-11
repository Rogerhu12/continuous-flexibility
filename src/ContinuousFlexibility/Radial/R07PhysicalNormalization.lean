import ContinuousFlexibility.Radial.R07NaturalLineNormalization
import ContinuousFlexibility.Radial.R07DeepTailChange
import ContinuousFlexibility.Radial.R07CapPullback
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Normalized globally smooth physical representatives of the R06 line

The parameter theorem normalizes the outward-coordinate natural solution.
The physical flatness theorem supplies a globally smooth representative of
the same line.  Natural-line uniqueness identifies their scalar ratio and
produces a physical representative whose entrance Cauchy data depend only
on the normalized outward entrance slope.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def r07PhysicalGauge (endpoint : ℝ) (side : Bool) (j : ℕ) (x : ℝ) : ℝ :=
  (tailPhysicalRadius side x / endpoint) ^ ((j : ℝ) ^ 2)

def r07PhysicalInitialSlope (endpoint : ℝ) (side : Bool) (j : ℕ)
    (entrance slope : ℝ) : ℝ :=
  (deriv (r07PhysicalGauge endpoint side j) entrance +
      r07PhysicalGauge endpoint side j entrance * slope) /
    deriv (tailPhysicalRadius side) entrance

theorem contDiff_r07PhysicalGauge {endpoint : ℝ} (he : 0 < endpoint) (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (r07PhysicalGauge endpoint side j) :=
  ((r07_contDiff_radius side).div_const endpoint).rpow_const_of_ne
    (fun x => (div_pos (r07_radius_pos side x) he).ne')

theorem deriv_r07PhysicalRadius_ne_zero (side : Bool) (x : ℝ) :
    deriv (tailPhysicalRadius side) x ≠ 0 := by
  rw [(r07_hasDerivAt_radius side x).deriv]
  have hs : r07OutwardSign side ≠ 0 := by
    cases side <;> norm_num [r07OutwardSign]
  exact mul_ne_zero hs (r07_radius_pos side x).ne'

theorem radialNaturalTail_const_mul {D : ReferenceData} {side : Bool} {j : ℕ} {entry c : ℝ}
    {u : ℝ → ℝ} (hN : RadialNaturalTail D side j entry u) (hc : c ≠ 0) :
    RadialNaturalTail D side j entry (fun r => c * u r) := by
  refine ⟨contDiffAt_const.mul hN.1,
    ⟨contDiffOn_const.mul hN.2.1.1, fun r hr => ?_⟩, hN.2.2.1.const_mul c, ?_⟩
  · rw [radialJacobi_const_mul, hN.2.1.2 r hr, mul_zero]
  · obtain ⟨r, hr, hne⟩ := hN.2.2.2
    exact ⟨r, hr, mul_ne_zero hc hne⟩

/-- The physical representative in a flatness conclusion itself satisfies
the actual radial natural-tail predicate. -/
theorem radialNaturalTail_of_physical_representation {D : ReferenceData} {Q : DeepTailData}
    {side : Bool} {j : ℕ} {u v : ℝ → ℝ}
    (hD : IsAccumulatingProfile D)
    (hend : Q.endpoint = r07OutwardLog side (if side then D.b else D.a))
    (hv : ContDiff ℝ ∞ v) (hune : ∃ x ∈ Ioo Q.entrance Q.endpoint, u x ≠ 0)
    (hrel : ∀ x ∈ Ioo Q.entrance Q.endpoint,
      v (tailPhysicalRadius side x) = r07PhysicalGauge (if side then D.b else D.a) side j x * u x)
    (hode : ∀ x ∈ Ioo Q.entrance Q.endpoint,
      radialJacobi ((j : ℝ) ^ 2) D.w v (tailPhysicalRadius side x) = 0) :
    RadialNaturalTail D side j (tailPhysicalRadius side Q.entrance) v := by
  obtain ⟨C, hC⟩ := hD
  have ha : 0 < D.a := hC.1.1
  have hb : 0 < D.b := ha.trans hC.1.2.1
  have hw : Continuous D.w := hC.1.2.2.1.1.continuous
  have hep : 0 < (if side then D.b else D.a) := by cases side <;> assumption
  refine ⟨hv.contDiffAt, ⟨hv.contDiffOn, ?_⟩,
    (r07_memLp_radialHilbertMeasure ha hw hv.continuous).restrict _, ?_⟩
  · intro r hr
    have hrpos : 0 < r := by
      cases side
      · exact ha.trans hr.1
      · exact (r07_radius_pos true Q.entrance).trans hr.1
    have hx : r07OutwardLog side r ∈ Ioo Q.entrance Q.endpoint := by
      rw [hend]
      apply (r07_radius_mem_tail_iff ha hb side Q.entrance _).mp
      simpa only [r07_radius_outwardLog side hrpos] using hr
    simpa only [r07_radius_outwardLog side hrpos] using hode _ hx
  · obtain ⟨x, hx, hux⟩ := hune
    have hrmem : tailPhysicalRadius side x ∈ radialTailInterval D side
        (tailPhysicalRadius side Q.entrance) :=
      (r07_radius_mem_tail_iff ha hb side Q.entrance x).mpr (by simpa only [hend] using hx)
    refine ⟨tailPhysicalRadius side x, hrmem, ?_⟩
    rw [hrel x hx]
    exact mul_ne_zero
      (rpow_pos_of_pos (div_pos (r07_radius_pos side x) hep) _).ne' hux

/-- A normalized outward natural solution has a globally smooth physical
representative with explicitly prescribed entrance value and derivative. -/
theorem exists_normalized_physicalNaturalTail {D : ReferenceData} {Q : DeepTailData}
    {side : Bool} {j start : ℕ} {U : ℝ → ℝ}
    (hD : IsAccumulatingProfile D) (hgap : Q.entrance < Q.endpoint)
    (hend : Q.endpoint = r07OutwardLog side (if side then D.b else D.a))
    (hline : TailNaturalLineAndKernel Q) (hflat : TailPhysicalFlatConclusion D Q side j start)
    (hU : TailNaturalEquation Q U) (hU₀ : U Q.entrance = 1) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      RadialNaturalTail D side j (tailPhysicalRadius side Q.entrance) v ∧
      v (tailPhysicalRadius side Q.entrance) =
        r07PhysicalGauge (if side then D.b else D.a) side j Q.entrance ∧
      deriv v (tailPhysicalRadius side Q.entrance) =
        r07PhysicalInitialSlope (if side then D.b else D.a) side j Q.entrance
          (deriv U Q.entrance) := by
  rcases hflat with ⟨u, v, hu, hune, hv, hrel, hode, _⟩
  have hN : RadialNaturalTail D side j (tailPhysicalRadius side Q.entrance) v :=
    radialNaturalTail_of_physical_representation hD hend hv hune hrel hode
  have hc : u Q.entrance ≠ 0 := tailNaturalLine_entrance_ne_zero hgap hline hU hU₀ hu hune
  have hspan := (tailNaturalLine_normalized_spans hgap hline hU hU₀ hu).1
  let V : ℝ → ℝ := fun r => (u Q.entrance)⁻¹ * v r
  have hV : ContDiff ℝ ∞ V := contDiff_const.mul hv
  have hVN : RadialNaturalTail D side j (tailPhysicalRadius side Q.entrance) V :=
    radialNaturalTail_const_mul hN (inv_ne_zero hc)
  let endpoint : ℝ := if side then D.b else D.a
  let gauge : ℝ → ℝ := r07PhysicalGauge endpoint side j
  have hep : 0 < endpoint := by
    obtain ⟨C, hC⟩ := hD
    have ha : 0 < D.a := hC.1.1
    cases side
    · exact ha
    · exact ha.trans hC.1.2.1
  have hg : ContDiff ℝ ∞ gauge := contDiff_r07PhysicalGauge hep side j
  have hrelV : EqOn (fun x => V (tailPhysicalRadius side x))
      (fun x => gauge x * U x) (Ioo Q.entrance Q.endpoint) := by
    intro x hx
    dsimp only [V]
    rw [hrel x hx, hspan hx]
    change (u Q.entrance)⁻¹ * (gauge x * (u Q.entrance * U x)) = gauge x * U x
    field_simp [hc]
    <;> ring
  have hF : HasDerivAt (fun x => V (tailPhysicalRadius side x))
      (deriv V (tailPhysicalRadius side Q.entrance) * deriv (tailPhysicalRadius side) Q.entrance)
      Q.entrance := by
    simpa only [Function.comp_def] using
      (hV.differentiable (by simp) (tailPhysicalRadius side Q.entrance)).hasDerivAt.comp
        Q.entrance ((r07_contDiff_radius side).differentiable (by simp) Q.entrance).hasDerivAt
  have hG : HasDerivAt (fun x => gauge x * U x)
      (deriv gauge Q.entrance * U Q.entrance + gauge Q.entrance * deriv U Q.entrance)
      Q.entrance :=
    (hg.differentiable (by simp) Q.entrance).hasDerivAt.mul
      (hU.1.differentiableAt (by simp)).hasDerivAt
  have hboundary := cauchyData_eq_of_eqOn_Ioo_right hgap hF.differentiableAt hG.differentiableAt hrelV
  refine ⟨V, hV, hVN, ?_, ?_⟩
  · simpa only [hU₀, mul_one] using hboundary.1
  · have hd := hboundary.2
    rw [hF.deriv, hG.deriv, hU₀, mul_one] at hd
    exact (eq_div_iff (deriv_r07PhysicalRadius_ne_zero side Q.entrance)).mpr hd

end ContinuousFlexibility.Radial
