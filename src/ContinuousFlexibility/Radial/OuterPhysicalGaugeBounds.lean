import ContinuousFlexibility.Radial.OuterPhysicalPointwiseDecay
import ContinuousFlexibility.Radial.OuterTailDensityBounds
import ContinuousFlexibility.Radial.OuterOutwardGreenTransport

/-!
# Uniform physical gauge losses on the actual deep tail

The transition cutoff bounds the gauge and its reciprocal throughout
the logarithmic tail. Thus pointwise and two-point estimates for the
same logarithmic basis pass to the outward physical coordinates with
fixed numerical losses, independent of the frequency and depth.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem outer_tail_gauge_bounds {D : ReferenceData} {T : DeepTailData}
    (hD : RadialProfileGeometry D) {right : Bool} {j start : ℕ}
    (hj : 2 ≤ j) (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {x : ℝ} (hx : x ∈ Ico T.entrance T.endpoint) :
    exp (-1) ≤ outerLogGauge D right j x ∧ outerLogGauge D right j x ≤ exp 1 := by
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hg := outer_tail_density_gauge_bounds hD hj hphysical hclose hx
  change exp (-1) ≤ (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^
      (2 * (j : ℝ) ^ 2) ∧
    (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^
      (2 * (j : ℝ) ^ 2) ≤ exp 1 at hg
  have hs : (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^
      (2 * (j : ℝ) ^ 2) = outerLogGauge D right j x ^ 2 := by
    rw [outerLogGauge_eq_rpow, mul_comm 2 ((j : ℝ) ^ 2),
      rpow_mul (div_pos (tailPhysicalRadius_pos right x) hend).le, rpow_two]
  rw [hs] at hg
  have hgp := outerLogGauge_pos hend j x
  have hem : exp (-1) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  have hep : 1 ≤ exp 1 := one_le_exp_iff.mpr (by norm_num)
  constructor
  · by_contra h
    have hlt : outerLogGauge D right j x < exp (-1) := lt_of_not_ge h
    have hsq := mul_self_lt_mul_self hgp.le hlt
    have hsmall := mul_nonneg (exp_pos (-1)).le (sub_nonneg.mpr hem)
    nlinarith only [hg.1, hsq, hsmall]
  · by_contra h
    have hlt : exp 1 < outerLogGauge D right j x := lt_of_not_ge h
    have hsq := mul_self_lt_mul_self (exp_pos 1).le hlt
    have hlarge := mul_nonneg (exp_pos 1).le (sub_nonneg.mpr hep)
    nlinarith only [hg.2, hsq, hlarge]

theorem outer_tail_physical_lift_bound {D : ReferenceData} {T : DeepTailData}
    (hD : RadialProfileGeometry D) {right : Bool} {j start : ℕ}
    (hj : 2 ≤ j) (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {x B : ℝ} (hx : x ∈ Ico T.entrance T.endpoint) {u : ℝ → ℝ}
    (hu : |u x| ≤ B) :
    |outerTailOutwardLift D right j u (outerOutwardLogRadius right x)| ≤ exp 1 * B := by
  have hg := outer_tail_gauge_bounds hD hj hphysical hclose hx
  have hgp := (exp_pos (-1)).trans_le hg.1
  rw [outerTailOutwardLift_logRadius, abs_mul, abs_of_pos hgp]
  exact mul_le_mul hg.2 hu (abs_nonneg _) (exp_pos 1).le

theorem outer_tail_physical_kernel_bound {D : ReferenceData} {T : DeepTailData}
    (hD : RadialProfileGeometry D) {right : Bool} {j start : ℕ}
    (hj : 2 ≤ j) (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {x y B : ℝ} (hx : x ∈ Ico T.entrance T.endpoint)
    (hy : y ∈ Ico T.entrance T.endpoint) {Q P : ℝ → ℝ}
    (hk : |Q (min x y) * P (max x y)| ≤ B) :
    |outerOutwardDirichletKernel D right j Q P
      (outerOutwardLogRadius right x) (outerOutwardLogRadius right y)| ≤ exp 2 * B := by
  have hmin : min x y ∈ Ico T.entrance T.endpoint :=
    ⟨le_min hx.1 hy.1, (min_le_left _ _).trans_lt hx.2⟩
  have hmax : max x y ∈ Ico T.entrance T.endpoint :=
    ⟨hx.1.trans (le_max_left _ _), max_lt hx.2 hy.2⟩
  have hgm := outer_tail_gauge_bounds hD hj hphysical hclose hmin
  have hgM := outer_tail_gauge_bounds hD hj hphysical hclose hmax
  have hgmpos := (exp_pos (-1)).trans_le hgm.1
  have hgMpos := (exp_pos (-1)).trans_le hgM.1
  rw [outerOutwardDirichletKernel, outerOutwardLogRadius_min, outerOutwardLogRadius_max,
    outerTailOutwardLift_logRadius, outerTailOutwardLift_logRadius]
  calc
    _ = (outerLogGauge D right j (min x y) * outerLogGauge D right j (max x y)) *
        |Q (min x y) * P (max x y)| := by
      simp only [abs_mul, abs_of_pos hgmpos, abs_of_pos hgMpos]
      ring
    _ ≤ (exp 1 * exp 1) * B :=
      mul_le_mul (mul_le_mul hgm.2 hgM.2 hgMpos.le (exp_pos 1).le)
        hk (abs_nonneg _) (mul_nonneg (exp_pos 1).le (exp_pos 1).le)
    _ = exp 2 * B := by rw [← exp_add]; norm_num

theorem MorsePhysicalTailBasis.logP_entry_abs_le
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance) (hj : 2 ≤ j)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hclose : (morsePhysicalDeepTail M D right j start entrance η K).endpoint -
      (morsePhysicalDeepTail M D right j start entrance η K).entrance ≤
        (2 * (j : ℝ) ^ 2)⁻¹) :
    |F.logP (tailPhysicalLog right entrance)| ≤ exp 1 := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hg := outer_tail_gauge_bounds hD hj hphysical hclose
    (show T.entrance ∈ Ico T.entrance T.endpoint from ⟨le_rfl, hT.1⟩)
  have hgp := (exp_pos (-1)).trans_le hg.1
  have hi : (outerLogGauge D right j T.entrance)⁻¹ ≤ exp 1 := by
    have hh := inv_anti₀ (exp_pos (-1)) hg.1
    simpa only [← exp_neg, neg_neg] using hh
  have heq : outerLogGauge D right j T.entrance =
      (entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) := by
    change outerLogGauge D right j (tailPhysicalLog right entrance) = _
    rw [outerLogGauge_eq_rpow, tailPhysicalRadius_log right hentry]
  rw [F.P_log_entry, ← heq, abs_of_pos (inv_pos.mpr hgp)]
  exact hi

end ContinuousFlexibility.Radial
