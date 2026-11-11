import ContinuousFlexibility.Analysis.OpticalControlRatio
import ContinuousFlexibility.Analysis.OpticalFactorSecondVariation
import ContinuousFlexibility.Analysis.N01RadialFlow

/-!
# Full-component optical curvature under the exact N01 support condition

Only `Function.support χ ⊆ Ioo l h` is used.  The ratio extension at the
simple turning points supplies the fixed-factor integral, so its second
derivative is the actual full travel derivative.  Unit normalization
forces a quantitative product lower bound for the control derivative
and that second derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem opticalSpeed_sq_mul_logRatio
    {w χ : ℝ → ℝ} {l h r : ℝ} (hl : 0 < l)
    (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0)
    (hsupp : Function.support χ ⊆ Ioo l h) (hr : r ∈ Icc l h) :
    opticalSpeed w r ^ 2 * opticalLogRatio w χ r = -deriv χ r / r := by
  by_cases hwr : deriv w r = 0
  · have hout : r ∉ Ioo l h := fun hri => (hneg r hri).ne hwr
    have hχ0 := (control_first_second_deriv_zero_off_interval hχ hsupp hout).1
    simp only [opticalSpeed, opticalLogRatio, hwr, hχ0, neg_zero, zero_div,
      Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
  · have hr0 : r ≠ 0 := (hl.trans_le hr.1).ne'
    have hw0 : w r ≠ 0 := (hpos r hr).ne'
    rw [opticalSpeed, Real.sq_sqrt (optical_radical_nonneg_on_component hl hpos hneg hturn hr)]
    dsimp only [opticalLogRatio]
    field_simp [hr0, hw0, hwr]
    <;> ring

/-- Both derivatives concern the actual full optical travel, with no
interior collar and no independent derivative assumption. -/
theorem hasDerivAt_opticalTravel_logPerturbation_full_twice
    {w χ : ℝ → ℝ} {l h : ℝ} (hl : 0 < l) (hlh : l < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0 ∧
      deriv (deriv w) l ≠ 0 ∧ deriv (deriv w) h ≠ 0)
    (hsupp : Function.support χ ⊆ Ioo l h) :
    HasDerivAt (fun t => opticalTravel (opticalLogPerturbation w χ t) l h)
      (∫ r in l..h, opticalSpeed w r * opticalLogRatio w χ r / 2) 0 ∧
    HasDerivAt (deriv (fun t => opticalTravel (opticalLogPerturbation w χ t) l h))
      (-(∫ r in l..h, opticalSpeed w r * opticalLogRatio w χ r ^ 2 / 4)) 0 := by
  have heq : (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) =
      (fun t => ∫ r in l..h, opticalSpeed w r * Real.sqrt (1 + t * opticalLogRatio w χ r)) :=
    funext (opticalTravel_logPerturbation_factor hl hlh hw hχ hpos hneg
      ⟨hturn.1, hturn.2.1⟩ hsupp)
  rw [heq]
  exact Analysis.hasDerivAt_sqrtFactor_integral_twice hlh
    (continuousOn_opticalSpeed_of_profile hw hl hpos)
    (continuousOn_opticalLogRatio hw hχ hneg hturn hsupp)

theorem normalized_opticalControl_full_curvature_bound
    {w χ : ℝ → ℝ} {l h B D : ℝ} (hl : 0 < l) (hlh : l < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0 ∧
      deriv (deriv w) l ≠ 0 ∧ deriv (deriv w) h ≠ 0)
    (hsupp : Function.support χ ⊆ Ioo l h)
    (hχB : ∀ r ∈ Icc l h, |deriv χ r| ≤ B)
    (hunit : HasDerivAt (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) 1 0)
    (hD : |deriv (deriv (fun t => opticalTravel (opticalLogPerturbation w χ t) l h)) 0| ≤ D) :
    2 * l ≤ (h - l) ^ 2 * B * D := by
  have heq : (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) =
      (fun t => ∫ r in l..h, opticalSpeed w r * Real.sqrt (1 + t * opticalLogRatio w χ r)) :=
    funext (opticalTravel_logPerturbation_factor hl hlh hw hχ hpos hneg
      ⟨hturn.1, hturn.2.1⟩ hsupp)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hχB l ⟨le_rfl, hlh.le⟩)
  have hB : ∀ r ∈ Icc l h,
      |opticalSpeed w r ^ 2 * opticalLogRatio w χ r| ≤ B / l := by
    intro r hr
    have hrpos : 0 < r := hl.trans_le hr.1
    rw [opticalSpeed_sq_mul_logRatio hl hχ hpos hneg ⟨hturn.1, hturn.2.1⟩ hsupp hr,
      abs_div, abs_neg, abs_of_pos hrpos]
    exact (div_le_div_of_nonneg_right (hχB r hr) hrpos.le).trans
      (div_le_div_of_nonneg_left hB0 hl hr.1)
  rw [heq] at hunit hD
  have hbound := Analysis.sqrtFactor_normalized_secondDerivative_lower_bound hlh
    (continuousOn_opticalSpeed_of_profile hw hl hpos)
    (continuousOn_opticalLogRatio hw hχ hneg hturn hsupp)
    (fun r _ => Real.sqrt_nonneg _) hB hunit hD
  calc
    2 * l ≤ ((h - l) ^ 2 * (B / l) * D) * l :=
      mul_le_mul_of_nonneg_right hbound hl.le
    _ = (h - l) ^ 2 * B * D := by field_simp [hl.ne']; ring

/-- The N01 hypotheses themselves supply every endpoint and support
premise of the full-component curvature inequality. -/
theorem N01Properties.control_curvature_product_lower_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) {B K : ℝ}
    (hB : 0 ≤ B)
    (hχB : ∀ r ∈ Ioo (C.left m) (C.right m), |deriv (C.control m) r| ≤ B)
    (hK : |deriv (deriv (fun t => opticalTravel
      (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m))) 0| ≤ K) :
    2 * C.left m ≤ (C.right m - C.left m) ^ 2 * B * K := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  rcases hcontrol with ⟨hinterval, hturn, _, hneg, _, hcontrols, _, _, hunit⟩
  apply normalized_opticalControl_full_curvature_bound
    (hgeom.1.1.trans (hinterval m).1) (hinterval m).2.1
    hgeom.1.2.2.1.1 (hcontrols m).1 ?_ (hneg m) (hturn m) (hcontrols m).2.2 ?_ ?_ hK
  · intro r hr
    exact hgeom.1.2.2.2.2.1 r
      ⟨(hinterval m).1.trans_le hr.1, hr.2.trans_lt (hinterval m).2.2⟩
  · intro r hr
    by_cases hri : r ∈ Ioo (C.left m) (C.right m)
    · exact hχB r hri
    · rw [(control_first_second_deriv_zero_off_interval
        (hcontrols m).1 (hcontrols m).2.2 hri).1, abs_zero]
      exact hB
  · simpa only [opticalTravel, opticalSpeed, opticalLogPerturbation] using hunit m

theorem N01Properties.controlTravel_hasDerivAt_second
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    HasDerivAt (deriv (fun t => opticalTravel
      (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m)))
      (-(∫ r in C.left m..C.right m,
        opticalSpeed D.w r * opticalLogRatio D.w (C.control m) r ^ 2 / 4)) 0 := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  rcases hcontrol with ⟨hinterval, hturn, _, hneg, _, hcontrols, _⟩
  apply (hasDerivAt_opticalTravel_logPerturbation_full_twice
    (hgeom.1.1.trans (hinterval m).1) (hinterval m).2.1
    hgeom.1.2.2.1.1 (hcontrols m).1 ?_ (hneg m) (hturn m) (hcontrols m).2.2).2
  intro r hr
  exact hgeom.1.2.2.2.2.1 r
    ⟨(hinterval m).1.trans_le hr.1, hr.2.trans_lt (hinterval m).2.2⟩

end ContinuousFlexibility.Statements
