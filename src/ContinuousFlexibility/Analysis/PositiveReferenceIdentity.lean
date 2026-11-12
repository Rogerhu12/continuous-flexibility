import ContinuousFlexibility.Analysis.PositiveReferenceCollarPrescribedWidth

/-!
# The fixed identity and a numerical lower bound for the same primitive

Constant physical endpoint slopes with total mass `r - l` produce the
identity radial coordinate. The unused middle mass is at most that
width, so the prescribed lower bound has a width-independent floor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

private theorem positiveReferenceScale_constant_unit_mass
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) :
    positiveReferenceScale l r δ (fun _ => 1 / (r - l))
      (fun _ => 1 / (r - l)) = 1 / (r - l) := by
  have hm : 0 < r - l := by linarith
  have hMiddle : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ hgap
  have hL := (contDiff_positiveEndpointCutoff l δ).continuous
  have hR := (contDiff_positiveEndpointCutoff r δ).continuous
  have hEnds : Continuous (fun x : ℝ =>
      positiveEndpointCutoff l δ x * (1 / (r - l)) +
        positiveEndpointCutoff r δ x * (1 / (r - l))) :=
    (hL.mul continuous_const).add (hR.mul continuous_const)
  have hMiddleScaled : Continuous (fun x : ℝ =>
      (1 / (r - l)) *
        (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x)) :=
    continuous_const.mul ((continuous_const.sub hL).sub hR)
  have hmass : positiveReferenceEndMass l r δ
      (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l)) +
      (1 / (r - l)) * positiveReferenceMiddleMass l r δ = 1 := by
    change (∫ x in l..r,
        positiveEndpointCutoff l δ x * (1 / (r - l)) +
          positiveEndpointCutoff r δ x * (1 / (r - l))) +
        (1 / (r - l)) * (∫ x in l..r,
          1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x) = 1
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (hEnds.intervalIntegrable (μ := MeasureTheory.volume) l r)
        (hMiddleScaled.intervalIntegrable (μ := MeasureTheory.volume) l r)]
    calc
      _ = ∫ _x in l..r, (1 / (r - l)) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = 1 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp [hm.ne']
  unfold positiveReferenceScale
  apply (div_eq_iff hMiddle.ne').mpr
  linarith only [hmass]

/-- With unit physical endpoint slopes, the actual primitive is the
identity on the whole plane, including both exterior portions. -/
theorem parameterizedPositiveReferenceCoordinate_one_eq_fst
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) :
    parameterizedPositiveReferenceCoordinate l r δ l (r - l)
      (fun _ _ => 1) = (Prod.fst : PolarPoint → ℝ) := by
  have hm : 0 < r - l := by linarith
  have hscale := positiveReferenceScale_constant_unit_mass hδ hgap
  have hs : positiveReferenceSlope l r δ
      (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l)) =
      (fun _ => 1 / (r - l)) := by
    funext x
    simp only [positiveReferenceSlope, hscale]
    ring
  funext p
  change l + (r - l) * (∫ x in l..p.1,
    positiveReferenceSlope l r δ
      (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l)) x) = p.1
  rw [hs, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp [hm.ne'] <;> ring

/-- The positive middle cutoff never contributes more than the width. -/
theorem positiveReferenceMiddleMass_le_width
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) :
    positiveReferenceMiddleMass l r δ ≤ r - l := by
  have hm : 0 < r - l := by linarith
  have hb (x : ℝ) :
      ‖1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x‖ ≤ 1 := by
    have hL := positiveEndpointCutoff_nonneg l δ x
    have hR := positiveEndpointCutoff_nonneg r δ x
    have hsum := positiveEndpointCutoff_add_le_one hδ hgap.le x
    have hnonneg : 0 ≤ 1 - positiveEndpointCutoff l δ x -
        positiveEndpointCutoff r δ x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    linarith
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := (1 : ℝ))
    (f := fun x => 1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x)
    (fun x _ => hb x)
  have hn' : |positiveReferenceMiddleMass l r δ| ≤ r - l := by
    simpa only [positiveReferenceMiddleMass, Real.norm_eq_abs,
      abs_of_pos hm, one_mul] using hn
  exact (le_abs_self _).trans hn'

/-- The reference slope is one and its fixed mass is the component width. -/
theorem prescribedPositiveCollarLower_reference_lower
    {l r δ κ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) :
    min (κ / 2) (1 / 2) ≤
      prescribedPositiveCollarLower l r δ (r - l) κ 1 := by
  have hm : 0 < r - l := by linarith
  have hMiddle : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ hgap
  have hupper := positiveReferenceMiddleMass_le_width hδ hgap
  let k : ℝ := min (κ / 2) (1 / 2)
  have hL : k ≤ min (κ / 2) (1 : ℝ) :=
    le_min (min_le_left _ _)
      ((min_le_right _ _).trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hR : k / (r - l) ≤ (1 / 2) / positiveReferenceMiddleMass l r δ :=
    (div_le_div_of_nonneg_right (min_le_right _ _) hm.le).trans
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 2) hMiddle hupper)
  have hbound : k ≤
      min (min (κ / 2) 1 / (r - l))
        ((1 / 2) / positiveReferenceMiddleMass l r δ) * (r - l) :=
    (div_le_iff₀ hm).mp
      (le_min (div_le_div_of_nonneg_right hL hm.le) hR)
  simpa only [k, prescribedPositiveCollarLower, mul_comm] using hbound

end ContinuousFlexibility.Analysis
