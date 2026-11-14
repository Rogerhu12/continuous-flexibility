module

public import ContinuousFlexibility.Radial.TailEdgeEnergy
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Weighted Poincaré estimates on a mass interval

The constants are the actual mass and resistance integrals. A zero weighted
mean supplies a zero of the continuous function, and weighted Cauchy--Schwarz
then controls every value, including both endpoint traces. These estimates
apply to either orientation of an interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

theorem tail_weighted_integral_cauchy {a b : ℝ} {p g : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, g x) ^ 2 ≤
      (∫ x in a..b, (p x)⁻¹) * ∫ x in a..b, p x * g x ^ 2 := by
  obtain rfl | hab := hab.eq_or_lt
  · simp
  have hi : ContinuousOn (fun x => (p x)⁻¹) (Icc a b) :=
    hp.inv₀ (fun x hx => (hpos x hx).ne')
  have hR : 0 < ∫ x in a..b, (p x)⁻¹ :=
    intervalIntegral.integral_pos hab hi
      (fun x hx => (inv_pos.mpr (hpos x ⟨hx.1.le, hx.2⟩)).le)
      ⟨a, ⟨le_rfl, hab.le⟩, inv_pos.mpr (hpos a ⟨le_rfl, hab.le⟩)⟩
  let R : ℝ := ∫ x in a..b, (p x)⁻¹
  let M : ℝ := ∫ x in a..b, g x
  let E : ℝ := ∫ x in a..b, p x * g x ^ 2
  let c : ℝ := M / R
  have hc : c * R = M := div_mul_cancel₀ M hR.ne'
  have hEint : IntervalIntegrable (fun x => p x * g x ^ 2) volume a b :=
    (hp.mul (hg.pow 2)).intervalIntegrable_of_Icc hab.le
  have hMint : IntervalIntegrable (fun x => (2 * c) * g x) volume a b :=
    (hg.const_mul (2 * c)).intervalIntegrable_of_Icc hab.le
  have hRint : IntervalIntegrable (fun x => c ^ 2 * (p x)⁻¹) volume a b :=
    (hi.const_mul (c ^ 2)).intervalIntegrable_of_Icc hab.le
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
    (f := fun x => p x * (g x - c / p x) ^ 2)
    (fun x hx => mul_nonneg (hpos x hx).le (sq_nonneg _))
  have he : (∫ x in a..b, p x * (g x - c / p x) ^ 2) =
      E - (2 * c) * M + c ^ 2 * R := by
    calc
      _ = ∫ x in a..b, (p x * g x ^ 2 - (2 * c) * g x) + c ^ 2 * (p x)⁻¹ := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hab.le]
        intro x hx
        field_simp [(hpos x hx).ne']
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hEint.sub hMint) hRint,
          intervalIntegral.integral_sub hEint hMint,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [he] at hn
  have hc₂ : c ^ 2 * R = c * M := by rw [← hc]; ring
  rw [hc₂] at hn
  have hME : c * M ≤ E := by linarith only [hn]
  change M ^ 2 ≤ R * E
  calc
    M ^ 2 = R * (c * M) := by rw [← hc]; ring
    _ ≤ R * E := mul_le_mul_of_nonneg_left hME hR.le

/-- A zero weighted mean forces a zero in the interval. -/
theorem tail_exists_zero_of_weighted_mean_zero {a b : ℝ} {p u : ℝ → ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hu : ContinuousOn u (Icc a b))
    (hmean : (∫ x in a..b, p x * u x) = 0) :
    ∃ z ∈ Icc a b, u z = 0 := by
  have hlo : ∃ x ∈ Icc a b, u x ≤ 0 := by
    by_contra h
    have hpositive (x : ℝ) (hx : x ∈ Icc a b) : 0 < u x :=
      lt_of_not_ge (fun hx' => h ⟨x, hx, hx'⟩)
    have hgt := intervalIntegral.integral_pos hab (hp.mul hu)
      (fun x hx => (mul_pos (hpos x ⟨hx.1.le, hx.2⟩)
        (hpositive x ⟨hx.1.le, hx.2⟩)).le)
      ⟨a, ⟨le_rfl, hab.le⟩,
        mul_pos (hpos a ⟨le_rfl, hab.le⟩) (hpositive a ⟨le_rfl, hab.le⟩)⟩
    simp only [Pi.mul_apply, hmean] at hgt
    exact lt_irrefl 0 hgt
  have hhi : ∃ x ∈ Icc a b, 0 ≤ u x := by
    by_contra h
    have hnegative (x : ℝ) (hx : x ∈ Icc a b) : u x < 0 :=
      lt_of_not_ge (fun hx' => h ⟨x, hx, hx'⟩)
    have hgt := intervalIntegral.integral_pos hab (hp.mul hu.neg)
      (fun x hx => (mul_pos (hpos x ⟨hx.1.le, hx.2⟩)
        (neg_pos.mpr (hnegative x ⟨hx.1.le, hx.2⟩))).le)
      ⟨a, ⟨le_rfl, hab.le⟩,
        mul_pos (hpos a ⟨le_rfl, hab.le⟩)
          (neg_pos.mpr (hnegative a ⟨le_rfl, hab.le⟩))⟩
    simp only [Pi.mul_apply, Pi.neg_apply, mul_neg, intervalIntegral.integral_neg,
      hmean, neg_zero] at hgt
    exact lt_irrefl 0 hgt
  obtain ⟨x, hx, hux⟩ := hlo
  obtain ⟨y, hy, huy⟩ := hhi
  exact isPreconnected_Icc.intermediate_value hx hy hu ⟨hux, huy⟩

private theorem tail_value_difference_sq_le_ordered {a b x y : ℝ} {p u : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hu : ContDiff ℝ 1 u)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    (u y - u x) ^ 2 ≤
      (∫ t in a..b, (p t)⁻¹) * ∫ t in a..b, p t * deriv u t ^ 2 := by
  have hs : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hd : Continuous (deriv u) := (contDiff_one_iff_deriv.mp hu).2
  have hdif : Differentiable ℝ u := (contDiff_one_iff_deriv.mp hu).1
  have hi : ContinuousOn (fun t => (p t)⁻¹) (Icc a b) :=
    hp.inv₀ (fun t ht => (hpos t ht).ne')
  have he : ContinuousOn (fun t => p t * deriv u t ^ 2) (Icc a b) :=
    hp.mul (hd.pow 2).continuousOn
  have hcs := tail_weighted_integral_cauchy hxy (hp.mono hs)
    (fun t ht => hpos t (hs ht)) hd.continuousOn
  rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hdif t)
    (hd.intervalIntegrable x y)] at hcs
  have hR : (∫ t in x..y, (p t)⁻¹) ≤ ∫ t in a..b, (p t)⁻¹ :=
    intervalIntegral.integral_mono_interval hx.1 hxy hy.2
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun t ht => (inv_pos.mpr (hpos t ⟨ht.1.le, ht.2⟩)).le))
      (hi.intervalIntegrable_of_Icc hab)
  have hE : (∫ t in x..y, p t * deriv u t ^ 2) ≤
      ∫ t in a..b, p t * deriv u t ^ 2 :=
    intervalIntegral.integral_mono_interval hx.1 hxy hy.2
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun t ht =>
          mul_nonneg (hpos t ⟨ht.1.le, ht.2⟩).le (sq_nonneg _)))
      (he.intervalIntegrable_of_Icc hab)
  exact hcs.trans (mul_le_mul hR hE
    (intervalIntegral.integral_nonneg hxy
      (fun t ht => mul_nonneg (hpos t (hs ht)).le (sq_nonneg _)))
    (intervalIntegral.integral_nonneg hab (fun t ht => (inv_pos.mpr (hpos t ht)).le)))

/-- Weighted Cauchy--Schwarz controls the oscillation on an entire interval. -/
theorem tail_value_difference_sq_le {a b x y : ℝ} {p u : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hu : ContDiff ℝ 1 u)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (u y - u x) ^ 2 ≤
      (∫ t in a..b, (p t)⁻¹) * ∫ t in a..b, p t * deriv u t ^ 2 := by
  rcases le_total x y with hxy | hyx
  · exact tail_value_difference_sq_le_ordered hab hp hpos hu hx hy hxy
  · simpa only [sub_sq_comm] using
      tail_value_difference_sq_le_ordered hab hp hpos hu hy hx hyx

/-- A single zero gives the Poincaré and trace estimates with the same
mass--resistance constant. -/
theorem tail_poincare_of_zero {a b z : ℝ} {p u : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hu : ContDiff ℝ 1 u)
    (hz : z ∈ Icc a b) (huz : u z = 0) :
    (∀ x ∈ Icc a b, u x ^ 2 ≤
      (∫ t in a..b, (p t)⁻¹) * ∫ t in a..b, p t * deriv u t ^ 2) ∧
      (∫ x in a..b, p x * u x ^ 2) ≤
        (∫ x in a..b, p x) * (∫ x in a..b, (p x)⁻¹) *
          ∫ x in a..b, p x * deriv u x ^ 2 := by
  have hvalue (x : ℝ) (hx : x ∈ Icc a b) : u x ^ 2 ≤
      (∫ t in a..b, (p t)⁻¹) * ∫ t in a..b, p t * deriv u t ^ 2 := by
    simpa only [huz, sub_zero] using tail_value_difference_sq_le hab hp hpos hu hz hx
  refine ⟨hvalue, ?_⟩
  calc
    _ ≤ ∫ x in a..b, p x * ((∫ t in a..b, (p t)⁻¹) *
        ∫ t in a..b, p t * deriv u t ^ 2) :=
      intervalIntegral.integral_mono_on hab
        ((hp.mul (hu.continuous.pow 2).continuousOn).intervalIntegrable_of_Icc hab)
        ((hp.mul continuousOn_const).intervalIntegrable_of_Icc hab)
        (fun x hx => mul_le_mul_of_nonneg_left (hvalue x hx) (hpos x hx).le)
    _ = _ := by rw [intervalIntegral.integral_mul_const]; ring

theorem tail_poincare_of_mean_zero {a b : ℝ} {p u : ℝ → ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hu : ContDiff ℝ 1 u)
    (hmean : (∫ x in a..b, p x * u x) = 0) :
    (∀ x ∈ Icc a b, u x ^ 2 ≤
      (∫ t in a..b, (p t)⁻¹) * ∫ t in a..b, p t * deriv u t ^ 2) ∧
      (∫ x in a..b, p x * u x ^ 2) ≤
        (∫ x in a..b, p x) * (∫ x in a..b, (p x)⁻¹) *
          ∫ x in a..b, p x * deriv u x ^ 2 := by
  obtain ⟨z, hz, huz⟩ := tail_exists_zero_of_weighted_mean_zero hab hp hpos
    hu.continuous.continuousOn hmean
  exact tail_poincare_of_zero hab.le hp hpos hu hz huz

/-- A trace bound at either end controls the intervening gap. The same lemma
handles a left or right trace, including a separate initial resistance edge. -/
theorem tail_gap_mass_of_trace {a b z A : ℝ} {p u : ℝ → ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hu : ContDiff ℝ 1 u)
    (hz : z ∈ Icc a b) (htrace : u z ^ 2 ≤ A) :
    (∫ x in a..b, p x * u x ^ 2) ≤
      2 * (∫ x in a..b, p x) * A +
      2 * (∫ x in a..b, p x) * (∫ x in a..b, (p x)⁻¹) *
        ∫ x in a..b, p x * deriv u x ^ 2 := by
  have hvalue (x : ℝ) (hx : x ∈ Icc a b) :
      u x ^ 2 ≤ 2 * A + 2 * ((∫ t in a..b, (p t)⁻¹) *
        ∫ t in a..b, p t * deriv u t ^ 2) := by
    have hd := tail_value_difference_sq_le hab hp hpos hu hz hx
    nlinarith [sq_nonneg (u x - 2 * u z)]
  calc
    _ ≤ ∫ x in a..b, p x * (2 * A + 2 * ((∫ t in a..b, (p t)⁻¹) *
        ∫ t in a..b, p t * deriv u t ^ 2)) :=
      intervalIntegral.integral_mono_on hab
        ((hp.mul (hu.continuous.pow 2).continuousOn).intervalIntegrable_of_Icc hab)
        ((hp.mul continuousOn_const).intervalIntegrable_of_Icc hab)
        (fun x hx => mul_le_mul_of_nonneg_left (hvalue x hx) (hpos x hx).le)
    _ = _ := by rw [intervalIntegral.integral_mul_const]; ring

end ContinuousFlexibility.Radial
