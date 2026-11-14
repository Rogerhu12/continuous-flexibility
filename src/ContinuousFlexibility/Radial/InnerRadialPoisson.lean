module

public import ContinuousFlexibility.Radial.InnerRadialODE
public import ContinuousFlexibility.Radial.InnerPositiveGap
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual positive radial gap Poisson problem

Positivity of the radial energy proves zero Dirichlet uniqueness and a
nonvanishing Dirichlet determinant. The actual conormal-flux initial-value
construction then solves arbitrary two-point boundary data. No restriction
on the gap length or assumption of Poisson solvability is imposed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

/-- A nonnegative logarithmic weight slope gives a nonnegative physical
potential term at every frequency. -/
theorem innerRadialGap_potential_nonneg {a b : ℝ} (ha : 0 < a)
    {w : ℝ → ℝ} (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r) (j : ℝ) :
    ∀ r ∈ Icc a b, 0 ≤ j ^ 2 * deriv w r / r := by
  intro r hr
  have hrad : 0 < r := ha.trans_le hr.1
  have hprod : 0 ≤ r * deriv w r := by
    simpa only [zero_mul] using (le_div_iff₀ (hpos r hr)).mp (hslope r hr)
  have hdw : 0 ≤ deriv w r := (mul_nonneg_iff_of_pos_left hrad).mp hprod
  exact div_nonneg (mul_nonneg (sq_nonneg j) hdw) hrad.le

/-- The positive gradient term forces every derivative to vanish for a
homogeneous zero-Dirichlet solution. This includes the endpoint derivatives,
and therefore controls the actual initial conormal flux. -/
theorem innerRadialGap_deriv_eq_zero {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r)
    (heq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0)
    (hua : u a = 0) (hub : u b = 0) :
    ∀ r ∈ Icc a b, deriv u r = 0 := by
  have hE : (∫ r in a..b, w r * deriv u r ^ 2 +
      j ^ 2 * deriv w r / r * u r ^ 2) = 0 := by
    simpa only [innerRadialGapEnergy, innerRadialGapBoundary, hua, hub,
      zero_mul, sub_self] using innerRadialGap_energy_eq_boundary hab.le ha hw hu heq
  have hdu := (contDiff_infty_iff_deriv.mp hu).2.continuous
  have hdw := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hc : ContinuousOn
      (fun r => w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2) (Icc a b) :=
    (hw.continuous.mul (hdu.pow 2)).continuousOn.add
      (((continuous_const.mul hdw).continuousOn.div continuous_id.continuousOn
        (fun r hr => (ha.trans_le hr.1).ne')).mul (hu.continuous.pow 2).continuousOn)
  have hpotential := innerRadialGap_potential_nonneg ha hpos hslope j
  intro r hr
  by_contra hne
  have hstrict : 0 < w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos (hpos r hr) (sq_pos_of_ne_zero hne))
      (mul_nonneg (hpotential r hr) (sq_nonneg _))
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab continuousOn_const hc
    (fun x hx => add_nonneg
      (mul_nonneg (hpos x (Ioc_subset_Icc_self hx)).le (sq_nonneg _))
      (mul_nonneg (hpotential x (Ioc_subset_Icc_self hx)) (sq_nonneg _)))
    ⟨r, hr, hstrict⟩
  simpa only [intervalIntegral.integral_zero, hE, lt_self_iff_false] using hi

/-- Zero Dirichlet values force the actual homogeneous radial function
to vanish throughout the retained interval. -/
theorem innerRadialGap_zero {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r)
    (heq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0)
    (hua : u a = 0) (hub : u b = 0) :
    ∀ r ∈ Icc a b, u r = 0 := by
  have hd := innerRadialGap_deriv_eq_zero hab ha hw hu hpos hslope heq hua hub
  intro r hr
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Icc a b) => hu.differentiable (by simp) x)
    (fun x hx => show ‖deriv u x‖ ≤ (0 : ℝ) by rw [hd x hx, norm_zero])
    (convex_Icc a b) (left_mem_Icc.mpr hab.le) hr
  have hn : ‖u r‖ ≤ 0 := by simpa only [hua, sub_zero, zero_mul] using h
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- The left-zero, unit-conormal-flux solution has a nonzero right value.
This is the actual radial Dirichlet determinant, without a short-gap
assumption or a guessed off-diagonal flux bound. -/
theorem innerRadialGap_dirichlet_determinant_ne_zero {a b j : ℝ}
    (hab : a < b) (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r)
    (heq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0)
    (hua : u a = 0) (hflux : w a * deriv u a = 1) : u b ≠ 0 := by
  intro hub
  have hd := innerRadialGap_deriv_eq_zero hab ha hw hu hpos hslope heq hua hub a
    (left_mem_Icc.mpr hab.le)
  rw [hd, mul_zero] at hflux
  exact zero_ne_one hflux

/-- Every pair of retained endpoint values has a genuine homogeneous
radial Poisson solution. The two initial-value solutions use the actual
weight and conormal flux, and energy positivity proves the needed
determinant rather than assuming its invertibility. -/
theorem exists_innerRadialGap_boundary {A l h B : ℝ}
    (hA : 0 < A) (hAl : A < l) (hlh : l < h) (hhB : h < B)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x)
    (hslope : ∀ x ∈ Icc l h, 0 ≤ x * deriv w x / w x)
    (j α β : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ u l = α ∧ u h = β ∧
      ∀ x ∈ Icc l h, radialJacobi (j ^ 2) w u x = 0 := by
  obtain ⟨f, hf, hfl, _, hfEq⟩ := exists_innerRadialODE_initial
    hA hAl hlh.le hhB hw hwnonneg hwpos j (left_mem_Icc.mpr hlh.le) α 0
  obtain ⟨g, hg, hgl, hfluxg, hgEq⟩ := exists_innerRadialODE_initial
    hA hAl hlh.le hhB hw hwnonneg hwpos j (left_mem_Icc.mpr hlh.le) 0 1
  have hpos : ∀ x ∈ Icc l h, 0 < w x :=
    fun x hx => hwpos x ⟨hAl.trans_le hx.1, hx.2.trans_lt hhB⟩
  have hgh := innerRadialGap_dirichlet_determinant_ne_zero hlh (hA.trans hAl)
    hw hg hpos hslope hgEq hgl hfluxg
  let c : ℝ := (β - f h) / g h
  refine ⟨fun x => 1 * f x + c * g x,
    (contDiff_const.mul hf).add (contDiff_const.mul hg), ?_, ?_, ?_⟩
  · change 1 * f l + c * g l = α
    rw [hfl, hgl, mul_zero, add_zero, one_mul]
  · change 1 * f h + c * g h = β
    dsimp only [c]
    rw [div_mul_cancel₀ _ hgh, one_mul]
    ring
  · intro x hx
    rw [innerRadialJacobi_linear_combination hw hf hg,
      hfEq x hx, hgEq x hx, mul_zero, mul_zero, add_zero]

/-- Homogeneous radial Poisson solutions with the same two boundary
values agree on the whole retained interval. -/
theorem innerRadialGap_boundary_unique {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    {w u v : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r)
    (huEq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0)
    (hvEq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w v r = 0)
    (haEq : u a = v a) (hbEq : u b = v b) : EqOn u v (Icc a b) := by
  have hc : ContDiff ℝ ∞ (fun x => 1 * u x + (-1) * v x) :=
    (contDiff_const.mul hu).add (contDiff_const.mul hv)
  have hEq : ∀ x ∈ Icc a b,
      radialJacobi (j ^ 2) w (fun y => 1 * u y + (-1) * v y) x = 0 := by
    intro x hx
    rw [innerRadialJacobi_linear_combination hw hu hv,
      huEq x hx, hvEq x hx, mul_zero, mul_zero, add_zero]
  have hz := innerRadialGap_zero hab ha hw hc hpos hslope hEq
    (by rw [haEq]; ring) (by rw [hbEq]; ring)
  intro x hx
  have h := hz x hx
  linarith only [h]

end ContinuousFlexibility.Radial
