import ContinuousFlexibility.Analysis.N01aJacobiTransfer
import ContinuousFlexibility.Analysis.N01aNegativeComponentTotalVariation

/-!
# Energy decay and the number of negative components

The backward Jacobi transfer exponent is the interval length plus a fixed
multiple of the actual total logarithmic variation. A finite cover of the
negative points then expresses that exponent in terms of the full drops of
the components, including components crossing an endpoint of the interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

theorem n01aJacobiEnergy_backward_transfer {D : ReferenceData}
    (hD : RadialProfileGeometry D) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b)
    (hJ : ∀ r ∈ Icc a b, Radial.radialJacobi 4 D.w u r = 0) :
    n01aJacobiEnergy u a ≤ n01aJacobiEnergy u b *
      Real.exp ((b - a) + (4 / D.a + 2) * ∫ r in a..b, |deriv D.w r / D.w r|) := by
  let κ : ℝ := 4 / D.a + 2
  have hκ : 0 < κ := by
    have hα : 0 < D.a := hD.1
    dsimp [κ]
    positivity
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < D.w r :=
    hD.2.2.2.2.1 r ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩
  have hc : ContinuousOn (fun r => |deriv D.w r / D.w r|) (Icc a b) :=
    ((contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn.div
      hw.continuous.continuousOn (fun r hr => (hp r hr).ne')).abs
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  have hnonneg : 0 ≤ ∫ r in a..b, (1 + κ * |deriv D.w r / D.w r|) :=
    intervalIntegral.integral_nonneg_of_forall hab
      (fun r => add_nonneg zero_le_one (mul_nonneg hκ.le (abs_nonneg _)))
  have hcost : |∫ r in b..a, (1 + κ * |deriv D.w r / D.w r|)| =
      (b - a) + κ * ∫ r in a..b, |deriv D.w r / D.w r| := by
    rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hnonneg,
      intervalIntegral.integral_add
        ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable a b)
        (hi.const_mul κ), intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      smul_eq_mul, mul_one]
  have htransfer := n01aJacobiEnergy_transfer hD.1 ha.1.le hab hw hu hp hJ
    (right_mem_Icc.mpr hab) (left_mem_Icc.mpr hab)
  change n01aJacobiEnergy u a ≤ n01aJacobiEnergy u b *
    Real.exp |∫ r in b..a, (1 + κ * |deriv D.w r / D.w r|)| at htransfer
  rw [hcost] at htransfer
  exact htransfer

theorem n01aJacobiEnergy_backward_component_transfer {D : ReferenceData}
    (hD : RadialProfileGeometry D) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b)
    (hJ : ∀ r ∈ Icc a b, Radial.radialJacobi 4 D.w u r = 0)
    (S : Finset (N01aNegativeComponent D))
    (hcover : ∀ r ∈ Ioo a b, deriv D.w r < 0 → ∃ J ∈ S, r ∈ J.interval) :
    n01aJacobiEnergy u a ≤ n01aJacobiEnergy u b *
      Real.exp ((b - a) + (4 / D.a + 2) *
        (Real.log (D.w b) - Real.log (D.w a) +
          2 * ∑ J ∈ S, (Real.log (D.w J.left) - Real.log (D.w J.right)))) := by
  have hκ : 0 ≤ 4 / D.a + 2 :=
    add_nonneg (div_nonneg (by norm_num) hD.1.le) (by norm_num)
  have hvariation := n01a_totalVariation_le_component_drops_of_cover hD ha hb hab S hcover
  exact (n01aJacobiEnergy_backward_transfer hD hu ha hb hab hJ).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (add_le_add_left
        (mul_le_mul_of_nonneg_left hvariation hκ) (b - a)))
      (n01aJacobiEnergy_nonneg u b))

/-- A concrete finite cover and pointwise energy decay force enough full
component drops. The quantities in the conclusion are ordinary scalars. -/
theorem n01a_component_energy_decay_bound {D : ReferenceData}
    (hD : RadialProfileGeometry D) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b)
    (hJ : ∀ r ∈ Icc a b, Radial.radialJacobi 4 D.w u r = 0)
    (S : Finset (N01aNegativeComponent D))
    (hcover : ∀ r ∈ Ioo a b, deriv D.w r < 0 → ∃ J ∈ S, r ∈ J.interval)
    {A c x L M : ℝ} (hA : 0 < A) (henergy : 0 < n01aJacobiEnergy u a)
    (hdecay : n01aJacobiEnergy u b ≤ A * Real.exp (-c * x ^ 3))
    (hlog : Real.log (D.w b) - Real.log (D.w a) ≤ L)
    (hdrop : ∀ J ∈ S, Real.log (D.w J.left) - Real.log (D.w J.right) ≤ M) :
    c * x ^ 3 ≤ (b - a) + (4 / D.a + 2) * (L + 2 * (S.card : ℝ) * M) +
      Real.log A - Real.log (n01aJacobiEnergy u a) := by
  have hκ : 0 ≤ 4 / D.a + 2 :=
    add_nonneg (div_nonneg (by norm_num) hD.1.le) (by norm_num)
  have hsum : (∑ J ∈ S, (Real.log (D.w J.left) - Real.log (D.w J.right))) ≤
      (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ J ∈ S, M := Finset.sum_le_sum hdrop
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hforced := n01a_energy_decay_forces_transfer
    (n01aJacobiEnergy u a) (n01aJacobiEnergy u b) A c x _ henergy hA
    (n01aJacobiEnergy_backward_component_transfer hD hu ha hb hab hJ S hcover) hdecay
  have hupper :
      Real.log (D.w b) - Real.log (D.w a) +
          2 * ∑ J ∈ S, (Real.log (D.w J.left) - Real.log (D.w J.right)) ≤
        L + 2 * (S.card : ℝ) * M := by
    have hh := add_le_add hlog (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [mul_assoc] using hh
  exact hforced.trans (sub_le_sub_right
    (add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_left hupper hκ) (b - a))
      (Real.log A)) (Real.log (n01aJacobiEnergy u a)))

/-- Cubic decay and quadratic cost per component give a linear count. -/
theorem n01a_linear_count_of_cubic_bound {c B x count : ℝ}
    (hc : 0 < c) (hB : 0 < B) (hx : 1 ≤ x) (hcount : 0 ≤ count)
    (hbound : c * x ^ 3 ≤ B * (1 + x ^ 2) * (count + 1)) :
    (c / (2 * B)) * x - 1 ≤ count := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hquad : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hquad hB.le) (by linarith : 0 ≤ count + 1)
  have hcancel : (c * x) * x ^ 2 ≤ (2 * B * (count + 1)) * x ^ 2 := by
    calc
      (c * x) * x ^ 2 = c * x ^ 3 := by ring
      _ ≤ B * (1 + x ^ 2) * (count + 1) := hbound
      _ ≤ B * (2 * x ^ 2) * (count + 1) := hcost
      _ = (2 * B * (count + 1)) * x ^ 2 := by ring
  have hlinear := (mul_le_mul_right (sq_pos_of_pos hxpos)).mp hcancel
  have hquot : (c / (2 * B)) * x ≤ count + 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hB)).mpr
    nlinarith only [hlinear]
  linarith

end ContinuousFlexibility.Statements
