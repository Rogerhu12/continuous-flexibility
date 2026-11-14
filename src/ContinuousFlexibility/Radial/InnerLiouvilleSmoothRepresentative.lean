module

public import ContinuousFlexibility.Radial.MorseCellLiouville

/-!
# Smooth representatives through both retained endpoints

The inverse coordinate is taken on a slightly larger interval on which
the actual radius still has positive derivative. Such an interval is
derived from the retained positivity hypotheses. This avoids extending
the endpoint inverse by an arbitrary constant and proves genuine local
smoothness and derivatives at both cuts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem exists_innerLiouville_positive_extension {R s : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Icc (a - δ) (b + δ), 0 < R x ∧ 0 < deriv R x ∧ 0 < s x := by
  let O := {x : ℝ | 0 < R x ∧ 0 < deriv R x ∧ 0 < s x}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const hR.continuous).inter
      ((isOpen_lt continuous_const (contDiff_infty_iff_deriv.mp hR).2.continuous).inter
        (isOpen_lt continuous_const hs.continuous))
  obtain ⟨εa, hεa, ha⟩ := Metric.isOpen_iff.mp hO a (hp a (left_mem_Icc.mpr hab))
  obtain ⟨εb, hεb, hb⟩ := Metric.isOpen_iff.mp hO b (hp b (right_mem_Icc.mpr hab))
  let δ := min εa εb / 2
  have hδ : 0 < δ := div_pos (lt_min hεa hεb) (by norm_num)
  have hδa : δ < εa := by
    dsimp only [δ]
    linarith [min_le_left εa εb]
  have hδb : δ < εb := by
    dsimp only [δ]
    linarith [min_le_right εa εb]
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_cases hxa : x < a
  · apply ha
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxa.le)]
    linarith [hx.1]
  · by_cases hbx : b < x
    · apply hb
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hbx.le)]
      linarith [hx.2]
    · exact hp x ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩

/-- Every model field smooth at the closed retained interval has an
actual radial representative smooth at both endpoints. The equality
is local around each endpoint, so it also identifies the true traces
and derivatives, rather than only almost everywhere values. -/
theorem exists_innerLiouvilleSmoothRepresentative {R s p : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x) :
    ∃ u : ℝ → ℝ,
      (∀ x ∈ Icc a b, (fun y => u (R y)) =ᶠ[𝓝 x]
        (fun y => p y / (Real.sqrt lam * s y))) ∧
      (∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r) := by
  obtain ⟨δ, hδ, hext⟩ := exists_innerLiouville_positive_extension hab hR hs hp
  let X := morseCellModelCoordinate R (a - δ) (b + δ)
  let u : ℝ → ℝ := fun r => p (X r) / (Real.sqrt lam * s (X r))
  have hm := morseCell_strictMonoOn hR (fun y hy => (hext y hy).2.1)
  have hxext (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (a - δ) (b + δ) := by
    constructor <;> linarith [hx.1, hx.2]
  have hX (x : ℝ) (hx : x ∈ Icc a b) : X (R x) = x :=
    morseCellModelCoordinate_apply hm (Ioo_subset_Icc_self (hxext x hx))
  have hnear (x : ℝ) (hx : x ∈ Icc a b) :
      (fun y => u (R y)) =ᶠ[𝓝 x] (fun y => p y / (Real.sqrt lam * s y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (hxext x hx)] with y hy
    dsimp only [u, X]
    rw [morseCellModelCoordinate_apply hm (Ioo_subset_Icc_self hy)]
  have hregular (x : ℝ) (hx : x ∈ Icc a b) : ContDiffAt ℝ ∞ u (R x) := by
    have hi : ContDiffAt ℝ ∞ X (R x) :=
      morseCellModelCoordinate_contDiffAt hR (fun y hy => (hext y hy).2.1) (hxext x hx)
    have hq : ContDiffAt ℝ ∞ (fun y => p y / (Real.sqrt lam * s y)) (X (R x)) := by
      rw [hX x hx]
      exact (hpp x hx).div (contDiffAt_const.mul hs.contDiffAt)
        (mul_ne_zero (Real.sqrt_pos.mpr hlam).ne' (hp x hx).2.2.ne')
    exact hq.comp (R x) hi
  refine ⟨u, hnear, ?_⟩
  intro r hr
  obtain ⟨hx, hRx⟩ := morseCellModelCoordinate_right hab hR
    (morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)) hr
  rw [← hRx]
  exact hregular _ hx

/-- The derivative is the actual radial derivative at either cut as
well as in the interior. -/
theorem innerLiouvilleSmoothRepresentative_deriv {R s p u : ℝ → ℝ} {lam x : ℝ}
    (hlam : 0 < lam) (hR : DifferentiableAt ℝ R x)
    (hs : DifferentiableAt ℝ s x) (hp : DifferentiableAt ℝ p x)
    (hu : DifferentiableAt ℝ u (R x)) (hspos : 0 < s x)
    (hne : (fun y => u (R y)) =ᶠ[𝓝 x]
      (fun y => p y / (Real.sqrt lam * s y))) :
    Real.sqrt lam * s x * deriv R x * deriv u (R x) =
      deriv p x - (deriv s x / s x) * p x := by
  have hd : Real.sqrt lam * s x ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.mpr hlam).ne' hspos.ne'
  have hc := hu.hasDerivAt.comp x hR.hasDerivAt
  have hq := hp.hasDerivAt.div (hs.hasDerivAt.const_mul (Real.sqrt lam)) hd
  have he := hc.unique (hq.congr_of_eventuallyEq hne)
  calc
    _ = (Real.sqrt lam * s x) * (deriv u (R x) * deriv R x) := by ring
    _ = (Real.sqrt lam * s x) *
        ((deriv p x * (Real.sqrt lam * s x) -
          p x * (Real.sqrt lam * deriv s x)) / (Real.sqrt lam * s x) ^ 2) := by rw [he]
    _ = _ := by
      field_simp [(Real.sqrt_pos.mpr hlam).ne', hspos.ne']
      <;> ring

end ContinuousFlexibility.Radial
