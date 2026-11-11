import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-!
# Compression of smooth interval tests

Precomposing a test supported in `(a,b)` with an affine expansion about the
midpoint moves its topological support strictly inside the interval. As
the expansion factors decrease to one, the test and its first two
derivatives converge pointwise to the original test.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

def intervalCompressionMap (a b λ x : ℝ) : ℝ :=
  (a + b) / 2 + λ * (x - (a + b) / 2)

def intervalTestCompression (a b λ : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ψ (intervalCompressionMap a b λ x)

def intervalCompressionScale (n : ℕ) : ℝ :=
  1 + 1 / ((n : ℝ) + 1)

theorem contDiff_intervalCompressionMap (a b λ : ℝ) :
    ContDiff ℝ ∞ (intervalCompressionMap a b λ) :=
  contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem hasDerivAt_intervalCompressionMap (a b λ x : ℝ) :
    HasDerivAt (intervalCompressionMap a b λ) λ x := by
  simpa only [intervalCompressionMap, mul_one] using
    (((hasDerivAt_id x).sub_const ((a + b) / 2)).const_mul λ).const_add ((a + b) / 2)

theorem contDiff_intervalTestCompression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a b λ : ℝ) : ContDiff ℝ ∞ (intervalTestCompression a b λ ψ) :=
  hψ.comp (contDiff_intervalCompressionMap a b λ)

theorem deriv_intervalTestCompression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a b λ : ℝ) :
    deriv (intervalTestCompression a b λ ψ) =
      fun x => λ * deriv ψ (intervalCompressionMap a b λ x) := by
  funext x
  have hd := ((hψ.differentiable (by simp) (intervalCompressionMap a b λ x)).hasDerivAt.comp
    x (hasDerivAt_intervalCompressionMap a b λ x)).deriv
  simpa only [intervalTestCompression, mul_comm] using hd

theorem secondDeriv_intervalTestCompression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a b λ : ℝ) :
    deriv (deriv (intervalTestCompression a b λ ψ)) =
      fun x => λ ^ 2 * deriv (deriv ψ) (intervalCompressionMap a b λ x) := by
  rw [deriv_intervalTestCompression hψ]
  funext x
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hd := (((hψ'.differentiable (by simp) (intervalCompressionMap a b λ x)).hasDerivAt.comp
    x (hasDerivAt_intervalCompressionMap a b λ x)).const_mul λ).deriv
  exact hd.trans (by ring)

/-- Both endpoints are handled by the midpoint distance estimate. -/
theorem tsupport_intervalTestCompression_subset {a b λ : ℝ} (hab : a < b) (hλ : 1 < λ)
    {ψ : ℝ → ℝ} (hψs : Function.support ψ ⊆ Ioo a b) :
    tsupport (intervalTestCompression a b λ ψ) ⊆ Ioo a b := by
  let m : ℝ := (a + b) / 2
  let R : ℝ := (b - a) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hλpos : 0 < λ := lt_trans zero_lt_one hλ
  have hpre : tsupport (intervalTestCompression a b λ ψ) ⊆
      (intervalCompressionMap a b λ) ⁻¹' Icc a b := by
    apply closure_minimal
    · intro x hx
      have hx' : intervalCompressionMap a b λ x ∈ Function.support ψ := hx
      exact ⟨(hψs hx').1.le, (hψs hx').2.le⟩
    · exact isClosed_Icc.preimage (contDiff_intervalCompressionMap a b λ).continuous
  intro x hx
  have hAx := hpre hx
  have habs : |intervalCompressionMap a b λ x - m| ≤ R := by
    apply abs_le.mpr
    dsimp only [m, R]
    constructor <;> linarith [hAx.1, hAx.2]
  have hmap : intervalCompressionMap a b λ x - m = λ * (x - m) := by
    dsimp only [intervalCompressionMap, m]
    ring
  rw [hmap, abs_mul, abs_of_pos hλpos] at habs
  have hinner : |x - m| < R := by
    by_contra hh
    have hge : R ≤ |x - m| := le_of_not_gt hh
    have hprod : 0 < (λ - 1) * |x - m| :=
      mul_pos (sub_pos.mpr hλ) (hR.trans_le hge)
    nlinarith
  obtain ⟨hleft, hright⟩ := abs_lt.mp hinner
  dsimp only [m, R] at hleft hright
  constructor <;> linarith

theorem hasCompactSupport_intervalTestCompression {a b λ : ℝ}
    (hab : a < b) (hλ : 1 < λ) {ψ : ℝ → ℝ}
    (hψs : Function.support ψ ⊆ Ioo a b) :
    HasCompactSupport (intervalTestCompression a b λ ψ) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    ((tsupport_intervalTestCompression_subset hab hλ hψs).trans Ioo_subset_Icc_self)

theorem intervalCompressionScale_bounds (n : ℕ) :
    1 < intervalCompressionScale n ∧ intervalCompressionScale n ≤ 2 := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hp : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
  have hl : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  dsimp only [intervalCompressionScale]
  constructor <;> linarith

theorem tendsto_intervalCompressionScale :
    Tendsto intervalCompressionScale atTop (𝓝 (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [intervalCompressionScale, add_zero] using
    (tendsto_const_nhds.add h : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1))
      atTop (𝓝 (1 + 0 : ℝ)))

theorem tendsto_intervalCompressionMap (a b x : ℝ) :
    Tendsto (fun n => intervalCompressionMap a b (intervalCompressionScale n) x)
      atTop (𝓝 x) := by
  have h : Tendsto (fun n => (a + b) / 2 +
      intervalCompressionScale n * (x - (a + b) / 2))
        atTop (𝓝 ((a + b) / 2 + 1 * (x - (a + b) / 2))) :=
    tendsto_const_nhds.add
      (tendsto_intervalCompressionScale.mul_const (x - (a + b) / 2))
  have he : (a + b) / 2 + (x - (a + b) / 2) = x := by ring
  simpa only [intervalCompressionMap, one_mul, he] using h

theorem tendsto_intervalTestCompression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a b x : ℝ) :
    Tendsto (fun n => intervalTestCompression a b (intervalCompressionScale n) ψ x)
      atTop (𝓝 (ψ x)) :=
  hψ.continuous.continuousAt.tendsto.comp (tendsto_intervalCompressionMap a b x)

theorem tendsto_deriv_intervalTestCompression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a b x : ℝ) :
    Tendsto (fun n => deriv (intervalTestCompression a b (intervalCompressionScale n) ψ) x)
      atTop (𝓝 (deriv ψ x)) := by
  simp_rw [deriv_intervalTestCompression hψ]
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have h := tendsto_intervalCompressionScale.mul
    (hψ'.continuous.continuousAt.tendsto.comp (tendsto_intervalCompressionMap a b x))
  simpa only [one_mul] using h

theorem tendsto_secondDeriv_intervalTestCompression {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a b x : ℝ) :
    Tendsto (fun n => deriv (deriv (intervalTestCompression a b (intervalCompressionScale n) ψ)) x)
      atTop (𝓝 (deriv (deriv ψ) x)) := by
  simp_rw [secondDeriv_intervalTestCompression hψ]
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have hψ'' := (contDiff_infty_iff_deriv.mp hψ').2
  have h := (tendsto_intervalCompressionScale.pow 2).mul
    (hψ''.continuous.continuousAt.tendsto.comp (tendsto_intervalCompressionMap a b x))
  simpa only [one_pow, one_mul] using h

end

end ContinuousFlexibility.Analysis
