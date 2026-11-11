import ContinuousFlexibility.Radial.ReferenceNaturalKernel
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Extending radial tests by an affine squeeze

A smooth test whose ordinary support lies in an open finite interval may
have topological support at the endpoints. Expanding its argument about
the midpoint makes its support compact in the open interval. The
expansion factors lie in [1,2] and tend to one, so the tests and their
first two derivatives have uniform bounds on the closed interval. This
extends every L¹ scalar Jacobi pairing by dominated convergence.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def referenceSqueezeArg (D : ReferenceData) (c r : ℝ) : ℝ :=
  (D.a + D.b) / 2 + c * (r - (D.a + D.b) / 2)

def referenceSqueezedTest (D : ReferenceData) (c : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ψ (referenceSqueezeArg D c r)

theorem referenceSqueezedTest_contDiff (D : ReferenceData) (c : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (referenceSqueezedTest D c ψ) := by
  exact hψ.comp (contDiff_const.add
    (contDiff_const.mul (contDiff_id.sub contDiff_const)))

theorem referenceSqueezedTest_one (D : ReferenceData) (ψ : ℝ → ℝ) :
    referenceSqueezedTest D 1 ψ = ψ := by
  funext r
  unfold referenceSqueezedTest referenceSqueezeArg
  congr 1
  ring

theorem referenceSqueezedTest_compact {D : ReferenceData} (hab : D.a < D.b)
    {c : ℝ} (hc : 1 < c) {ψ : ℝ → ℝ}
    (hs : Function.support ψ ⊆ radialCore D) :
    HasCompactSupport (referenceSqueezedTest D c ψ) ∧
      tsupport (referenceSqueezedTest D c ψ) ⊆ radialCore D := by
  let m := (D.a + D.b) / 2
  let l := m + (D.a - m) / c
  let h := m + (D.b - m) / c
  have hcpos : 0 < c := zero_lt_one.trans hc
  have ham : D.a < m := by dsimp only [m]; linarith
  have hmb : m < D.b := by dsimp only [m]; linarith
  have hal : D.a < l := by
    change D.a < m + (D.a - m) / c
    rw [lt_add_iff_sub_lt]
    apply (lt_div_iff₀ hcpos).mpr
    have hp := mul_neg_of_neg_of_pos (sub_neg.mpr ham) (sub_pos.mpr hc)
    nlinarith only [hp]
  have hhb : h < D.b := by
    change m + (D.b - m) / c < D.b
    rw [add_lt_iff_lt_sub_left]
    apply (div_lt_iff₀ hcpos).mpr
    have hp := mul_pos (sub_pos.mpr hmb) (sub_pos.mpr hc)
    nlinarith only [hp]
  have hs' : Function.support (referenceSqueezedTest D c ψ) ⊆ Icc l h := by
    intro r hr
    have harg : referenceSqueezeArg D c r ∈ radialCore D :=
      hs (Function.mem_support.mpr (Function.mem_support.mp hr))
    change D.a < m + c * (r - m) ∧ m + c * (r - m) < D.b at harg
    have hl : (D.a - m) / c < r - m :=
      (div_lt_iff₀ hcpos).mpr (by nlinarith only [harg.1])
    have hh : r - m < (D.b - m) / c :=
      (lt_div_iff₀ hcpos).mpr (by nlinarith only [harg.2])
    constructor <;> dsimp only [l, h] <;> linarith only [hl, hh]
  refine ⟨HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs', ?_⟩
  have hclosure : tsupport (referenceSqueezedTest D c ψ) ⊆ Icc l h :=
    closure_minimal hs' isClosed_Icc
  intro r hr
  exact ⟨hal.trans_le (hclosure hr).1, (hclosure hr).2.trans_lt hhb⟩

private theorem hasDerivAt_referenceSqueezeArg (D : ReferenceData) (c r : ℝ) :
    HasDerivAt (referenceSqueezeArg D c) c r := by
  have h := (((hasDerivAt_id r).sub_const ((D.a + D.b) / 2)).const_mul c).const_add
    ((D.a + D.b) / 2)
  simpa only [referenceSqueezeArg, mul_one] using h

theorem deriv_referenceSqueezedTest (D : ReferenceData) (c : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    deriv (referenceSqueezedTest D c ψ) r =
      deriv ψ (referenceSqueezeArg D c r) * c :=
  ((hψ.differentiable (by simp) _).hasDerivAt.comp r
    (hasDerivAt_referenceSqueezeArg D c r)).deriv

theorem deriv_deriv_referenceSqueezedTest (D : ReferenceData) (c : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    deriv (deriv (referenceSqueezedTest D c ψ)) r =
      deriv (deriv ψ) (referenceSqueezeArg D c r) * c * c := by
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have he : deriv (referenceSqueezedTest D c ψ) =
      fun r => deriv ψ (referenceSqueezeArg D c r) * c :=
    funext (deriv_referenceSqueezedTest D c hψ)
  rw [he]
  exact (((hψ'.differentiable (by simp) _).hasDerivAt.comp r
    (hasDerivAt_referenceSqueezeArg D c r)).mul_const c).deriv

def referenceJacobiSqueezeExpr (D : ReferenceData) (J : ℝ)
    (w ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv w p.2 * (deriv ψ (referenceSqueezeArg D p.1 p.2) * p.1) +
    w p.2 * (deriv (deriv ψ) (referenceSqueezeArg D p.1 p.2) * p.1 * p.1) -
      J * deriv w p.2 / p.2 * ψ (referenceSqueezeArg D p.1 p.2)

theorem radialJacobi_referenceSqueezedTest (D : ReferenceData) (J c : ℝ)
    {w ψ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    radialJacobi J w (referenceSqueezedTest D c ψ) r =
      referenceJacobiSqueezeExpr D J w ψ (c, r) := by
  have hs := referenceSqueezedTest_contDiff D c hψ
  have hs' := (contDiff_infty_iff_deriv.mp hs).2
  have hd := ((hw.differentiable (by simp) r).hasDerivAt.mul
    (hs'.differentiable (by simp) r).hasDerivAt).deriv
  unfold radialJacobi
  change deriv (w * deriv (referenceSqueezedTest D c ψ)) r -
    J * deriv w r / r * referenceSqueezedTest D c ψ r = _
  rw [hd, deriv_referenceSqueezedTest D c hψ,
    deriv_deriv_referenceSqueezedTest D c hψ]
  rfl

private theorem referenceJacobiSqueezeExpr_continuousOn
    {D : ReferenceData} (ha : 0 < D.a) (J : ℝ)
    {w ψ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hψ : ContDiff ℝ ∞ ψ) :
    ContinuousOn (referenceJacobiSqueezeExpr D J w ψ)
      (Set.prod (Icc (1 : ℝ) 2) (Icc D.a D.b)) := by
  have hw' := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have hψ'' := (contDiff_infty_iff_deriv.mp hψ').2.continuous
  have harg : Continuous (fun p : ℝ × ℝ => referenceSqueezeArg D p.1 p.2) :=
    continuous_const.add (continuous_fst.mul (continuous_snd.sub continuous_const))
  have hpot : ContinuousOn (fun p : ℝ × ℝ => J * deriv w p.2 / p.2)
      (Set.prod (Icc (1 : ℝ) 2) (Icc D.a D.b)) := by
    exact (continuous_const.mul (hw'.comp continuous_snd)).continuousOn.div
      continuous_snd.continuousOn (fun p hp => (ha.trans_le hp.2.1).ne')
  exact (((hw'.comp continuous_snd).mul
    ((hψ'.continuous.comp harg).mul continuous_fst)).continuousOn.add
      ((hw.continuous.comp continuous_snd).mul
        (((hψ''.comp harg).mul continuous_fst).mul continuous_fst)).continuousOn).sub
    (hpot.mul (hψ.continuous.comp harg).continuousOn)

/-- Continuous functions of a compact parameter and the closed radial
interval may be paired against any actual integrable radial field. -/
private theorem reference_integral_param_tendsto {D : ReferenceData}
    {u : ℝ → ℝ} (hu : IntegrableOn u (radialCore D))
    {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Set.prod (Icc (1 : ℝ) 2) (Icc D.a D.b)))
    {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (1 : ℝ) 2)
    (hc₁ : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => ∫ r, u r * F (c n, r) ∂volume.restrict (radialCore D))
      atTop (𝓝 (∫ r, u r * F (1, r) ∂volume.restrict (radialCore D))) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  apply tendsto_integral_of_dominated_convergence (fun r => ‖u r‖ * B)
  · intro n
    have hcF : ContinuousOn (fun r => F (c n, r)) (radialCore D) :=
      hF.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨hc n, Ioo_subset_Icc_self hr⟩)
    exact hu.aestronglyMeasurable.mul (hcF.aestronglyMeasurable measurableSet_Ioo)
  · exact hu.norm.mul_const B
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB (c n, r) ⟨hc n, Ioo_subset_Icc_self hr⟩)
      (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have ht : Tendsto (fun n => (c n, r)) atTop
        (𝓝[Set.prod (Icc (1 : ℝ) 2) (Icc D.a D.b)] (1, r)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hc₁.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall (fun n => ⟨hc n, Ioo_subset_Icc_self hr⟩)⟩
    exact tendsto_const_nhds.mul
      ((hF (1, r) ⟨⟨le_rfl, by norm_num⟩, Ioo_subset_Icc_self hr⟩).tendsto.comp ht)

/-- Strictly interior smooth tests determine the pairing with every smooth
test supported in the open interval, even when its topological support
meets an endpoint. Both sides are genuine integrable radial fields. -/
theorem radialJacobi_weak_extend_support_tests {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (J : ℝ)
    {u v : ℝ → ℝ} (hu : IntegrableOn u (radialCore D))
    (hv : IntegrableOn v (radialCore D))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ radialCore D →
      (∫ r in D.a..D.b, u r * radialJacobi J D.w ψ r) =
        ∫ r in D.a..D.b, v r * ψ r)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ ⊆ radialCore D) :
    (∫ r in D.a..D.b, u r * radialJacobi J D.w ψ r) =
      ∫ r in D.a..D.b, v r * ψ r := by
  let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hc (n : ℕ) : 1 < c n ∧ c n ≤ 2 := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
    have hb : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ hn).mpr (by linarith only [Nat.cast_nonneg n])
    dsimp only [c]
    constructor <;> linarith only [hp, hb]
  have hc₁ : Tendsto c atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero] using ht
  have hleft := reference_integral_param_tendsto hu
    (referenceJacobiSqueezeExpr_continuousOn hgeom.1 J hgeom.2.2.1.1 hψ)
    (fun n => ⟨(hc n).1.le, (hc n).2⟩) hc₁
  have harg : Continuous (fun p : ℝ × ℝ => referenceSqueezeArg D p.1 p.2) :=
    continuous_const.add (continuous_fst.mul (continuous_snd.sub continuous_const))
  have hright := reference_integral_param_tendsto hv (hψ.continuous.comp harg).continuousOn
    (fun n => ⟨(hc n).1.le, (hc n).2⟩) hc₁
  have heq (n : ℕ) :
      (∫ r, u r * referenceJacobiSqueezeExpr D J D.w ψ (c n, r)
        ∂volume.restrict (radialCore D)) =
      ∫ r, v r * ψ (referenceSqueezeArg D (c n) r)
        ∂volume.restrict (radialCore D) := by
    obtain ⟨hcompact, hsupport⟩ := referenceSqueezedTest_compact hgeom.2.1 (hc n).1 hs
    have h := hweak (referenceSqueezedTest D (c n) ψ)
      (referenceSqueezedTest_contDiff D (c n) hψ) hcompact hsupport
    simpa only [radialJacobi_referenceSqueezedTest D J (c n) hgeom.2.2.1.1 hψ,
      referenceSqueezedTest, intervalIntegral.integral_of_le hgeom.2.1.le,
      integral_Ioc_eq_integral_Ioo, radialCore] using h
  have hsame : (fun n => ∫ r, u r * referenceJacobiSqueezeExpr D J D.w ψ (c n, r)
        ∂volume.restrict (radialCore D)) =
      (fun n => ∫ r, v r * ψ (referenceSqueezeArg D (c n) r)
        ∂volume.restrict (radialCore D)) := funext heq
  rw [hsame] at hleft
  have hlimit := tendsto_nhds_unique hleft hright
  have hone (r : ℝ) : referenceJacobiSqueezeExpr D J D.w ψ (1, r) =
      radialJacobi J D.w ψ r := by
    rw [← radialJacobi_referenceSqueezedTest D J 1 hgeom.2.2.1.1 hψ,
      referenceSqueezedTest_one]
  have hargone (r : ℝ) : referenceSqueezeArg D 1 r = r := by
    unfold referenceSqueezeArg
    ring
  simpa only [hone, hargone, intervalIntegral.integral_of_le hgeom.2.1.le,
    integral_Ioc_eq_integral_Ioo, radialCore] using hlimit

end ContinuousFlexibility.Radial
