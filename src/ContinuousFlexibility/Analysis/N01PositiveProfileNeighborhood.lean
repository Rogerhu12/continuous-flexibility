module

public import ContinuousFlexibility.Analysis.StateNeighborhood
public import ContinuousFlexibility.Analysis.StateProfileRegularity
public import Mathlib.Topology.Algebra.Support

/-!
# One positive-profile neighborhood for every positive component

This module uses the strengthened main contract: the closed support of
the border control is compact and lies in the strict positive profile
region. A single bound for w * chi' / w' there fixes the allowed real
control parameter. Outside that closed support the perturbation has the
actual reference germ. Negative-component controls vanish on the whole
open positive region. The original state grading controls the real
coordinate, so the original base and one smaller radius work for every
positive component simultaneously.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A compact border supported in the strict positive derivative region
admits one parameter interval preserving every positive profile slope. -/
theorem exists_logProfile_positive_parameter
    {w χ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport χ)
    (hsupport : ∀ r ∈ tsupport χ, 0 < deriv w r) :
    ∃ η : ℝ, 0 < η ∧ ∀ ν : ℝ, |ν| < η → ∀ r : ℝ, 0 < deriv w r →
      0 < deriv (fun s => w s * Real.exp (ν * χ s)) r := by
  let R : ℝ → ℝ := fun r => w r * deriv χ r / deriv w r
  have hwd : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hχd : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hR : ContinuousOn R (tsupport χ) :=
    (hw.continuous.mul hχd).continuousOn.div hwd.continuousOn
      (fun r hr => (hsupport r hr).ne')
  have hK : IsCompact (tsupport χ) := hcompact
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hR
  let A : ℝ := |M| + 1
  have hA : 0 < A := add_pos_of_nonneg_of_pos (abs_nonneg M) zero_lt_one
  let η : ℝ := (1 / 2 : ℝ) / A
  have hη : 0 < η := div_pos (by norm_num) hA
  have hηA : η * A = (1 / 2 : ℝ) := div_mul_cancel₀ _ hA.ne'
  refine ⟨η, hη, ?_⟩
  intro ν hν r hrpos
  by_cases hr : r ∈ tsupport χ
  · have hRA : |R r| ≤ A := by
      have hb : |R r| ≤ M := by simpa only [Real.norm_eq_abs] using hM r hr
      exact hb.trans ((le_abs_self M).trans (by dsimp only [A]; linarith))
    have hsmall : |ν * R r| < (1 / 2 : ℝ) := calc
      _ = |ν| * |R r| := abs_mul _ _
      _ ≤ |ν| * A := mul_le_mul_of_nonneg_left hRA (abs_nonneg ν)
      _ < η * A := mul_lt_mul_of_pos_right hν hA
      _ = _ := hηA
    have hfactor : 0 < 1 + ν * R r := by
      have hh := (abs_lt.mp hsmall).1
      linarith
    have hd := ((hw.differentiable (by simp) r).hasDerivAt.fun_mul
      (((hχ.differentiable (by simp) r).hasDerivAt.const_mul ν).exp)).deriv
    have he : deriv (fun s => w s * Real.exp (ν * χ s)) r =
        Real.exp (ν * χ r) * (deriv w r * (1 + ν * R r)) := by
      rw [hd]
      dsimp only [R]
      field_simp [hrpos.ne']
      <;> ring
    rw [he]
    exact mul_pos (Real.exp_pos _) (mul_pos hrpos hfactor)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hr
    have he : (fun s => w s * Real.exp (ν * χ s)) =ᶠ[𝓝 r] w := by
      filter_upwards [hz] with s hs
      simp only [hs, Pi.zero_apply, mul_zero, Real.exp_zero, mul_one]
    rw [he.deriv_eq]
    exact hrpos

/-- All controls are supported on negative components, so on the open
positive region the actual profile has only its real metric parameter. -/
theorem stateProfile_eventuallyEq_metric_on_positive
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (hw : Continuous (deriv D.w))
    (x : AnnularState S) {r : ℝ} (hr : 0 < deriv D.w r) :
    stateProfile D S C x =ᶠ[𝓝 r]
      (fun s => D.w s * Real.exp (x.2.1 * D.chi s)) := by
  have hnear : ∀ᶠ s in 𝓝 r, 0 < deriv D.w s :=
    hw.continuousAt.eventually (Ioi_mem_nhds hr)
  filter_upwards [hnear] with s hs
  have hcontrol (m : ℕ) : C.control m s = 0 := by
    by_contra hm
    have hsm : s ∈ Ioo (C.left m) (C.right m) :=
      hC.support_subset m hm
    exact lt_asymm (hC.2.2.2.1 m s hsm) hs
  simp only [stateProfile, hcontrol, mul_zero, tsum_zero, add_zero]

private theorem metricCoordinate_le_nested_pairGrading
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (n : ℕ) (x : E × (ℝ × F)) :
    |x.2.1| ≤ pairGrading p (pairGrading realGrading q) n x := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply,
    realGrading, coe_normSeminorm, Real.norm_eq_abs]
  linarith [apply_nonneg (p n) x.1, apply_nonneg (q n) x.2.2]

/-- The actual real metric coordinate is controlled by every state seminorm. -/
theorem stateMetricCoordinate_abs_le_stateGrading
    (S : PhysicalSpacesData) {C : NonlinearGeometryData S}
    (href : C.referenceState.2.1 = 0) (n : ℕ) (x : AnnularState S) :
    |x.2.1| ≤ stateGrading S n (x - C.referenceState) := by
  have he : |(x - C.referenceState).2.1| ≤ stateGrading S n (x - C.referenceState) :=
    metricCoordinate_le_nested_pairGrading (heightPairGrading S)
      (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading)
      n (x - C.referenceState)
  simpa only [Prod.snd_sub, Prod.fst_sub, href, sub_zero] using he

/-- The original base and one smaller radius preserve the strict positive
profile type everywhere. In particular the radius is chosen before any
component, state, angle, or finite derivative order. This uses the main
RadialTrueBorder clause for tsupport, rather than the older support clause. -/
theorem n01_exists_common_positiveProfile_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base ε', ∀ r ∈ Ioo D.a D.b,
        0 < deriv D.w r → 0 < deriv (stateProfile D S C z.1) r := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.1.2.2.1.1
  have hborder : RadialTrueBorder D := hN.1.2.2.2.1
  obtain ⟨η, hη, hpositive⟩ := exists_logProfile_positive_parameter hw hborder.1
    hborder.2.1 (fun r hr => (hborder.2.2.1 hr).2)
  refine ⟨min ε η, lt_min hN.2.1 hη, min_le_left _ _, ?_⟩
  intro z hz r _ hr
  have hν : |z.1.2.1| < η :=
    ((stateMetricCoordinate_abs_le_stateGrading S hN.2.2.1.2.2.1 base z.1).trans_lt hz.1).trans_le
      (min_le_right _ _)
  have he := stateProfile_eventuallyEq_metric_on_positive hN.2.2.2.1
    (contDiff_infty_iff_deriv.mp hw).2.continuous z.1 hr
  rw [he.deriv_eq]
  exact hpositive z.1.2.1 hν r hr

end ContinuousFlexibility.Analysis
