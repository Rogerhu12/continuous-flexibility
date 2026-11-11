import ContinuousFlexibility.Analysis.ProjectiveDifferential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Convex.Basic

/-!
# Nonlinear curve chain rules with a projective Fréchet source

The directional differential is jointly continuous in the base point and
direction on one fixed open convex set. The proof integrates the actual
derivative along a line segment. A compactness argument controls every
point of the segment while the direction itself varies and converges.
No norm is put on the projective source and no fixed-direction rule is
silently applied to a varying direction.

We first prove the Banach-output result and then assemble the actual
projective-output chain rule in all Banach coordinates. Higher Bastiani
derivatives and tame nonlinear estimates are not constructed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section BanachOutput

variable {V Y : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {U : Set V} {g : V → Y} {D : V → V →L[ℝ] Y}

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [CompleteSpace Y] in
/-- An actual line derivative at the shifted base point gives the actual
real derivative along the same affine line at an arbitrary parameter. -/
theorem hasDerivAt_affineLine_of_hasLineDerivAt {x v : V} {s : ℝ}
    (hg : HasLineDerivAt ℝ g (D (x + s • v) v) (x + s • v) v) :
    HasDerivAt (fun r : ℝ => g (x + r • v)) (D (x + s • v) v) s := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [add_smul, add_assoc] using hg.tendsto_slope_zero

omit [CompleteSpace Y] in
/-- Joint continuity really controls the derivative along the entire
fixed line segment, in an arbitrary fixed direction. -/
theorem continuousOn_bastiani_segment
    (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : V × V => D p.1 p.2) (U ×ˢ (univ : Set V)))
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) (v : V) :
    ContinuousOn (fun s : ℝ => D (x + s • (y - x)) v) (Icc (0 : ℝ) 1) := by
  apply hD.comp
    (((continuous_const.add (continuous_id.smul continuous_const)).prodMk
      continuous_const).continuousOn)
  intro s hs
  exact ⟨hUc.add_smul_sub_mem hx hy hs, mem_univ v⟩

/-- Actual Banach-valued fundamental theorem of calculus along a segment. -/
theorem bastiani_segment_integral
    (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : V × V => D p.1 p.2) (U ×ˢ (univ : Set V)))
    (hg : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ g (D x v) x v)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    (∫ s in (0 : ℝ)..1, D (x + s • (y - x)) (y - x)) = g y - g x := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => g (x + r • (y - x))) (D (x + s • (y - x)) (y - x)) s := by
    intro s hs
    apply hasDerivAt_affineLine_of_hasLineDerivAt
    exact hg _ (hUc.add_smul_sub_mem hx hy (by simpa only [uIcc_of_le zero_le_one] using hs)) _
  have hint := (continuousOn_bastiani_segment hUc hD hx hy (y - x)).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have he : x + (y - x) = y := by abel
  simpa only [one_smul, zero_smul, add_zero, he] using h

/-- Linearity of the genuine differential normalizes the segment FTC
identity by any real scalar, including an inverse step size. -/
theorem bastiani_segment_scaled_integral
    (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : V × V => D p.1 p.2) (U ×ˢ (univ : Set V)))
    (hg : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ g (D x v) x v)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) (a : ℝ) :
    a • (g y - g x) = ∫ s in (0 : ℝ)..1, D (x + s • (y - x)) (a • (y - x)) := by
  rw [← bastiani_segment_integral hUc hD hg hx hy, ← intervalIntegral.integral_smul]
  congr 1
  funext s
  exact ((D (x + s • (y - x))).map_smul a (y - x)).symm

omit [CompleteSpace Y] in
/-- Compact uniform control of the actual differential for simultaneously
varying small displacement and converging direction. No bounded-set norm
or operator norm on the Fréchet source is assumed. -/
theorem eventually_uniform_bastiani_segment
    {x v : V} (hDc : ContinuousAt (fun p : V × V => D p.1 p.2) (x, v))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : V × V in 𝓝 ((0 : V), v), ∀ s ∈ Icc (0 : ℝ) 1,
      ‖D (x + s • p.1) p.2 - D x v‖ < ε := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro s _
  have harg : Tendsto (fun p : (V × V) × ℝ => (x + p.2 • p.1.1, p.1.2))
      (𝓝 (((0 : V), v), s)) (𝓝 (x, v)) := by
    have hc : Continuous (fun p : (V × V) × ℝ => (x + p.2 • p.1.1, p.1.2)) :=
      (continuous_const.add (continuous_snd.smul continuous_fst.fst)).prodMk continuous_fst.snd
    simpa only [ContinuousAt, smul_zero, add_zero] using
      (hc.continuousAt (x := (((0 : V), v), s)))
  have hval := hDc.tendsto.comp harg
  have hnorm : Tendsto
      (fun p : (V × V) × ℝ => ‖D (x + p.2 • p.1.1) p.1.2 - D x v‖)
      (𝓝 (((0 : V), v), s)) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using (hval.sub_const (D x v)).norm
  exact hnorm (Iio_mem_nhds hε)

/-- Banach-output nonlinear curve chain rule. The extra curve continuity
is automatic for the projective source in the wrapper below. -/
theorem hasDerivAt_bastiani_comp_curve
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : V × V => D p.1 p.2) (U ×ˢ (univ : Set V)))
    (hg : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ g (D x v) x v)
    {c : ℝ → V} {dc : V} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hcc : ContinuousAt c t) (hct : c t ∈ U) :
    HasDerivAt (fun s : ℝ => g (c s)) (D (c t) dc) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hDc : ContinuousAt (fun p : V × V => D p.1 p.2) (c t, dc) :=
    (hD (c t, dc) ⟨hct, mem_univ dc⟩).continuousAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hct, mem_univ dc⟩)
  have hshift : Tendsto (fun h : ℝ => t + h) (𝓝[≠] (0 : ℝ)) (𝓝 t) := by
    simpa only [add_zero, id_eq] using (tendsto_const_nhds (x := t)).add
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  have hcurve : Tendsto (fun h : ℝ => c (t + h)) (𝓝[≠] (0 : ℝ)) (𝓝 (c t)) := by
    simpa only [Function.comp_def] using hcc.tendsto.comp hshift
  have hδ : Tendsto (fun h : ℝ => c (t + h) - c t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : V)) := by
    simpa only [sub_self] using hcurve.sub_const (c t)
  have hpair := hδ.prodMk_nhds hc
  have hunif := hpair.eventually (eventually_uniform_bastiani_segment hDc (half_pos hε))
  have hinU := hcurve.eventually (hU.mem_nhds hct)
  filter_upwards [hunif, hinU] with h hh hy
  rw [dist_eq_norm]
  have hint := (continuousOn_bastiani_segment hUc hD hct hy
    (h⁻¹ • (c (t + h) - c t))).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hconst : IntervalIntegrable (fun _ : ℝ => D (c t) dc) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hquot := bastiani_segment_scaled_integral hUc hD hg hct hy h⁻¹
  have hrepr : h⁻¹ • (g (c (t + h)) - g (c t)) - D (c t) dc =
      ∫ s in (0 : ℝ)..1,
        D (c t + s • (c (t + h) - c t)) (h⁻¹ • (c (t + h) - c t)) - D (c t) dc := by
    rw [intervalIntegral.integral_sub hint hconst, ← hquot]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  rw [hrepr]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ε / 2)
    (f := fun s : ℝ =>
      D (c t + s • (c (t + h) - c t)) (h⁻¹ • (c (t + h) - c t)) - D (c t) dc)
    (fun s hs => (hh s (by
      simp only [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩)).le)
  have hbound' : ‖∫ s in (0 : ℝ)..1,
      D (c t + s • (c (t + h) - c t)) (h⁻¹ • (c (t + h) - c t)) - D (c t) dc‖ ≤ ε / 2 := by
    simpa only [sub_zero, abs_one, mul_one] using hbound
  exact hbound'.trans_lt (half_lt_self hε)

end BanachOutput

section ProjectiveSource

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
variable {bond : ∀ n, E (n + 1) →L[ℝ] E n}
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The Banach-output chain rule for an actual projective Fréchet curve;
there is no independent curve-continuity hypothesis. -/
theorem hasDerivAt_bastiani_comp_projective_curve
    {U : Set (ProjectiveLimit E bond)} {g : ProjectiveLimit E bond → Y}
    {D : ProjectiveLimit E bond → ProjectiveLimit E bond →L[ℝ] Y}
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : ProjectiveLimit E bond × ProjectiveLimit E bond => D p.1 p.2)
      (U ×ˢ univ))
    (hg : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ g (D x v) x v)
    {c : ℝ → ProjectiveLimit E bond} {dc : ProjectiveLimit E bond} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U) :
    HasDerivAt (fun s : ℝ => g (c s)) (D (c t) dc) t :=
  hasDerivAt_bastiani_comp_curve hU hUc hD hg hc hc.continuousAt hct

variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
variable {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

/-- Genuine nonlinear curve chain rule with projective Fréchet source
and target, proved through the actual Banach derivatives in every output
coordinate. The same fixed open convex domain serves all coordinates. -/
theorem HasProjectiveCurveDerivAt.bastiani_comp
    {U : Set (ProjectiveLimit E bond)} {g : ProjectiveLimit E bond → ProjectiveLimit F fbond}
    {D : ProjectiveLimit E bond → ProjectiveLimit E bond →L[ℝ] ProjectiveLimit F fbond}
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : ProjectiveLimit E bond × ProjectiveLimit E bond => D p.1 p.2)
      (U ×ˢ univ))
    (hg : ∀ x ∈ U, ∀ v, HasProjectiveLineDerivAt g (D x v) x v)
    {c : ℝ → ProjectiveLimit E bond} {dc : ProjectiveLimit E bond} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U) :
    HasProjectiveCurveDerivAt (fun s : ℝ => g (c s)) (D (c t) dc) t := by
  apply (hasProjectiveCurveDerivAt_iff_levels _ _ _).mpr
  intro n
  let P := projectiveCoordinate F fbond n
  have hDn : ContinuousOn
      (fun p : ProjectiveLimit E bond × ProjectiveLimit E bond => (P.comp (D p.1)) p.2)
      (U ×ˢ univ) := P.continuous.comp_continuousOn hD
  have hgn : ∀ x ∈ U, ∀ v,
      HasLineDerivAt ℝ (fun y => P (g y)) ((P.comp (D x)) v) x v := by
    intro x hx v
    exact (hasProjectiveLineDerivAt_iff_levels g (D x v) x v).mp (hg x hx v) n
  exact hasDerivAt_bastiani_comp_projective_curve hU hUc hDn hgn hc hct

/-- The nonlinear directional chain rule is a consequence of the genuine
curve theorem. The outer map has the jointly continuous differential;
the inner map supplies its actual derivative along the given line. -/
theorem HasProjectiveLineDerivAt.bastiani_comp
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {f : X → ProjectiveLimit E bond} {df : ProjectiveLimit E bond} {x v : X}
    {U : Set (ProjectiveLimit E bond)} {g : ProjectiveLimit E bond → ProjectiveLimit F fbond}
    {D : ProjectiveLimit E bond → ProjectiveLimit E bond →L[ℝ] ProjectiveLimit F fbond}
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : ProjectiveLimit E bond × ProjectiveLimit E bond => D p.1 p.2)
      (U ×ˢ univ))
    (hg : ∀ y ∈ U, ∀ w, HasProjectiveLineDerivAt g (D y w) y w)
    (hf : HasProjectiveLineDerivAt f df x v) (hfx : f x ∈ U) :
    HasProjectiveLineDerivAt (fun y => g (f y)) (D (f x) df) x v := by
  have hbase : (fun t : ℝ => f (x + t • v)) 0 ∈ U := by
    simpa only [zero_smul, add_zero] using hfx
  have h := HasProjectiveCurveDerivAt.bastiani_comp hU hUc hD hg hf hbase
  simpa only [HasProjectiveLineDerivAt, zero_smul, add_zero] using h

end ProjectiveSource

end ContinuousFlexibility.Analysis
