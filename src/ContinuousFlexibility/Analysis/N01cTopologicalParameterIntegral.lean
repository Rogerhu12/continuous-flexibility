module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compact-time integrals with arbitrary topological parameters

Joint continuity on a parameter set times a compact interval gives
continuity of its actual interval integral. The parameter space has no
norm or local compactness hypothesis. The primitive wrapper also allows
the time endpoint to vary, by the actual affine change of variables.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology Interval

variable {X F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem continuousOn_parametric_intervalIntegral_topological
    {f : X → ℝ → F} {U : Set X} {a b : ℝ}
    (hf : ContinuousOn f.uncurry (U ×ˢ uIcc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, f x t) U := by
  have hi (x : X) (hx : x ∈ U) : IntervalIntegrable (f x) volume a b :=
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx, ht⟩)).intervalIntegrable
  intro q hq
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_mul_lt hε |b - a|
  obtain ⟨V, hV, hclose⟩ :
      ∃ V ∈ 𝓝[U] q, ∀ x ∈ V, ∀ t ∈ uIcc a b,
        dist (f x t) (f q t) < δ :=
    isCompact_uIcc.mem_uniformity_of_prod hf hq (Metric.dist_mem_uniformity hδ)
  filter_upwards [hV, self_mem_nhdsWithin] with x hx hxU
  calc
    dist (∫ t in a..b, f x t) (∫ t in a..b, f q t) =
        ‖∫ t in a..b, f x t - f q t‖ := by
      rw [dist_eq_norm, intervalIntegral.integral_sub (hi x hxU) (hi q hq)]
    _ ≤ δ * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
        simpa only [dist_eq_norm] using
          (hclose x hx t (uIoc_subset_uIcc ht)).le)
    _ < ε := by simpa only [mul_comm] using hbound

theorem continuous_parametric_intervalIntegral_topological
    {f : X × ℝ → F} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun x => ∫ t in a..b, f (x, t)) :=
  continuousOn_univ.mp
    (continuousOn_parametric_intervalIntegral_topological
      (U := univ) (f := fun x t => f (x, t)) hf.continuousOn)

theorem continuous_parametric_primitive_topological
    {f : X × ℝ → F} (hf : Continuous f) (a : ℝ) :
    Continuous (fun p : X × ℝ => ∫ t in a..p.2, f (p.1, t)) := by
  have hi : Continuous (fun p : X × ℝ =>
      ∫ u in (0 : ℝ)..1, f (p.1, a + (p.2 - a) * u)) :=
    continuous_parametric_intervalIntegral_topological
      (hf.comp (continuous_fst.fst.prodMk
        (continuous_const.add
          ((continuous_fst.snd.sub continuous_const).mul continuous_snd)))) 0 1
  have hc : Continuous (fun p : X × ℝ =>
      (p.2 - a) • ∫ u in (0 : ℝ)..1, f (p.1, a + (p.2 - a) * u)) :=
    (continuous_snd.sub continuous_const).smul hi
  have he (p : X × ℝ) :
      (p.2 - a) • (∫ u in (0 : ℝ)..1, f (p.1, a + (p.2 - a) * u)) =
        ∫ t in a..p.2, f (p.1, t) := by
    simpa using intervalIntegral.smul_integral_comp_add_mul
      (fun t => f (p.1, t)) (a := (0 : ℝ)) (b := 1) (p.2 - a) a
  exact (funext he) ▸ hc

end ContinuousFlexibility.Analysis
