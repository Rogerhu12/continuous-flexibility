module

public import ContinuousFlexibility.Analysis.N06IntervalPrimitiveLp
public import ContinuousFlexibility.Analysis.SmoothCompactL2Density
public import Mathlib.Topology.Sequences

/-!
# Smooth H2 approximation with arbitrary endpoint values

The second derivative is approximated in L2 by smooth functions and then
integrated twice. The two constants are the original value and derivative
at zero. Thus neither the original representative nor its approximants
are required to satisfy a boundary condition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

/-- An actual L2 function on the unit interval admits a sequence of globally
smooth representatives converging in that same L2 space. -/
theorem n06_unit_exists_smooth_L2_sequence {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃ g : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      ∃ hg : ∀ n, MemLp (g n) 2 (volume.restrict (Ioo (0 : ℝ) 1)),
        Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hf.toLp f)) := by
  have hfinite : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (0 : ℝ) 1 →
      (volume.restrict (Ioo (0 : ℝ) 1)) K < ⊤ := by
    intro K _ _
    exact lt_of_le_of_lt (measure_mono (subset_univ K)) (by
      simp [Measure.restrict_apply_univ, Real.volume_Ioo])
  have hdense := smoothCompactL2Submodule_dense isOpen_Ioo
    (ae_restrict_mem measurableSet_Ioo :
      ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), x ∈ Ioo (0 : ℝ) 1) hfinite
  obtain ⟨G, hG, hGlim⟩ := mem_closure_iff_seq_limit.mp (hdense (hf.toLp f))
  have hrep : ∀ n : ℕ, ∃ g : ℝ → ℝ,
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo (0 : ℝ) 1 ∧
        (G n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := hG
  choose g hg hgc hgs hgae using hrep
  have hg₂ : ∀ n, MemLp (g n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun n => interval_memLp_of_continuous (hg n).continuous
  have heq (n : ℕ) : (hg₂ n).toLp (g n) = G n := by
    apply Lp.ext
    exact (hg₂ n).coeFn_toLp.trans (hgae n).symm
  refine ⟨g, hg, hg₂, ?_⟩
  simpa only [heq] using hGlim

/-- A C1 representative with absolutely continuous first derivative and L2
second derivative admits actual globally smooth H2 approximants. -/
theorem n06_exists_smooth_H2_approximation {v : ℝ → ℝ}
    (hv : ContDiff ℝ 1 v)
    (hvdAC : AbsolutelyContinuousOnInterval (deriv v) 0 1)
    (hv₀ : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃ p : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (p n)) ∧
      ∃ hp₀ : ∀ n, MemLp (p n) 2 (volume.restrict (Ioo (0 : ℝ) 1)),
      ∃ hp₁ : ∀ n, MemLp (deriv (p n)) 2 (volume.restrict (Ioo (0 : ℝ) 1)),
      ∃ hp₂ : ∀ n, MemLp (deriv (deriv (p n))) 2
          (volume.restrict (Ioo (0 : ℝ) 1)),
        Tendsto (fun n => (hp₀ n).toLp (p n)) atTop (𝓝 (hv₀.toLp v)) ∧
        Tendsto (fun n => (hp₁ n).toLp (deriv (p n))) atTop
          (𝓝 (hv₁.toLp (deriv v))) ∧
        Tendsto (fun n => (hp₂ n).toLp (deriv (deriv (p n)))) atTop
          (𝓝 (hv₂.toLp (deriv (deriv v)))) := by
  obtain ⟨g, hg, hg₂, hglim⟩ := n06_unit_exists_smooth_L2_sequence hv₂
  let w : ℕ → ℝ → ℝ := fun n => n06SmoothPrimitive (deriv v 0) (g n)
  let p : ℕ → ℝ → ℝ := fun n => n06SmoothPrimitive (v 0) (w n)
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) :=
    n06SmoothPrimitive_contDiff _ (hg n)
  have hp (n : ℕ) : ContDiff ℝ ∞ (p n) :=
    n06SmoothPrimitive_contDiff _ (hw n)
  have hwder (n : ℕ) : deriv (w n) = g n :=
    n06SmoothPrimitive_deriv _ (hg n).continuous
  have hpder (n : ℕ) : deriv (p n) = w n :=
    n06SmoothPrimitive_deriv _ (hw n).continuous
  have hpder₂ (n : ℕ) : deriv (deriv (p n)) = g n := by
    rw [hpder n, hwder n]
  have hw₂ (n : ℕ) : MemLp (w n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    interval_memLp_of_continuous (hw n).continuous
  have hp₀ (n : ℕ) : MemLp (p n) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    interval_memLp_of_continuous (hp n).continuous
  have hp₁ (n : ℕ) : MemLp (deriv (p n)) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [hpder n]
    exact hw₂ n
  have hp₂ (n : ℕ) : MemLp (deriv (deriv (p n))) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [hpder₂ n]
    exact hg₂ n
  have hwbound (n : ℕ) :
      ‖(hw₂ n).toLp (w n) - hv₁.toLp (deriv v)‖ ≤
        ‖(hg₂ n).toLp (g n) - hv₂.toLp (deriv (deriv v))‖ :=
    n06_primitive_toLp_sub_norm_le hvdAC (hg n).continuous hv₁ hv₂
  have hwlim : Tendsto (fun n => (hw₂ n).toLp (w n)) atTop
      (𝓝 (hv₁.toLp (deriv v))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hwbound
      (tendsto_iff_norm_sub_tendsto_zero.mp hglim)
  have hvAC : AbsolutelyContinuousOnInterval v 0 1 :=
    hv.contDiffOn.absolutelyContinuousOnInterval
  have hpbound (n : ℕ) :
      ‖(hp₀ n).toLp (p n) - hv₀.toLp v‖ ≤
        ‖(hw₂ n).toLp (w n) - hv₁.toLp (deriv v)‖ :=
    n06_primitive_toLp_sub_norm_le hvAC (hw n).continuous hv₀ hv₁
  have hplim : Tendsto (fun n => (hp₀ n).toLp (p n)) atTop (𝓝 (hv₀.toLp v)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hpbound
      (tendsto_iff_norm_sub_tendsto_zero.mp hwlim)
  have hpeq₁ (n : ℕ) : (hp₁ n).toLp (deriv (p n)) = (hw₂ n).toLp (w n) :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun (hpder n) x)
  have hpeq₂ (n : ℕ) : (hp₂ n).toLp (deriv (deriv (p n))) = (hg₂ n).toLp (g n) :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun (hpder₂ n) x)
  refine ⟨p, hp, hp₀, hp₁, hp₂, hplim, ?_, ?_⟩
  · simpa only [hpeq₁] using hwlim
  · simpa only [hpeq₂] using hglim

end ContinuousFlexibility.Analysis
