import ContinuousFlexibility.Analysis.N06IntervalPrimitiveBounds
import ContinuousFlexibility.Analysis.SmoothCompactL2Density
import Mathlib.Topology.Sequences

/-!
# Smooth approximation with genuine endpoint traces on any finite interval

Only the actual second derivative is approximated in L2. Integrating it
twice, with the original value and derivative at the left endpoint,
produces globally smooth functions converging in H2 and uniformly in C1
on the closed recorded interval. In particular both endpoint traces
converge, without imposing any zero boundary condition.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Smooth functions approximate the original L2 class on the actual
interval; no affine change of measure is used. -/
theorem n06_interval_exists_smooth_L2_sequence {a b : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) :
    ∃ g : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      ∃ hg : ∀ n, MemLp (g n) 2 (volume.restrict (Ioo a b)),
        Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hf.toLp f)) := by
  have hfinite : ∀ J : Set ℝ, IsCompact J → J ⊆ Ioo a b →
      (volume.restrict (Ioo a b)) J < ⊤ := by
    intro J _ _
    exact lt_of_le_of_lt (measure_mono (subset_univ J)) (by
      simp [Measure.restrict_apply_univ, Real.volume_Ioo])
  have hdense := smoothCompactL2Submodule_dense isOpen_Ioo
    (ae_restrict_mem measurableSet_Ioo :
      ∀ᵐ x ∂volume.restrict (Ioo a b), x ∈ Ioo a b) hfinite
  obtain ⟨G, hG, hGlim⟩ := mem_closure_iff_seq_limit.mp (hdense (hf.toLp f))
  have hrep : ∀ n : ℕ, ∃ g : ℝ → ℝ,
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo a b ∧
        (G n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] g := hG
  choose g hg hgc hgs hgae using hrep
  have hg₂ : ∀ n, MemLp (g n) 2 (volume.restrict (Ioo a b)) :=
    fun n => interval_memLp_of_continuous (hg n).continuous
  have heq (n : ℕ) : (hg₂ n).toLp (g n) = G n := by
    apply Lp.ext
    exact (hg₂ n).coeFn_toLp.trans (hgae n).symm
  refine ⟨g, hg, hg₂, ?_⟩
  simpa only [heq] using hGlim

/-- One smooth sequence retains the original L2 classes and controls
both genuine first jets on the entire closed interval. -/
structure N06IntervalH2Approximation (a b : ℝ) (v : ℝ → ℝ) where
  approx : ℕ → ℝ → ℝ
  smooth : ∀ n, ContDiff ℝ ∞ (approx n)
  value_memLp : MemLp v 2 (volume.restrict (Ioo a b))
  deriv_memLp : MemLp (deriv v) 2 (volume.restrict (Ioo a b))
  second_memLp : MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo a b))
  approx_memLp : ∀ n, MemLp (approx n) 2 (volume.restrict (Ioo a b))
  approx_deriv_memLp : ∀ n, MemLp (deriv (approx n)) 2 (volume.restrict (Ioo a b))
  approx_second_memLp : ∀ n, MemLp (deriv (deriv (approx n))) 2
    (volume.restrict (Ioo a b))
  value_tendsto : Tendsto (fun n => (approx_memLp n).toLp (approx n)) atTop
    (𝓝 (value_memLp.toLp v))
  deriv_tendsto : Tendsto (fun n => (approx_deriv_memLp n).toLp (deriv (approx n))) atTop
    (𝓝 (deriv_memLp.toLp (deriv v)))
  second_tendsto : Tendsto
    (fun n => (approx_second_memLp n).toLp (deriv (deriv (approx n)))) atTop
      (𝓝 (second_memLp.toLp (deriv (deriv v))))
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto : Tendsto error atTop (𝓝 0)
  value_error : ∀ n x, x ∈ Icc a b → ‖approx n x - v x‖ ≤ error n
  deriv_error : ∀ n x, x ∈ Icc a b → ‖deriv (approx n) x - deriv v x‖ ≤ error n
  left_value : ∀ n, approx n a = v a
  left_deriv : ∀ n, deriv (approx n) a = deriv v a

/-- The actual C1/AC/L2 representative supplies all smooth approximation
and trace data. No independent graph or boundary hypothesis is introduced. -/
theorem n06_interval_exists_smooth_H2_approximation {a b : ℝ} (hab : a ≤ b)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hvdAC : AbsolutelyContinuousOnInterval (deriv v) a b)
    (hv₀ : MemLp v 2 (volume.restrict (Ioo a b)))
    (hv₁ : MemLp (deriv v) 2 (volume.restrict (Ioo a b)))
    (hv₂ : MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo a b))) :
    Nonempty (N06IntervalH2Approximation a b v) := by
  obtain ⟨g, hg, hg₂, hglim⟩ := n06_interval_exists_smooth_L2_sequence hv₂
  let w : ℕ → ℝ → ℝ := fun n => n06IntervalPrimitive a (deriv v a) (g n)
  let p : ℕ → ℝ → ℝ := fun n => n06IntervalPrimitive a (v a) (w n)
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) :=
    n06IntervalPrimitive_contDiff _ _ (hg n)
  have hp (n : ℕ) : ContDiff ℝ ∞ (p n) :=
    n06IntervalPrimitive_contDiff _ _ (hw n)
  have hwder (n : ℕ) : deriv (w n) = g n :=
    n06IntervalPrimitive_deriv _ _ (hg n).continuous
  have hpder (n : ℕ) : deriv (p n) = w n :=
    n06IntervalPrimitive_deriv _ _ (hw n).continuous
  have hpder₂ (n : ℕ) : deriv (deriv (p n)) = g n := by
    rw [hpder n, hwder n]
  have hw₂ (n : ℕ) : MemLp (w n) 2 (volume.restrict (Ioo a b)) :=
    interval_memLp_of_continuous (hw n).continuous
  have hp₀ (n : ℕ) : MemLp (p n) 2 (volume.restrict (Ioo a b)) :=
    interval_memLp_of_continuous (hp n).continuous
  have hp₁ (n : ℕ) : MemLp (deriv (p n)) 2 (volume.restrict (Ioo a b)) := by
    rw [hpder n]
    exact hw₂ n
  have hp₂ (n : ℕ) : MemLp (deriv (deriv (p n))) 2
      (volume.restrict (Ioo a b)) := by
    rw [hpder₂ n]
    exact hg₂ n
  have hwbound (n : ℕ) :
      ‖(hw₂ n).toLp (w n) - hv₁.toLp (deriv v)‖ ≤ n06IntervalL2Unit a b ^ 2 *
        ‖(hg₂ n).toLp (g n) - hv₂.toLp (deriv (deriv v))‖ :=
    n06_interval_primitive_toLp_sub_norm_le hab hvdAC (hg n) hv₁ hv₂
  have hgerr : Tendsto (fun n =>
      ‖(hg₂ n).toLp (g n) - hv₂.toLp (deriv (deriv v))‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hglim
  have hwlim : Tendsto (fun n => (hw₂ n).toLp (w n)) atTop
      (𝓝 (hv₁.toLp (deriv v))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hwbound
      (by simpa only [mul_zero] using hgerr.const_mul (n06IntervalL2Unit a b ^ 2))
  have hwerr : Tendsto (fun n =>
      ‖(hw₂ n).toLp (w n) - hv₁.toLp (deriv v)‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hwlim
  have hvAC : AbsolutelyContinuousOnInterval v a b :=
    hv.contDiffOn.absolutelyContinuousOnInterval
  have hpbound (n : ℕ) :
      ‖(hp₀ n).toLp (p n) - hv₀.toLp v‖ ≤ n06IntervalL2Unit a b ^ 2 *
        ‖(hw₂ n).toLp (w n) - hv₁.toLp (deriv v)‖ :=
    n06_interval_primitive_toLp_sub_norm_le hab hvAC (hw n) hv₀ hv₁
  have hplim : Tendsto (fun n => (hp₀ n).toLp (p n)) atTop (𝓝 (hv₀.toLp v)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hpbound
      (by simpa only [mul_zero] using hwerr.const_mul (n06IntervalL2Unit a b ^ 2))
  have hpeq₁ (n : ℕ) : (hp₁ n).toLp (deriv (p n)) = (hw₂ n).toLp (w n) :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun (hpder n) x)
  have hpeq₂ (n : ℕ) : (hp₂ n).toLp (deriv (deriv (p n))) = (hg₂ n).toLp (g n) :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun (hpder₂ n) x)
  let error : ℕ → ℝ := fun n => n06IntervalL2Unit a b *
    (‖(hw₂ n).toLp (w n) - hv₁.toLp (deriv v)‖ +
      ‖(hg₂ n).toLp (g n) - hv₂.toLp (deriv (deriv v))‖)
  have he0 (n : ℕ) : 0 ≤ error n :=
    mul_nonneg (n06IntervalL2Unit_nonneg a b) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have helim : Tendsto error atTop (𝓝 0) := by
    simpa only [error, add_zero, mul_zero] using
      (hwerr.add hgerr).const_mul (n06IntervalL2Unit a b)
  have hevalue (n : ℕ) (x : ℝ) (hx : x ∈ Icc a b) : ‖p n x - v x‖ ≤ error n := by
    refine (n06_interval_primitive_sub_norm_le hvAC (hw n).continuous hv₁ hx).trans ?_
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
      (n06IntervalL2Unit_nonneg a b)
  have hederiv (n : ℕ) (x : ℝ) (hx : x ∈ Icc a b) :
      ‖deriv (p n) x - deriv v x‖ ≤ error n := by
    rw [hpder n]
    refine (n06_interval_primitive_sub_norm_le hvdAC (hg n).continuous hv₂ hx).trans ?_
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
      (n06IntervalL2Unit_nonneg a b)
  refine ⟨{
    approx := p
    smooth := hp
    value_memLp := hv₀
    deriv_memLp := hv₁
    second_memLp := hv₂
    approx_memLp := hp₀
    approx_deriv_memLp := hp₁
    approx_second_memLp := hp₂
    value_tendsto := hplim
    deriv_tendsto := ?_
    second_tendsto := ?_
    error := error
    error_nonneg := he0
    error_tendsto := helim
    value_error := hevalue
    deriv_error := hederiv
    left_value := ?_
    left_deriv := ?_
  }⟩
  · simpa only [hpeq₁] using hwlim
  · simpa only [hpeq₂] using hglim
  · intro n
    exact n06IntervalPrimitive_left a (v a) (w n)
  · intro n
    rw [hpder n]
    exact n06IntervalPrimitive_left a (deriv v a) (g n)

/-- The same sequence converges uniformly in value on the closed
interval, so it retains the genuine right as well as left trace. -/
theorem N06IntervalH2Approximation.value_uniformly
    {a b : ℝ} {v : ℝ → ℝ} (P : N06IntervalH2Approximation a b v) :
    TendstoUniformlyOn P.approx v atTop (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [P.error_tendsto.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  rw [dist_comm, dist_eq_norm]
  exact (P.value_error n x hx).trans_lt hn

/-- Uniform convergence also holds for the actual first derivatives. -/
theorem N06IntervalH2Approximation.deriv_uniformly
    {a b : ℝ} {v : ℝ → ℝ} (P : N06IntervalH2Approximation a b v) :
    TendstoUniformlyOn (fun n => deriv (P.approx n)) (deriv v) atTop (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [P.error_tendsto.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  rw [dist_comm, dist_eq_norm]
  exact (P.deriv_error n x hx).trans_lt hn

/-- In particular every genuine endpoint value and first derivative
converges; the proof does not replace either trace by an L2 value. -/
theorem N06IntervalH2Approximation.trace_tendsto
    {a b x : ℝ} {v : ℝ → ℝ} (P : N06IntervalH2Approximation a b v)
    (hx : x ∈ Icc a b) :
    Tendsto (fun n => P.approx n x) atTop (𝓝 (v x)) ∧
      Tendsto (fun n => deriv (P.approx n) x) atTop (𝓝 (deriv v x)) :=
  ⟨P.value_uniformly.tendsto_at hx, P.deriv_uniformly.tendsto_at hx⟩

end ContinuousFlexibility.Analysis
