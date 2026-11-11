import ContinuousFlexibility.Radial.TailFundamentalGreenRepresentation
import ContinuousFlexibility.Analysis.L2KernelExtension
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The actual tail Green formula for every weighted L² source

Every row of the fundamental kernel belongs to the actual weighted Hilbert
space: its left part is continuous on a compact interval and its right part
is a multiple of the natural solution.  Interior smooth sources are dense
for the finite physical tail measure.  The already constructed Dirichlet
resolvent therefore has its actual kernel representation for every source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- The weighted tail measure is concentrated on its open interval. -/
theorem deepTailMeasure_ae_mem (T : DeepTailData) :
    ∀ᵐ x ∂deepTailMeasure T, x ∈ Ioo T.entrance T.endpoint :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- Each actual fundamental-kernel row is square integrable.  This does not
require the entire tail measure to be finite. -/
theorem tailFundamentalGreenKernel_memLp_row
    {T : DeepTailData} {w u : ℝ → ℝ} {W : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 < T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hu : ContinuousOn u (Ico T.entrance T.endpoint))
    (huL2 : MemLp u 2 (deepTailMeasure T)) (x : ℝ) :
    MemLp (fun y => tailFundamentalGreenKernel
      T.entrance T.endpoint w u W x y) 2 (deepTailMeasure T) := by
  by_cases hx : x ∈ Ioo T.entrance T.endpoint
  · let R : ℝ → ℝ := fun y => w (min x y) * u (max x y) / W
    have hmin : MapsTo (fun y => min x y) (Ico T.entrance T.endpoint)
        (Ico T.entrance T.endpoint) := by
      intro y hy
      exact ⟨le_min hx.1.le hy.1, (min_le_left _ _).trans_lt hx.2⟩
    have hmax : MapsTo (fun y => max x y) (Ico T.entrance T.endpoint)
        (Ico T.entrance T.endpoint) := by
      intro y hy
      exact ⟨hx.1.le.trans (le_max_left _ _), max_lt hx.2 hy.2⟩
    have hR : ContinuousOn R (Ico T.entrance T.endpoint) :=
      ((hw.comp (continuous_const.min continuous_id).continuousOn hmin).mul
        (hu.comp (continuous_const.max continuous_id).continuousOn hmax)).div_const W
    have hRL2 : MemLp R 2 (deepTailMeasure T) :=
      tail_memLp_of_continuousOn_eq_mul_tail hp hp₀ hR hx huL2
        (C := w x / W) (by
          intro y hy
          dsimp only [R]
          rw [min_eq_left hy.1, max_eq_right hy.1]
          ring)
    apply (memLp_congr_ae (show
      (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y)
        =ᵐ[deepTailMeasure T] R from ?_)).mpr hRL2
    filter_upwards [deepTailMeasure_ae_mem T] with y hy
    exact tailFundamentalGreenKernel_eq hx hy
  · have heq : (fun y => tailFundamentalGreenKernel
        T.entrance T.endpoint w u W x y) = fun _ => (0 : ℝ) :=
      funext (tailFundamentalGreenKernel_eq_zero_of_notMem_left hx)
    rw [heq]
    exact memLp_zero

/-- Every L² source is integrable against every actual kernel row. -/
theorem tailFundamentalGreenKernel_mul_integrable_L2
    {T : DeepTailData} {w u : ℝ → ℝ} {W : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 < T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hu : ContinuousOn u (Ico T.entrance T.endpoint))
    (huL2 : MemLp u 2 (deepTailMeasure T)) (x : ℝ) (f : DeepTailL2 T) :
    Integrable (fun y => tailFundamentalGreenKernel
      T.entrance T.endpoint w u W x y * f y) (deepTailMeasure T) := by
  have hrow := tailFundamentalGreenKernel_memLp_row hp hp₀ hw hu huL2 x
  apply (L2.integrable_inner (𝕜 := ℝ) (hrow.toLp _) f).congr
  filter_upwards [MemLp.coeFn_toLp hrow] with y hy
  rw [Real.inner_apply, hy]
  ring

/-- Smooth functions supported compactly inside the tail form a dense
source class for its finite physical weighted measure. -/
theorem dense_tailInteriorSources (T : DeepTailData) [IsFiniteMeasure (deepTailMeasure T)] :
    Dense {f : DeepTailL2 T | ∃ ψ : ℝ → ℝ,
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ ∧ ContDiff ℝ ∞ ψ ∧
      HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo T.entrance T.endpoint} := by
  classical
  let S : Set (DeepTailL2 T) := {f | ∃ ψ : ℝ → ℝ,
    (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ ∧ ContDiff ℝ ∞ ψ ∧
    HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo T.entrance T.endpoint}
  let A : Set (DeepTailL2 T) := {f | ∃ ψ : ℝ → ℝ,
    (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ ∧ HasCompactSupport ψ ∧ ContDiff ℝ ∞ ψ}
  have hdense : Dense A := Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hsub : A ⊆ closure S := by
    intro f hf
    obtain ⟨ψ, hfψ, _, hψ⟩ := hf
    have hLp : MemLp ψ 2 (deepTailMeasure T) :=
      (memLp_congr_ae hfψ).mp (Lp.memLp f)
    let φ : ℝ → ℝ := (Ioo T.entrance T.endpoint).indicator ψ
    have hφLp : MemLp φ 2 (deepTailMeasure T) := hLp.indicator measurableSet_Ioo
    have hcutLp (n : ℕ) : MemLp (intervalCutoffTest T.entrance T.endpoint ψ n)
        2 (deepTailMeasure T) := intervalCutoffTest_memLp hψ.continuous hLp n
    have hzero (n : ℕ) {x : ℝ} (hx : x ∉ Ioo T.entrance T.endpoint) :
        intervalCutoffTest T.entrance T.endpoint ψ n x = 0 :=
      Function.notMem_support.mp fun hx' =>
        hx ((intervalCutoffTest_tsupport_subset T.entrance T.endpoint ψ n)
          ((subset_tsupport _) hx'))
    have hbound (n : ℕ) (x : ℝ) :
        |intervalCutoffTest T.entrance T.endpoint ψ n x - φ x| ≤ |ψ x| := by
      by_cases hx : x ∈ Ioo T.entrance T.endpoint
      · rw [φ, Set.indicator_of_mem hx]
        exact abs_intervalCutoffTest_sub_le _ _ _ _ _
      · rw [φ, Set.indicator_of_notMem hx, hzero n hx, sub_self, abs_zero]
        exact abs_nonneg _
    have hlim (x : ℝ) : Tendsto
        (fun n => intervalCutoffTest T.entrance T.endpoint ψ n x) atTop (𝓝 (φ x)) := by
      by_cases hx : x ∈ Ioo T.entrance T.endpoint
      · simpa only [φ, Set.indicator_of_mem hx, intervalCutoffTest, one_mul] using
          (tendsto_intervalTestCutoff hx).mul_const (ψ x)
      · simpa only [φ, Set.indicator_of_notMem hx, hzero _ hx] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hφf : hφLp.toLp φ = f := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp hφLp, hfψ, deepTailMeasure_ae_mem T] with x hφ hf hx
      rw [hφ, φ, Set.indicator_of_mem hx, hf]
    have ht := realL2_tendsto_toLp_of_dominated hcutLp hφLp hLp hbound hlim
    rw [hφf] at ht
    apply isClosed_closure.mem_of_tendsto ht
    apply Eventually.of_forall
    intro n
    apply subset_closure
    exact ⟨intervalCutoffTest T.entrance T.endpoint ψ n, MemLp.coeFn_toLp (hcutLp n),
      contDiff_intervalCutoffTest hψ n,
      intervalCutoffTest_hasCompactSupport _ _ _ _,
      intervalCutoffTest_tsupport_subset _ _ _ _⟩
  intro f
  exact (closure_minimal hsub isClosed_closure) (hdense f)

/-- The actual Dirichlet fundamental Green formula holds for every source
in the weighted Hilbert space, not just for smooth test sources. -/
theorem tailFundamentalGreen_L2_representation {T : DeepTailData}
    [IsFiniteMeasure (deepTailMeasure T)]
    (hT : DeepTailHypotheses T) (hI : TailFormIdentification T T.endpoint)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f))
    {u q w z : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (hua : u T.entrance ≠ 0)
    (hUnique : ∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x)
    (hwc : ContinuousOn w (Ico T.entrance T.endpoint))
    (hus : TailFirstOrderSystem T.p T.Λ u q (Ico T.entrance T.endpoint))
    (hws : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint))
    (hwa : w T.entrance = 0)
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, z x * u x - w x * q x = 1)
    (f : DeepTailL2 T) :
    (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ∫ y,
      tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y * f y
        ∂deepTailMeasure T := by
  have hTcopy := hT
  rcases hTcopy with ⟨hab, _, _, _, _, _, _, hp, hpos, _, _⟩
  have huc : ContinuousOn u (Ico T.entrance T.endpoint) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · subst x
      exact hu.1.continuousAt.continuousWithinAt
    · exact (hu.2.1.contDiffAt (isOpen_Ioo.mem_nhds ⟨hlt, hx.2⟩)).continuousAt.continuousWithinAt
  let K : ℝ → ℝ → ℝ := tailFundamentalGreenKernel T.entrance T.endpoint w u 1
  have hrow (x : ℝ) : MemLp (K x) 2 (deepTailMeasure T) :=
    tailFundamentalGreenKernel_memLp_row hp hpos hwc huc hu.2.2.1 x
  let row : ℝ → DeepTailL2 T := fun x => (hrow x).toLp (K x)
  have hpair (g : DeepTailL2 T) (x : ℝ) :
      inner ℝ (row x) g = ∫ y, K x y * g y ∂deepTailMeasure T := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hrow x)] with y hy
    rw [Real.inner_apply, hy]
    ring
  have hdense := dense_tailInteriorSources T
  have hrep : ∀ g : DeepTailL2 T,
      g ∈ {g : DeepTailL2 T | ∃ ψ : ℝ → ℝ,
        (g : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ ∧ ContDiff ℝ ∞ ψ ∧
        HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo T.entrance T.endpoint} →
      (G g : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => inner ℝ (row x) g := by
    intro g hg
    obtain ⟨ψ, hgψ, hψ, hcψ, hsψ⟩ := hg
    apply (tailFundamentalGreen_compact_representation hT hI G hG hu hua hUnique hwc
      hus hws hwa hW g ψ hψ hcψ hsψ hgψ).trans
    apply Eventually.of_forall
    intro x
    rw [hpair]
    apply integral_congr_ae
    filter_upwards [hgψ] with y hy
    rw [hy]
  exact (ae_eq_row_pairing_of_dense G row hdense hrep f).trans
    (Eventually.of_forall (hpair f))

end ContinuousFlexibility.Radial
