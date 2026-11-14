module

public import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
public import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative
public import ContinuousFlexibility.Radial.TailKernelTestExtension

/-!
# The actual interior cutoffs in each original canonical L² space

Multiplication by the existing scalar cutoff converges strongly to the
identity on a unit canonical cylinder. A globally smooth periodic test
therefore has a sequence of genuine compact canonical tests, with no
condition on its values at the two endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The established scalar interior cutoff applied only in the radial
variable. It preserves the test's original angular period. -/
def n06InteriorTestCut (n : ℕ) (φ : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => intervalTestCutoff 0 1 n p.1 * φ p

theorem n06InteriorTestCut_contDiff (n : ℕ) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (n06InteriorTestCut n φ) :=
  ((contDiff_intervalTestCutoff 0 1 n).comp contDiff_fst).mul hφ

theorem n06InteriorTestCut_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : MemLp φ 2 (canonicalMeasure S K m)) (n : ℕ) :
    MemLp (n06InteriorTestCut n φ) 2 (canonicalMeasure S K m) := by
  apply hφ.of_le
    (((contDiff_intervalTestCutoff 0 1 n).continuous.comp continuous_fst).aestronglyMeasurable.mul
      hφ.aestronglyMeasurable)
  filter_upwards [] with p
  change ‖intervalTestCutoff 0 1 n p.1 * φ p‖ ≤ ‖φ p‖
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (intervalTestCutoff_nonneg 0 1 n p.1)]
  exact (mul_le_mul_of_nonneg_right (intervalTestCutoff_le_one 0 1 n p.1)
    (abs_nonneg (φ p))).trans_eq (one_mul _)

/-- Strong convergence holds for every actual L² field, not only for
smooth functions or functions with zero boundary values. -/
theorem n06InteriorTestCut_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : MemLp φ 2 (canonicalMeasure S K m)) :
    Tendsto (fun n => (n06InteriorTestCut_memLp hφ n).toLp (n06InteriorTestCut n φ))
      atTop (𝓝 (hφ.toLp φ)) := by
  have hdom : MemLp (fun p => |φ p|) 2 (canonicalMeasure S K m) := by
    simpa only [Real.norm_eq_abs] using hφ.norm
  apply spaces_tendsto_toLp_of_dominated
    (fun n => n06InteriorTestCut_memLp hφ n) hφ hdom
  · apply Eventually.of_forall
    intro n
    filter_upwards [] with p
    have hc : |intervalTestCutoff 0 1 n p.1 - 1| ≤ 1 := by
      apply abs_le.mpr
      constructor
      · linarith only [intervalTestCutoff_nonneg 0 1 n p.1]
      · linarith only [intervalTestCutoff_le_one 0 1 n p.1]
    calc
      |n06InteriorTestCut n φ p - φ p| =
          |intervalTestCutoff 0 1 n p.1 - 1| * |φ p| := by
        rw [← abs_mul]
        congr 1
        dsimp only [n06InteriorTestCut]
        ring
      _ ≤ 1 * |φ p| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = |φ p| := one_mul _
  · rw [canonicalMeasure, hl, hr]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    simpa only [n06InteriorTestCut, one_mul] using
      (tendsto_intervalTestCutoff hp.1).mul_const (φ p)

theorem n06InteriorTestCut_canonicalTest
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : Function.Periodic φ (0, Real.pi)) (n : ℕ) :
    CanonicalTest S K m (n06InteriorTestCut n φ) := by
  refine ⟨n06InteriorTestCut_contDiff n hφ, ?_,
    tsupport (intervalTestCutoff 0 1 n), intervalTestCutoff_hasCompactSupport 0 1 n, ?_, ?_⟩
  · intro p
    simp only [n06InteriorTestCut, Prod.fst_add, add_zero, hp p]
  · simpa only [hl, hr] using intervalTestCutoff_tsupport_subset 0 1 n
  · intro r hr θ
    simp only [n06InteriorTestCut, image_eq_zero_of_notMem_tsupport hr, zero_mul]

end ContinuousFlexibility.Analysis
