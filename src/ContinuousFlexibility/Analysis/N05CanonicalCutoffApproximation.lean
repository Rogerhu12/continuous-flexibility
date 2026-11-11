import ContinuousFlexibility.Analysis.N05CanonicalZeroExtension
import ContinuousFlexibility.Analysis.IntervalLayerCutoff
import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compact radial cutoff approximation on a canonical cell

The explicit cutoffs take values in `[0,1]`, have compact support strictly
inside the actual radial interval, and eventually equal one at each
interior point. Multiplication by them converges strongly on the actual
canonical L² space. The same cutoff preserves every angular weak
derivative pair.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def n05CanonicalCutoffWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem n05CanonicalCutoffWidth_pos (n : ℕ) : 0 < n05CanonicalCutoffWidth n := by
  unfold n05CanonicalCutoffWidth
  positivity

theorem n05CanonicalCutoffWidth_tendsto :
    Tendsto n05CanonicalCutoffWidth atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def n05CanonicalRadialCutoffFunction (a b : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  intervalLayerThreshold (n05CanonicalCutoffWidth n) (r - a) *
    intervalLayerThreshold (n05CanonicalCutoffWidth n) (b - r)

theorem n05CanonicalRadialCutoffFunction_contDiff (a b : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (n05CanonicalRadialCutoffFunction a b n) :=
  ((contDiff_intervalLayerThreshold _).comp (contDiff_id.sub contDiff_const)).mul
    ((contDiff_intervalLayerThreshold _).comp (contDiff_const.sub contDiff_id))

theorem n05CanonicalRadialCutoffFunction_bounds (a b : ℝ) (n : ℕ) (r : ℝ) :
    0 ≤ n05CanonicalRadialCutoffFunction a b n r ∧
      n05CanonicalRadialCutoffFunction a b n r ≤ 1 := by
  have hl := intervalLayerThreshold_bounds (n05CanonicalCutoffWidth n) (r - a)
  have hr := intervalLayerThreshold_bounds (n05CanonicalCutoffWidth n) (b - r)
  exact ⟨mul_nonneg hl.1 hr.1,
    (mul_le_mul_of_nonneg_left hr.2 hl.1).trans (by simpa only [mul_one] using hl.2)⟩

theorem n05CanonicalRadialCutoffFunction_abs_le (a b : ℝ) (n : ℕ) (r : ℝ) :
    |n05CanonicalRadialCutoffFunction a b n r| ≤ 1 := by
  rw [abs_of_nonneg (n05CanonicalRadialCutoffFunction_bounds a b n r).1]
  exact (n05CanonicalRadialCutoffFunction_bounds a b n r).2

theorem n05CanonicalRadialCutoffFunction_tsupport (a b : ℝ) (n : ℕ) :
    tsupport (n05CanonicalRadialCutoffFunction a b n) ⊆
      Icc (a + n05CanonicalCutoffWidth n) (b - n05CanonicalCutoffWidth n) := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  change n05CanonicalRadialCutoffFunction a b n r ≠ 0 at hr
  have hp := mul_ne_zero_iff.mp hr
  have hl : n05CanonicalCutoffWidth n < r - a :=
    lt_of_not_ge fun h => hp.1 (intervalLayerThreshold_zero (n05CanonicalCutoffWidth_pos n) h)
  have hh : n05CanonicalCutoffWidth n < b - r :=
    lt_of_not_ge fun h => hp.2 (intervalLayerThreshold_zero (n05CanonicalCutoffWidth_pos n) h)
  exact ⟨by linarith, by linarith⟩

theorem n05CanonicalRadialCutoffFunction_hasCompactSupport (a b : ℝ) (n : ℕ) :
    HasCompactSupport (n05CanonicalRadialCutoffFunction a b n) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (n05CanonicalRadialCutoffFunction_tsupport a b n)

theorem n05CanonicalRadialCutoffFunction_tsupport_subset (a b : ℝ) (n : ℕ) :
    tsupport (n05CanonicalRadialCutoffFunction a b n) ⊆ Ioo a b := by
  intro r hr
  have hh := n05CanonicalRadialCutoffFunction_tsupport a b n hr
  have hp := n05CanonicalCutoffWidth_pos n
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem n05CanonicalRadialCutoffFunction_eventually_one {a b r : ℝ}
    (hr : r ∈ Ioo a b) :
    ∀ᶠ n in atTop, n05CanonicalRadialCutoffFunction a b n r = 1 := by
  have hδ : 0 < min (r - a) (b - r) / 2 := by
    exact div_pos (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)) (by norm_num)
  filter_upwards [n05CanonicalCutoffWidth_tendsto.eventually (gt_mem_nhds hδ)] with n hn
  have hl : 2 * n05CanonicalCutoffWidth n ≤ r - a := by
    have hh := min_le_left (r - a) (b - r)
    linarith
  have hh : 2 * n05CanonicalCutoffWidth n ≤ b - r := by
    have hh := min_le_right (r - a) (b - r)
    linarith
  simp only [n05CanonicalRadialCutoffFunction,
    intervalLayerThreshold_one (n05CanonicalCutoffWidth_pos n) hl,
    intervalLayerThreshold_one (n05CanonicalCutoffWidth_pos n) hh, mul_one]

theorem n05CanonicalRadialCutoffFunction_tendsto {a b r : ℝ}
    (hr : r ∈ Ioo a b) :
    Tendsto (fun n => n05CanonicalRadialCutoffFunction a b n r) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (n05CanonicalRadialCutoffFunction_eventually_one hr).symm

def n05CanonicalRadialCutoffOperator (S : PhysicalSpacesData) (K : CanonicalData S)
    (m n : ℕ) : CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  n05CanonicalRadialMultiply S K m
    (n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n)
    (n05CanonicalRadialCutoffFunction_contDiff _ _ n).continuous 1
    (n05CanonicalRadialCutoffFunction_abs_le _ _ n)

theorem n05CanonicalRadialCutoffOperator_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m n : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalRadialCutoffOperator S K m n u : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        fun p => n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n p.1 * u p :=
  n05CanonicalRadialMultiply_ae S K m _ _ _ _ u

theorem n05CanonicalRadialCutoffOperator_norm_le (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (u : CanonicalL2 S K m) :
    ‖n05CanonicalRadialCutoffOperator S K m n u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using n05CanonicalRadialMultiply_norm_le S K m
    (n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n)
    (n05CanonicalRadialCutoffFunction_contDiff _ _ n).continuous 1
    (n05CanonicalRadialCutoffFunction_abs_le _ _ n) u

theorem n05CanonicalRadialCutoffOperator_even (S : PhysicalSpacesData)
    (K : CanonicalData S) (m n : ℕ) (u : CanonicalL2 S K m)
    (hu : n05CanonicalReflection S K m u = u) :
    n05CanonicalReflection S K m (n05CanonicalRadialCutoffOperator S K m n u) =
      n05CanonicalRadialCutoffOperator S K m n u :=
  n05CanonicalRadialMultiply_even S K m _ _ _ _ u hu

theorem n05WeakCanonicalAngularDerivative_radialCutoff {S : PhysicalSpacesData}
    {K : CanonicalData S} {m j : ℕ} {f g : CanonicalL2 S K m}
    (h : WeakCanonicalAngularDerivative S K m f g j) (n : ℕ) :
    WeakCanonicalAngularDerivative S K m
      (n05CanonicalRadialCutoffOperator S K m n f)
      (n05CanonicalRadialCutoffOperator S K m n g) j :=
  n05WeakCanonicalAngularDerivative_radialMultiply h _
    (n05CanonicalRadialCutoffFunction_contDiff _ _ n) 1
    (n05CanonicalRadialCutoffFunction_abs_le _ _ n)

theorem n05CanonicalRadialCutoffOperator_tendsto (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    Tendsto (fun n => n05CanonicalRadialCutoffOperator S K m n u) atTop (𝓝 u) := by
  let F : ℕ → PolarPoint → ℝ := fun n p =>
    n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n p.1 * u p
  have hF (n : ℕ) : MemLp (F n) 2 (canonicalMeasure S K m) :=
    spacesMemLp_bounded_mul (canonicalMeasure S K m)
      ((n05CanonicalRadialCutoffFunction_contDiff _ _ n).continuous.comp
        continuous_fst).aestronglyMeasurable
      (fun p => n05CanonicalRadialCutoffFunction_abs_le _ _ n p.1) (Lp.memLp u)
  have hg : MemLp (fun p => |u p|) 2 (canonicalMeasure S K m) := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp u).norm
  have hb : ∀ᶠ n in atTop, ∀ᵐ p ∂canonicalMeasure S K m, |F n p - u p| ≤ |u p| := by
    filter_upwards [] with n
    filter_upwards [] with p
    have hc := n05CanonicalRadialCutoffFunction_bounds (K.left m) (K.right m) n p.1
    have ha : |n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n p.1 - 1| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hc.2)]
      linarith [hc.1]
    calc
      |F n p - u p| =
          |n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n p.1 - 1| * |u p| := by
        dsimp only [F]
        rw [← sub_one_mul, abs_mul]
      _ ≤ 1 * |u p| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ = |u p| := one_mul _
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  have hl : ∀ᵐ p ∂canonicalMeasure S K m,
      Tendsto (fun n => F n p) atTop (𝓝 (u p)) := by
    filter_upwards [ha] with p hp
    simpa only [F, one_mul] using
      (n05CanonicalRadialCutoffFunction_tendsto hp.1).mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => u p) atTop (𝓝 (u p)))
  have ht := spaces_tendsto_toLp_of_dominated hF (Lp.memLp u) hg hb hl
  have he (n : ℕ) :
      n05CanonicalRadialCutoffOperator S K m n u = (hF n).toLp (F n) := by
    apply Lp.ext
    exact (n05CanonicalRadialCutoffOperator_ae S K m n u).trans (MemLp.coeFn_toLp (hF n)).symm
  simpa only [he, Lp.toLp_coeFn] using ht

end ContinuousFlexibility.Statements
