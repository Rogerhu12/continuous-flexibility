import ContinuousFlexibility.Analysis.CylinderTestPairing
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Summation estimates for the trace extension

The pointwise sum of packets with summable L² norms represents the actual
Banach-space sum. A bounded function supported in a radial interval of length
two has a uniform cylinder L² bound, independently of the interval's centre.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators

theorem spaces_memLp_tsum_of_summable_norm {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : ℕ → X → ℝ) (hf : ∀ m, MemLp (f m) 2 μ)
    (hs : Summable (fun m => (eLpNorm (f m) 2 μ).toReal)) :
    MemLp (fun x => ∑' m, f m x) 2 μ ∧
      (eLpNorm (fun x => ∑' m, f m x) 2 μ).toReal ≤
        ∑' m, (eLpNorm (f m) 2 μ).toReal := by
  let F (m : ℕ) : Lp ℝ 2 μ := (hf m).toLp (f m)
  have hn (m : ℕ) : ‖F m‖ = (eLpNorm (f m) 2 μ).toReal := Lp.norm_toLp _ _
  have hsn : Summable (fun m => ‖F m‖) := by simpa only [hn] using hs
  have he : (⇑(∑' m, F m)) =ᵐ[μ] fun x => ∑' m, f m x := by
    filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hsn),
      ae_all_iff.mpr (fun m => MemLp.coeFn_toLp (hf m))] with x hx hfx
    exact hx.trans (tsum_congr fun m => hfx m)
  refine ⟨(memLp_congr_ae he).mp (Lp.memLp (∑' m, F m)), ?_⟩
  calc
    (eLpNorm (fun x => ∑' m, f m x) 2 μ).toReal = ‖∑' m, F m‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae he]
    _ ≤ ∑' m, ‖F m‖ := norm_tsum_le_tsum_norm hsn
    _ = _ := tsum_congr hn

def spacesTraceUnitStrip (center : ℝ) : Set PolarPoint :=
  Icc (center - 1) (center + 1) ×ˢ univ

theorem spacesTraceUnitStrip_measurable (center : ℝ) :
    MeasurableSet (spacesTraceUnitStrip center) := measurableSet_Icc.prod MeasurableSet.univ

theorem spacesTraceUnitStrip_measure (center : ℝ) :
    materialCylinderMeasure (spacesTraceUnitStrip center) = ENNReal.ofReal (2 * Real.pi) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [materialCylinderMeasure_eq_prod, spacesTraceUnitStrip, Measure.prod_prod,
    Real.volume_Icc]
  have ha : angleMeasure univ = ENNReal.ofReal Real.pi := by
    rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [ha]
  have he : center + 1 - (center - 1) = (2 : ℝ) := by ring
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

def spacesTraceStripConstant : ℝ :=
  ((ENNReal.ofReal (2 * Real.pi)) ^ (1 / (2 : ℝ≥0∞).toReal)).toReal

theorem spacesTraceStripConstant_nonneg : 0 ≤ spacesTraceStripConstant := ENNReal.toReal_nonneg

/-- A common bound for every unit radial strip in the actual cylinder measure. -/
theorem spaces_memLp_norm_le_of_unit_radial_support {g : PolarPoint → ℝ}
    (hg : AEStronglyMeasurable g materialCylinderMeasure) (center : ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ p, |g p| ≤ A)
    (hzero : ∀ p, p.1 ∉ Icc (center - 1) (center + 1) → g p = 0) :
    MemLp g 2 materialCylinderMeasure ∧
      (eLpNorm g 2 materialCylinderMeasure).toReal ≤ spacesTraceStripConstant * A := by
  let K := spacesTraceUnitStrip center
  have hK := spacesTraceUnitStrip_measurable center
  have hi : MemLp (K.indicator fun _ : PolarPoint => A) 2 materialCylinderMeasure :=
    memLp_indicator_const 2 hK A (Or.inr (by
      rw [spacesTraceUnitStrip_measure]
      exact ENNReal.ofReal_ne_top))
  have hdom (p : PolarPoint) : ‖g p‖ ≤ ‖(K.indicator fun _ : PolarPoint => A) p‖ := by
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA]
      exact hbound p
    · have hx : p.1 ∉ Icc (center - 1) (center + 1) := fun hx => hp ⟨hx, mem_univ _⟩
      rw [Set.indicator_of_notMem hp, hzero p hx, norm_zero]
  have hnorm := eLpNorm_mono (p := 2) hg hdom
  refine ⟨lt_of_le_of_lt hnorm hi, ?_⟩
  calc
    (eLpNorm g 2 materialCylinderMeasure).toReal ≤
        (eLpNorm (K.indicator fun _ : PolarPoint => A) 2 materialCylinderMeasure).toReal :=
      ENNReal.toReal_mono hi.eLpNorm_ne_top hnorm
    _ = spacesTraceStripConstant * A := by
      rw [eLpNorm_indicator_const hK.nullMeasurableSet (by norm_num) (by norm_num),
        spacesTraceUnitStrip_measure, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
        ENNReal.toReal_ofReal (abs_nonneg A), abs_of_nonneg hA]
      exact mul_comm _ _

end ContinuousFlexibility.Statements
