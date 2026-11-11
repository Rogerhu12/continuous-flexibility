import ContinuousFlexibility.Radial.ZeroModeEndpointIntegrability
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Excluding nonzero endpoint limits in the actual output space

A radial output member cannot remain bounded away from zero on a right
endpoint interval. The proof uses its inverse-distance L2 control, finite
interval L2-to-L1 inclusion, and the actual nonintegrability of
`(b-r)⁻¹`. The lower bound is only required almost everywhere.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ENNReal
open ContinuousFlexibility.Statements

theorem zeroMode_right_lower_bound_impossible
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    {γ M : ℝ} (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (referenceRadialWeightedMeasure D γ (-M)))
    {l c : ℝ} (hla : D.a < l) (hlb : l < D.b) (hc : 0 < c)
    (hlow : ∀ᵐ r ∂volume.restrict (Ioo l D.b), c ≤ |u r|) :
    False := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    change IsFiniteMeasure (volume.restrict (Ioo D.a D.b))
    infer_instance
  have hq := zeroMode_memLp_div_endpointDistance hD hγ hu
  have hsub : Ioo l D.b ⊆ radialCore D :=
    fun _ hr => ⟨hla.trans hr.1, hr.2⟩
  have hqi : Integrable (fun r => u r / min (r - D.a) (D.b - r))
      (volume.restrict (Ioo l D.b)) :=
    (hq.integrable (by norm_num)).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hinv : IntegrableOn (fun r => (D.b - r)⁻¹) (Ioo l D.b) := by
    apply (hqi.norm.div_const c).mono'
      ((measurable_const.sub measurable_id).inv.aestronglyMeasurable)
    filter_upwards [hlow, ae_restrict_mem measurableSet_Ioo] with r hcr hr
    have har : D.a < r := hla.trans hr.1
    have hbpos : 0 < D.b - r := sub_pos.mpr hr.2
    have hdpos : 0 < min (r - D.a) (D.b - r) :=
      lt_min (sub_pos.mpr har) hbpos
    have hdinv : (D.b - r)⁻¹ ≤ (min (r - D.a) (D.b - r))⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le hdpos (min_le_right (r - D.a) (D.b - r))
    have huc : 1 ≤ |u r| / c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hcr)
    calc
      ‖(D.b - r)⁻¹‖ = (D.b - r)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
      _ ≤ (min (r - D.a) (D.b - r))⁻¹ := hdinv
      _ ≤ (min (r - D.a) (D.b - r))⁻¹ * (|u r| / c) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left huc (inv_nonneg.mpr hdpos.le)
      _ = ‖u r / min (r - D.a) (D.b - r)‖ / c := by
        rw [norm_div]
        simp only [Real.norm_eq_abs, abs_of_pos hdpos, div_eq_mul_inv]
        ring
  have hi : IntervalIntegrable (fun r => (D.b - r)⁻¹) volume l D.b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlb.le).mpr hinv
  have hbad : IntervalIntegrable (fun r => (r - D.b)⁻¹) volume l D.b := by
    simpa only [Pi.neg_apply, ← inv_neg, neg_sub] using hi.neg
  rcases intervalIntegrable_sub_inv_iff.mp hbad with heq | hnot
  · exact hlb.ne heq
  · exact hnot right_mem_uIcc

end ContinuousFlexibility.Radial
