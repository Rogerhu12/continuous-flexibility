import ContinuousFlexibility.Analysis.N01aReferenceMeasure
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Recovering the physical square integral from the reference partition

The revised local L² contract includes measurability of each signed
localized field. The quantitative square estimate below uses their
integrable squares and the actual bounded-overlap partition identity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ENNReal

/-- The bounded overlap and partition identity control the actual pointwise
square, independently of the sign or regularity of its value. -/
theorem radialPartition_square_bound {D : ReferenceData} (hD : RadialPartition D) :
    ∃ B : ℕ, ∀ r ∈ radialCore D, ∀ a : ℝ,
      a ^ 2 ≤ (B : ℝ) * ∑' m, (D.localizer m r * a) ^ 2 := by
  classical
  obtain ⟨B, hB⟩ := hD.2.2.2.2.2
  refine ⟨B, fun r hr a => ?_⟩
  let s : Finset ℕ := (hB r).1.toFinset
  have hout (m : ℕ) (hm : m ∉ s) : D.localizer m r = 0 := by
    by_contra hne
    exact hm ((hB r).1.mem_toFinset.mpr hne)
  have hsum : (∑ m ∈ s, D.localizer m r) = 1 := by
    have heq : (∑' m : ℕ, D.localizer m r) = ∑ m ∈ s, D.localizer m r :=
      tsum_eq_sum hout
    rw [← heq]
    exact (hD.2.2.2.2.1 r hr).2
  have hsquare : (∑' m, (D.localizer m r * a) ^ 2) =
      ∑ m ∈ s, (D.localizer m r * a) ^ 2 := by
    apply tsum_eq_sum
    intro m hm
    rw [hout m hm, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hcard : s.card ≤ B := by
    simpa only [s, ← Set.ncard_eq_toFinset_card] using (hB r).2
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun m => D.localizer m r * a)
  rw [← Finset.sum_mul, hsum, one_mul] at hcs
  rw [hsquare]
  exact hcs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem radialPartition_localized_squares_summable {D : ReferenceData}
    (hD : RadialPartition D) (r a : ℝ) :
    Summable (fun m => (D.localizer m r * a) ^ 2) := by
  obtain ⟨B, hB⟩ := hD.2.2.2.2.2
  apply summable_of_hasFiniteSupport
  apply (hB r).1.subset
  intro m hm
  intro hz
  exact hm (by simp only [show D.localizer m r = 0 from hz, zero_mul,
    zero_pow (by decide : (2 : ℕ) ≠ 0)])

theorem RadialCellIntegrable.aemeasurable_sq {D : ReferenceData}
    (hD : RadialPartition D) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    AEMeasurable (fun p => f p ^ 2) (radialPhysicalMeasure D) := by
  have hnum : AEMeasurable
      (fun p : PolarPoint => ∑' m, (D.localizer m p.1 * f p) ^ 2)
      (radialPhysicalMeasure D) :=
    AEMeasurable.tsum fun m => (hf.integrable_square m).aestronglyMeasurable.aemeasurable
  have hden : Measurable (fun p : PolarPoint => ∑' m, D.localizer m p.1 ^ 2) :=
    Measurable.tsum fun m =>
      (((hD.1 m).continuous.comp continuous_fst).pow 2).measurable
  obtain ⟨B, hbound⟩ := radialPartition_square_bound hD
  have he : (fun p : PolarPoint => f p ^ 2) =ᵐ[radialPhysicalMeasure D]
      (fun p => (∑' m, (D.localizer m p.1 * f p) ^ 2) /
        (∑' m, D.localizer m p.1 ^ 2)) := by
    filter_upwards [radialPhysicalMeasure_ae_radialCore D] with p hp
    have hpos := hbound p.1 hp 1
    simp only [one_pow, mul_one] at hpos
    have hne : (∑' m, D.localizer m p.1 ^ 2) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hpos
      norm_num at hpos
    simp_rw [mul_pow, tsum_mul_right]
    exact (eq_div_iff hne).mpr (by ring)
  exact (hnum.div hden.aemeasurable).congr he.symm

/-- A summable family of actual nonnegative localized square integrals has
an integrable pointwise sum. -/
private theorem n01a_integrable_sum_of_localized_squares {D : ReferenceData}
    (hD : RadialPartition D) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (hs : Summable (fun m =>
      ∫ p, (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D)) :
    Integrable (fun p => ∑' m, (D.localizer m p.1 * f p) ^ 2)
      (radialPhysicalMeasure D) := by
  have hm : AEMeasurable (fun p : PolarPoint => ∑' m, (D.localizer m p.1 * f p) ^ 2)
      (radialPhysicalMeasure D) :=
    AEMeasurable.tsum fun m => (hf.integrable_square m).aestronglyMeasurable.aemeasurable
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [Real.enorm_eq_ofReal (tsum_nonneg fun m => sq_nonneg _),
    ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _)
      (radialPartition_localized_squares_summable hD _ _)]
  rw [lintegral_tsum (fun m =>
    (hf.integrable_square m).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  have hi (m : ℕ) :
      (∫⁻ p, ENNReal.ofReal ((D.localizer m p.1 * f p) ^ 2) ∂radialPhysicalMeasure D) =
        ENNReal.ofReal (∫ p, (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) :=
    (ofReal_integral_eq_lintegral_ofReal (hf.integrable_square m)
      (Eventually.of_forall fun _ => sq_nonneg _)).symm
  simp_rw [hi]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => integral_nonneg fun _ => sq_nonneg _) hs]
  exact ENNReal.ofReal_lt_top

/-- Unweighted reference squares control the physical square integral. -/
theorem exists_radialPartition_integral_square_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ,
      RadialCellIntegrable D f → Summable (fun m => referenceCellSquare D m f) →
      Integrable (fun p => f p ^ 2) (radialPhysicalMeasure D) ∧
        (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) ≤ C * ∑' m, referenceCellSquare D m f := by
  obtain ⟨B, hbound⟩ := radialPartition_square_bound hD
  refine ⟨((B : ℝ) + 1) * (2 * Real.pi), by positivity, fun f hf hs => ?_⟩
  have hsum : Summable (fun m =>
      ∫ p, (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) := by
    simpa only [integral_reference_cell_square hab hf] using hs.mul_left (2 * Real.pi)
  have hq := n01a_integrable_sum_of_localized_squares hD hf hsum
  have hmajor : ∀ᵐ p ∂radialPhysicalMeasure D,
      f p ^ 2 ≤ (B : ℝ) * ∑' m, (D.localizer m p.1 * f p) ^ 2 :=
    (radialPhysicalMeasure_ae_radialCore D).mono fun p hp => hbound p.1 hp (f p)
  have hfi : Integrable (fun p => f p ^ 2) (radialPhysicalMeasure D) :=
    (hq.const_mul (B : ℝ)).mono' (hf.aemeasurable_sq hD).aestronglyMeasurable
      (hmajor.mono fun p hp => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f p))] using hp)
  refine ⟨hfi, ?_⟩
  have hlim := integral_mono_ae hfi (hq.const_mul (B : ℝ)) hmajor
  rw [integral_const_mul] at hlim
  have hnormsum : Summable (fun m =>
      ∫ p, ‖(D.localizer m p.1 * f p) ^ 2‖ ∂radialPhysicalMeasure D) := by
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hsum
  rw [← integral_tsum_of_summable_integral_norm (fun m => hf.integrable_square m) hnormsum]
    at hlim
  simp_rw [integral_reference_cell_square hab hf] at hlim
  rw [tsum_mul_left] at hlim
  have hnonneg : 0 ≤ ∑' m, referenceCellSquare D m f :=
    tsum_nonneg fun m => n01a_referenceCellSquare_nonneg hab m f
  calc
    _ ≤ (B : ℝ) * ((2 * Real.pi) * ∑' m, referenceCellSquare D m f) := hlim
    _ ≤ ((B : ℝ) + 1) * (2 * Real.pi) * ∑' m, referenceCellSquare D m f := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hnonneg]

end ContinuousFlexibility.Statements
