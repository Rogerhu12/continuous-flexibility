import ContinuousFlexibility.Analysis.SpacesPhysicalLocalization
import ContinuousFlexibility.Analysis.SpacesPhysicalSynthesisRows
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact reconstruction after localization and envelope gluing

The radial partition sums to one and each envelope equals one on its
partition function. Dominated convergence transfers that identity to the
actual cylinder inner product, proving the Hilbert-space reconstruction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ContDiff BigOperators RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem spacesRadialPartition_hasSum (x : ℝ) :
    HasSum (fun n : ℤ => spacesRadialPartition n x) 1 := by
  have hs : Summable (fun n : ℤ => spacesRadialPartition n x) := by
    apply summable_of_ne_finset_zero (s := {⌊x⌋, ⌊x⌋ + 1})
    intro n hn
    apply spacesRadialPartition_eq_zero_of_index x
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  simpa only [spacesRadialPartition_sum] using hs.hasSum

theorem spaces_integral_radial_partition_product (u v : CylinderL2) :
    HasSum (fun n : ℤ => ∫ p, spacesRadialPartition n p.1 * u p * v p ∂materialCylinderMeasure)
      (∫ p, u p * v p ∂materialCylinderMeasure) := by
  let bound : ℤ → PolarPoint → ℝ := fun n p => spacesRadialPartition n p.1 * |u p * v p|
  apply hasSum_integral_of_dominated_convergence bound
  · intro n
    exact (((spacesRadialPartition_contDiff n).continuous.comp continuous_fst).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u)).mul (Lp.aestronglyMeasurable v)
  · intro n
    exact Eventually.of_forall (fun p => by
      simp only [bound, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (spacesRadialPartition_nonneg n p.1), mul_assoc, le_refl])
  · exact Eventually.of_forall (fun p =>
      (spacesRadialPartition_hasSum p.1).summable.mul_right |u p * v p|)
  · have he : (fun p => ∑' n, bound n p) = fun p => |u p * v p| := by
      funext p
      rw [show (fun n => bound n p) = fun n => spacesRadialPartition n p.1 * |u p * v p| from rfl,
        tsum_mul_right, spacesRadialPartition_sum, one_mul]
    rw [he]
    simpa only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, mul_comm] using
      (L2.integrable_inner (𝕜 := ℝ) u v).norm
  · exact Eventually.of_forall (fun p => by
      simpa only [one_mul, mul_assoc] using (spacesRadialPartition_hasSum p.1).mul_right (u p * v p))

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

theorem spacesPhysicalEnvelopeSynthesis_localized_single_ae
    (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    (spacesPhysicalEnvelopeSynthesis hT 0 0
      (lp.single 2 n (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n)) : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] fun p =>
        spacesRadialPartition n p.1 * physicalJetProjectiveZero hT u p := by
  filter_upwards [spacesPhysicalEnvelopeSynthesis_single_ae hT 0 0 n
      (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n),
    spacesPhysicalLocalizedJetFamily_zero_ae hT u n,
    spacesPhysicalRepresentative_zero_ae hT u] with p hs hl hr
  rw [hs, hl]
  simp only [spacesPhysicalEnvelopeMultiplier, iteratedDeriv_zero, pow_zero, div_self (by norm_num : (1 : ℝ) ≠ 0),
    mul_one, spacesPhysicalLocalizedRepresentative]
  rw [← mul_assoc, spacesRadialEnvelope_mul_partition, hr]

/-- The actual envelope-gluing operator is a left inverse to localization. -/
theorem spacesPhysicalEnvelopeSynthesis_localization (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalEnvelopeSynthesis hT 0 0 (spacesPhysicalLocalizedJetFamily hT 0 0 0 u) =
      physicalJetProjectiveZero hT u := by
  apply ext_inner_left ℝ
  intro v
  have hs := (spacesPhysicalEnvelopeSynthesis hT 0 0).hasSum
    (lp.hasSum_single ENNReal.ofNat_ne_top (spacesPhysicalLocalizedJetFamily hT 0 0 0 u))
  have hi := (innerSL ℝ v).hasSum hs
  have he (n : ℤ) :
      inner ℝ v (spacesPhysicalEnvelopeSynthesis hT 0 0
        (lp.single 2 n (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n))) =
      ∫ p, spacesRadialPartition n p.1 * v p * physicalJetProjectiveZero hT u p
        ∂materialCylinderMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [spacesPhysicalEnvelopeSynthesis_localized_single_ae hT u n] with p hp
    rw [hp]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    ring
  simp only [innerSL_apply_apply, he] at hi
  have hsum := spaces_integral_radial_partition_product v (physicalJetProjectiveZero hT u)
  have hout : inner ℝ v (physicalJetProjectiveZero hT u) =
      ∫ p, v p * physicalJetProjectiveZero hT u p ∂materialCylinderMeasure := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hout]
  exact hi.unique hsum

end ContinuousFlexibility.Statements
