import ContinuousFlexibility.Radial.TailNaturalInterpolation
import ContinuousFlexibility.Radial.TailTestPairing
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Global integrability of the actual tail interpolation

The closed physical edges cover the outward interval. Summable node masses
therefore control the weighted absolute and square integrals of the same
Poisson interpolant. A continuous initial extension can then be attached
without imposing an artificial entrance boundary condition.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem deepTail_iUnion_closed_edges {T : DeepTailData} (hT : DeepTailHypotheses T) :
    (⋃ n : ℕ, Icc (T.node n) (T.node (n + 1))) = Ico (T.node 0) T.endpoint := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨((deepTail_node_strictMono hT).monotone (Nat.zero_le n)).trans hn.1,
      hn.2.trans_lt (deepTail_node_lt_endpoint hT (n + 1))⟩
  · intro hx
    obtain ⟨n, hn⟩ := morse_outward_block_exists hT.2.2.2.2.2.2.2.2.2.1 hx.1 hx.2
    exact mem_iUnion.mpr ⟨n, ⟨hn.1, hn.2.le⟩⟩

theorem tailPoissonInterpolation_continuousOn_edge {T : DeepTailData}
    (hT : DeepTailHypotheses T) (a : ℕ → ℝ) (n : ℕ) :
    ContinuousOn (tailPoissonInterpolation T hT a) (Icc (T.node n) (T.node (n + 1))) :=
  (tailActualEdgeInterpolation_differentiable hT n (a n) (a (n + 1))).continuous.continuousOn.congr
    (fun _ hx => tailPoissonInterpolation_apply_closed hT a hx)

theorem tailPoissonInterpolation_aestronglyMeasurable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (a : ℕ → ℝ) :
    AEStronglyMeasurable (tailPoissonInterpolation T hT a)
      (volume.restrict (Ico (T.node 0) T.endpoint)) := by
  rw [← deepTail_iUnion_closed_edges hT]
  exact AEStronglyMeasurable.iUnion fun n =>
    (tailPoissonInterpolation_continuousOn_edge hT a n).aestronglyMeasurable measurableSet_Icc

/-- A common summation argument for any nonnegative continuous function of the interpolant. -/
theorem tailPoissonInterpolation_weighted_integrableOn_of_summable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (a : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : Continuous F) (hF₀ : ∀ x, 0 ≤ F x) {B : ℕ → ℝ} (hB : Summable B)
    (hbound : ∀ n,
      (∫ x in T.node n..T.node (n + 1),
        T.p x * F (tailActualEdgeInterpolation T hT n (a n) (a (n + 1)) x)) ≤ B n) :
    IntegrableOn (fun x => T.p x * F (tailPoissonInterpolation T hT a x))
      (Ico (T.node 0) T.endpoint) := by
  let f : ℝ → ℝ := fun x => T.p x * F (tailPoissonInterpolation T hT a x)
  have hlocal (n : ℕ) : IntegrableOn f (Icc (T.node n) (T.node (n + 1))) := by
    have hc := (tailActualEdge_continuousOn hT n).mul
      (hF.comp (tailActualEdgeInterpolation_differentiable hT n (a n) (a (n + 1))).continuous).continuousOn
    exact hc.integrableOn_Icc.congr_fun (fun x hx => by
      dsimp only [f]
      rw [tailPoissonInterpolation_apply_closed hT a hx]) measurableSet_Icc
  have heq (n : ℕ) :
      (∫ x in Icc (T.node n) (T.node (n + 1)), ‖f x‖) =
        ∫ x in T.node n..T.node (n + 1),
          T.p x * F (tailActualEdgeInterpolation T hT n (a n) (a (n + 1)) x) := by
    rw [intervalIntegral.integral_of_le (tailActualEdge_order hT n).le,
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only [f]
    rw [Real.norm_eq_abs, tailPoissonInterpolation_apply_closed hT a hx,
      abs_of_nonneg (mul_nonneg (tailActualEdge_pos hT n x hx).le (hF₀ _))]
  have hs : Summable (fun n => ∫ x in Icc (T.node n) (T.node (n + 1)), ‖f x‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ hB
    intro n
    rw [heq n]
    exact hbound n
  rw [← deepTail_iUnion_closed_edges hT]
  exact integrableOn_iUnion_of_summable_integral_norm hlocal hs

theorem tailPoissonInterpolation_weighted_sq_integrableOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {a : ℕ → ℝ} (ha : Summable (fun n => tailMass T n * a n ^ 2)) :
    IntegrableOn (fun x => T.p x * tailPoissonInterpolation T hT a x ^ 2)
      (Ico (T.node 0) T.endpoint) := by
  have hshift : Summable (fun n => tailMass T (n + 1) * a (n + 1) ^ 2) :=
    (summable_nat_add_iff 1).mpr ha
  exact tailPoissonInterpolation_weighted_integrableOn_of_summable hT a
    (continuous_id.pow 2) (fun x => sq_nonneg x) ((ha.add hshift).mul_left 8)
    (fun n => tailActualEdgeInterpolation_sq_integral_le hT hη hK n (a n) (a (n + 1)))

theorem tailPoissonInterpolation_weighted_abs_integrableOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16)
    {a : ℕ → ℝ} (ha : Summable (fun n => tailMass T n * |a n|)) :
    IntegrableOn (fun x => T.p x * |tailPoissonInterpolation T hT a x|)
      (Ico (T.node 0) T.endpoint) := by
  have hshift : Summable (fun n => tailMass T (n + 1) * |a (n + 1)|) :=
    (summable_nat_add_iff 1).mpr ha
  exact tailPoissonInterpolation_weighted_integrableOn_of_summable hT a
    continuous_abs (fun x => abs_nonneg x) ((ha.add hshift).mul_left 4)
    (fun n => tailActualEdgeInterpolation_abs_integral_le hT hη n (a n) (a (n + 1)))

private theorem tail_initial_outward_cover (T : DeepTailData) :
    Ioo T.entrance T.endpoint ⊆
      Icc T.entrance (T.node 0) ∪ Ico (T.node 0) T.endpoint := by
  intro x hx
  by_cases h : x ≤ T.node 0
  · exact Or.inl ⟨hx.1.le, h⟩
  · exact Or.inr ⟨(lt_of_not_ge h).le, hx.2⟩

/-- Initial compact regularity and outward interpolation suffice for weighted measurability. -/
theorem tailActualExtension_aestronglyMeasurable {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ} {u : ℝ → ℝ}
    (hinit : ContinuousOn u (Icc T.entrance (T.node 0)))
    (hout : EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint)) :
    AEStronglyMeasurable u (deepTailMeasure T) := by
  have hmout : AEStronglyMeasurable u (volume.restrict (Ico (T.node 0) T.endpoint)) := by
    apply (tailPoissonInterpolation_aestronglyMeasurable hT a).congr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact (hout hx).symm
  have hmi : AEStronglyMeasurable u (volume.restrict (Icc T.entrance (T.node 0))) :=
    hinit.aestronglyMeasurable measurableSet_Icc
  have hmu : AEStronglyMeasurable u
      (volume.restrict (Icc T.entrance (T.node 0) ∪ Ico (T.node 0) T.endpoint)) :=
    aestronglyMeasurable_union_iff.mpr ⟨hmi, hmout⟩
  have hm : AEStronglyMeasurable u (volume.restrict (Ioo T.entrance T.endpoint)) :=
    hmu.mono_measure (Measure.restrict_mono (tail_initial_outward_cover T) le_rfl)
  exact AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) hm

/-- A compact initial extension adds a finite weighted integral to the outward tail. -/
theorem tailActualExtension_weighted_integrableOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ} {u : ℝ → ℝ} {F : ℝ → ℝ}
    (hinit : ContinuousOn u (Icc T.entrance (T.node 0)))
    (hout : EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint))
    (hF : Continuous F)
    (hI : IntegrableOn (fun x => T.p x * F (tailPoissonInterpolation T hT a x))
      (Ico (T.node 0) T.endpoint)) :
    IntegrableOn (fun x => T.p x * F (u x)) (Ioo T.entrance T.endpoint) := by
  have hp : ContinuousOn T.p (Icc T.entrance (T.node 0)) :=
    (deepTail_contDiffOn hT).continuousOn.mono
      (deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0))
  have hi : IntegrableOn (fun x => T.p x * F (u x)) (Icc T.entrance (T.node 0)) :=
    (hp.mul (hF.comp_continuousOn hinit)).integrableOn_Icc
  have ho : IntegrableOn (fun x => T.p x * F (u x)) (Ico (T.node 0) T.endpoint) :=
    hI.congr_fun (fun x hx => by dsimp only; rw [hout hx]) measurableSet_Ico
  exact (hi.union ho).mono_set (tail_initial_outward_cover T)

/-- Summable weighted node values give the actual extended solution in weighted `L¹`. -/
theorem tailActualExtension_integrable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) {a : ℕ → ℝ} {u : ℝ → ℝ}
    (ha : Summable (fun n => tailMass T n * |a n|))
    (hinit : ContinuousOn u (Icc T.entrance (T.node 0)))
    (hout : EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint)) :
    Integrable u (deepTailMeasure T) := by
  have hi := tailActualExtension_weighted_integrableOn hT hinit hout continuous_abs
    (tailPoissonInterpolation_weighted_abs_integrableOn hT hη ha)
  have hnorm : Integrable (fun x => |u x|) (deepTailMeasure T) :=
    (tail_integrable_density_iff ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
      (fun x hx => deepTail_pos hT x ⟨hx.1.le, hx.2⟩) _).mpr hi
  apply (integrable_norm_iff (tailActualExtension_aestronglyMeasurable hT hinit hout)).mp
  simpa only [Real.norm_eq_abs] using hnorm

/-- Summable weighted node squares give the actual extended solution in weighted `L²`. -/
theorem tailActualExtension_memLp_two {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {a : ℕ → ℝ} {u : ℝ → ℝ} (ha : Summable (fun n => tailMass T n * a n ^ 2))
    (hinit : ContinuousOn u (Icc T.entrance (T.node 0)))
    (hout : EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint)) :
    MemLp u 2 (deepTailMeasure T) := by
  apply (memLp_two_iff_integrable_sq
    (tailActualExtension_aestronglyMeasurable hT hinit hout)).mpr
  apply (tail_integrable_density_iff ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
    (fun x hx => deepTail_pos hT x ⟨hx.1.le, hx.2⟩) _).mpr
  exact tailActualExtension_weighted_integrableOn hT hinit hout (continuous_id.pow 2)
    (tailPoissonInterpolation_weighted_sq_integrableOn hT hη hK ha)

end ContinuousFlexibility.Radial
