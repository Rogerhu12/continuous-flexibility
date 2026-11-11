import ContinuousFlexibility.Radial.TailMassResistanceData
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Interval.Set.Union

/-!
# Weighted square integrability of an actual tail interpolant

The upper interpolation estimate suffices for the parameter argument:
square-summable node data produce a square-integrable solution.  No lower
interpolation estimate or converse limit-point assertion is used here.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

/-- The square integral of an edge interpolant is controlled by the two
Poisson square integrals, without any cancellation assumption. -/
theorem tailEdge_interpolant_square_bound {a b : ℝ} (hab : a ≤ b)
    {p v₀ v₁ : ℝ → ℝ} (hp : ContinuousOn p (Icc a b))
    (hv₀ : ContinuousOn v₀ (Icc a b)) (hv₁ : ContinuousOn v₁ (Icc a b))
    (hp₀ : ∀ x ∈ Icc a b, 0 ≤ p x) {M₀ M₁ : ℝ}
    (h₀ : (∫ x in a..b, p x * v₀ x ^ 2) ≤ M₀)
    (h₁ : (∫ x in a..b, p x * v₁ x ^ 2) ≤ M₁) (c₀ c₁ : ℝ) :
    (∫ x in a..b, p x * (c₀ * v₀ x + c₁ * v₁ x) ^ 2) ≤
      2 * (M₀ * c₀ ^ 2 + M₁ * c₁ ^ 2) := by
  have hi₀ := (hp.mul (hv₀.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₁ := (hp.mul (hv₁.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi : IntervalIntegrable (fun x => p x * (c₀ * v₀ x + c₁ * v₁ x) ^ 2)
      volume a b :=
    (hp.mul (((hv₀.const_mul c₀).add (hv₁.const_mul c₁)).pow 2)).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ x in a..b, (2 * c₀ ^ 2) * (p x * v₀ x ^ 2) +
        (2 * c₁ ^ 2) * (p x * v₁ x ^ 2) := by
      apply intervalIntegral.integral_mono_on hab hi
        ((hi₀.const_mul _).add (hi₁.const_mul _))
      intro x hx
      have hs : (c₀ * v₀ x + c₁ * v₁ x) ^ 2 ≤
          2 * (c₀ * v₀ x) ^ 2 + 2 * (c₁ * v₁ x) ^ 2 := by
        nlinarith only [sq_nonneg (c₀ * v₀ x - c₁ * v₁ x)]
      have hh := mul_le_mul_of_nonneg_left hs (hp₀ x hx)
      convert hh using 1 <;> ring
    _ = (2 * c₀ ^ 2) * (∫ x in a..b, p x * v₀ x ^ 2) +
        (2 * c₁ ^ 2) * (∫ x in a..b, p x * v₁ x ^ 2) := by
      rw [intervalIntegral.integral_add (hi₀.const_mul _) (hi₁.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (2 * c₀ ^ 2) * M₀ + (2 * c₁ ^ 2) * M₁ :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity))
        (mul_le_mul_of_nonneg_left h₁ (by positivity))
    _ = _ := by ring

/-- Consecutive closed edges cover the open tail when its entrance is
the first node.  Overlap at nodes is harmless for the integrability argument. -/
theorem deepTail_open_subset_iUnion_edges {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hstart : T.node 0 = T.entrance) :
    Ioo T.entrance T.endpoint ⊆ ⋃ n : ℕ, Icc (T.node n) (T.node (n + 1)) := by
  intro x hx
  have ht := hT.2.2.2.2.2.2.2.2.2.1
  obtain ⟨N, hN⟩ := (ht.eventually (lt_mem_nhds hx.2)).exists
  have hxN : x ∈ Ico (T.node 0) (T.node N) := by
    rw [hstart]
    exact ⟨hx.1.le, hN⟩
  have hcover := Ico_subset_biUnion_Ico N T.node hxN
  obtain ⟨n, hn⟩ := mem_iUnion.mp hcover
  obtain ⟨_, hn⟩ := mem_iUnion.mp hn
  exact mem_iUnion.mpr ⟨n, hn.1, hn.2.le⟩

/-- Square-summable node data and one uniform upper interpolation bound
give membership in the original weighted `L²` space. -/
theorem deepTail_memLp_of_edge_square_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hstart : T.node 0 = T.entrance)
    {u : ℝ → ℝ} (hu : ContinuousOn u (Ioo T.entrance T.endpoint))
    (huEdge : ∀ n, ContinuousOn u (Icc (T.node n) (T.node (n + 1))))
    {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, (∫ x in T.node n..T.node (n + 1), T.p x * u x ^ 2) ≤
      C * (tailMass T n * a n ^ 2 + tailMass T (n + 1) * a (n + 1) ^ 2))
    (hsum : Summable (fun n => tailMass T n * a n ^ 2)) :
    MemLp u 2 (deepTailMeasure T) := by
  let I (n : ℕ) := Icc (T.node n) (T.node (n + 1))
  have hsub (n : ℕ) : I n ⊆ Ico T.entrance T.endpoint :=
    deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
      (deepTail_node_lt_endpoint hT (n + 1))
  have hint (n : ℕ) : IntegrableOn (fun x => T.p x * u x ^ 2) (I n) :=
    (((deepTail_contDiffOn hT).continuousOn.mono (hsub n)).mul
      ((huEdge n).pow 2)).integrableOn_Icc
  have hnorm (n : ℕ) : (∫ x in I n, ‖T.p x * u x ^ 2‖) =
      ∫ x in T.node n..T.node (n + 1), T.p x * u x ^ 2 := by
    rw [intervalIntegral.integral_of_le
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)).le,
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change ‖T.p x * u x ^ 2‖ = T.p x * u x ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (deepTail_pos hT x (hsub n hx)).le (sq_nonneg _))]
  have hshift : Summable (fun n => tailMass T (n + 1) * a (n + 1) ^ 2) :=
    (summable_nat_add_iff 1).mpr hsum
  have hs : Summable (fun n => ∫ x in I n, ‖T.p x * u x ^ 2‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => (hnorm n).trans_le (hbound n))
    exact (hsum.add hshift).mul_left C
  have hwhole : IntegrableOn (fun x => T.p x * u x ^ 2)
      (Ioo T.entrance T.endpoint) :=
    (integrableOn_iUnion_of_summable_integral_norm hint hs).mono_set
      (deepTail_open_subset_iUnion_edges hT hstart)
  have huAE : AEStronglyMeasurable u (deepTailMeasure T) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
      (hu.aestronglyMeasurable measurableSet_Ioo)
  apply (memLp_two_iff_integrable_sq huAE).mpr
  have hpAE : AEMeasurable (fun x => ENNReal.ofReal (T.p x))
      (volume.restrict (Ioo T.entrance T.endpoint)) :=
    (((deepTail_contDiffOn hT).continuousOn.mono Ioo_subset_Ico_self).aemeasurable
      measurableSet_Ioo).ennreal_ofReal
  rw [deepTailMeasure, integrable_withDensity_iff_integrable_smul₀' hpAE (by simp)]
  apply (integrable_congr ?_).mpr hwhole
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [ENNReal.toReal_ofReal (deepTail_pos hT x (Ioo_subset_Ico_self hx)).le,
    smul_eq_mul]

end ContinuousFlexibility.Radial
