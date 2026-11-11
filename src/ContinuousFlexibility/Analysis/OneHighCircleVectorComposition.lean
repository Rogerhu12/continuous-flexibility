import ContinuousFlexibility.Analysis.OneHighCircleVectorProducts
import ContinuousFlexibility.Analysis.OneHighCircleScalarComposition

/-!
# Uniform multivariable smooth composition on the physical circle

The outer function may have any finite number of real inputs. Its actual
multilinear derivative norms are bounded on a convex region containing zero
and the joint input range. The explicit constant involves only these bounds,
the number of inputs, and their prescribed low Fourier bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Function Set
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)] {m : ℕ}

theorem circle_vector_composition_derivative_l2_le
    (v : ℝ → Fin m → ℝ) (Φ : (Fin m → ℝ) → ℝ)
    (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    (hΦ : ∀ x, ContDiffAt ℝ ∞ Φ (v x))
    {s : ℕ} (hs : 0 < s) {R : ℝ} (hR0 : 0 ≤ R) {B : ℕ → ℝ}
    (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ x k, 1 ≤ k → k ≤ s → ‖iteratedFDeriv ℝ k Φ (v x)‖ ≤ B k)
    (hR : ∀ i, circleRealFourierL1Norm
      (circleComponent (periodicCircleJet v hp hv 0) i) ≤ R) :
    (eLpNorm (periodicCircleJet (fun x => Φ (v x) - Φ 0)
      (periodic_sub_base_comp hp Φ) (contDiff_sub_base_comp hv hΦ) s)
        2 AddCircle.haarAddCircle).toReal ≤
      circleVectorCompositionCoefficient m s R B *
        ∑ i, circleRealSobolevNorm (s : ℝ)
          (circleComponent (periodicCircleJet v hp hv 0) i) := by
  classical
  let f := periodicCircleJet v hp hv
  let w := periodicCircleJet (fun x => Φ (v x) - Φ 0)
    (periodic_sub_base_comp hp Φ) (contDiff_sub_base_comp hv hΦ)
  let N (c : OrderedFinpartition s) : C(AddCircle P, ℝ) :=
    B c.length • ∏ j, circleNormMap (f (c.partSize j))
  have hN (c : OrderedFinpartition s) (θ : AddCircle P) : 0 ≤ N c θ := by
    simp only [N, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.prod_apply, circleNormMap_apply]
    exact mul_nonneg (hB0 c.length) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hpoint (θ : AddCircle P) : ‖w s θ‖ ≤ ‖(∑ c, N c) θ‖ := by
    have hn : 0 ≤ (∑ c, N c) θ := by
      simpa only [ContinuousMap.sum_apply] using Finset.sum_nonneg (fun c _ => hN c θ)
    rw [Real.norm_of_nonneg hn]
    refine QuotientAddGroup.induction_on θ ?_
    intro x
    have hsub : iteratedDeriv s (fun y => Φ (v y) - Φ 0) x =
        iteratedDeriv s (Φ ∘ v) x := by
      simpa only [sub_eq_add_neg, add_comm, Function.comp_apply] using
        (iteratedDeriv_const_add (f := Φ ∘ v) (x := x) hs (-Φ 0))
    have hc := norm_iteratedFDeriv_comp_le_bounded_partition_sum
      (hΦ x) hv.contDiffAt hs (hB x)
    simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hc
    simpa only [w, f, N, periodicCircleJet_coe_apply, hsub,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.prod_apply, circleNormMap_apply] using hc
  have hprod (c : OrderedFinpartition s) :
      (eLpNorm (∏ j, circleNormMap (f (c.partSize j))) 2 AddCircle.haarAddCircle).toReal ≤
        (m : ℝ) ^ c.length * (c.length : ℝ) * R ^ (c.length - 1) *
          ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) :=
    circle_vector_derivative_product_le f (periodicCircleJet_hasDerivAt v hp hv)
      (c.length_pos hs) c.partSize (oneHighPartition_sum_orders c).le hR0 hR
  calc
    _ ≤ (eLpNorm (∑ c, N c) 2 AddCircle.haarAddCircle).toReal :=
      circle_l2_le_of_norm_le (w s) (∑ c, N c) hpoint
    _ ≤ ∑ c, (eLpNorm (N c) 2 AddCircle.haarAddCircle).toReal := circle_l2_sum_le N
    _ = ∑ c : OrderedFinpartition s, B c.length *
        (eLpNorm (∏ j, circleNormMap (f (c.partSize j))) 2 AddCircle.haarAddCircle).toReal := by
      apply Finset.sum_congr rfl
      intro c _
      exact circle_l2_const_smul _ (hB0 c.length)
    _ ≤ ∑ c : OrderedFinpartition s, B c.length *
        ((m : ℝ) ^ c.length * (c.length : ℝ) * R ^ (c.length - 1) *
          ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i)) :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hprod c) (hB0 c.length)
    _ = _ := by
      simp only [circleVectorCompositionCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring

def circleVectorCompositionConstant (m s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  if s = 0 then B 1 else
    (2 : ℝ) ^ s * (B 1 + circleVectorCompositionCoefficient m s R B)

/-- The full multivariable estimate for every natural order, including zero.
All input norms are those of the actual component functions, and the outer
function need only be smooth near the specified convex region. -/
theorem circle_vector_composition_sobolev_le
    (s : ℕ) (v : ℝ → Fin m → ℝ) (Φ : (Fin m → ℝ) → ℝ)
    (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    {S : Set (Fin m → ℝ)} (hS : Convex ℝ S) (h0 : (0 : Fin m → ℝ) ∈ S)
    (hvin : ∀ x, v x ∈ S) (hΦ : ∀ z ∈ S, ContDiffAt ℝ ∞ Φ z)
    {R : ℝ} (hR0 : 0 ≤ R) {B : ℕ → ℝ} (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ z ∈ S, ∀ k, 1 ≤ k → k ≤ max 1 s → ‖iteratedFDeriv ℝ k Φ z‖ ≤ B k)
    (hR : ∀ i, circleRealFourierL1Norm
      (circleComponent (periodicCircleJet v hp hv 0) i) ≤ R) :
    circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (fun x => Φ (v x) - Φ 0)
        (periodic_sub_base_comp hp Φ)
        (contDiff_sub_base_comp hv (fun x => hΦ (v x) (hvin x))) 0) ≤
      circleVectorCompositionConstant m s R B *
        ∑ i, circleRealSobolevNorm (s : ℝ)
          (circleComponent (periodicCircleJet v hp hv 0) i) := by
  classical
  let hΦv := fun x => hΦ (v x) (hvin x)
  let f := periodicCircleJet v hp hv
  let w := periodicCircleJet (fun x => Φ (v x) - Φ 0)
    (periodic_sub_base_comp hp Φ) (contDiff_sub_base_comp hv hΦv)
  have hdiff (z : Fin m → ℝ) (hz : z ∈ S) : DifferentiableAt ℝ Φ z :=
    (hΦ z hz).differentiableAt (by simp)
  have hfirst (z : Fin m → ℝ) (hz : z ∈ S) : ‖fderiv ℝ Φ z‖ ≤ B 1 := by
    rw [← norm_iteratedFDeriv_one Φ]
    exact hB z hz 1 le_rfl (le_max_left _ _)
  have hrange (θ : AddCircle P) : f 0 θ ∈ S := by
    refine QuotientAddGroup.induction_on θ ?_
    intro x
    simpa only [f, periodicCircleJet_coe_apply, iteratedDeriv_zero] using hvin x
  have hw0 : ⇑(w 0) = fun θ => Φ (f 0 θ) - Φ 0 := by
    funext θ
    refine QuotientAddGroup.induction_on θ ?_
    intro x
    simp only [w, f, periodicCircleJet_coe_apply, iteratedDeriv_zero]
  have hbase : (eLpNorm (w 0) 2 AddCircle.haarAddCircle).toReal ≤
      B 1 * (eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal := by
    rw [hw0]
    exact composition_sub_base_LpNorm_le hS h0 (hB0 1) hdiff hfirst
      (f 0).continuous hrange
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ (f 0))
  have hinput : (eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal ≤
      ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i) := by
    apply (circle_l2_pi_le_sum (f 0)).trans
    apply Finset.sum_le_sum
    intro i _
    exact circle_real_derivative_l2_le_sobolev (fun k => circleComponent (f k) i)
      (circleComponent_hasDerivAt f (periodicCircleJet_hasDerivAt v hp hv) i)
      (Nat.zero_le s)
  have hbase' := hbase.trans (mul_le_mul_of_nonneg_left hinput (hB0 1))
  by_cases hs : s = 0
  · subst s
    simpa only [circleVectorCompositionConstant, if_pos rfl, Nat.cast_zero,
      circle_real_sobolevNorm_zero_eq_l2] using hbase'
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hhigh := circle_vector_composition_derivative_l2_le v Φ hp hv hΦv hspos hR0 hB0
      (fun x k hk hks => hB (v x) (hvin x) k hk (hks.trans (le_max_right _ _))) hR
    calc
      _ ≤ (2 : ℝ) ^ s *
          ((eLpNorm (w 0) 2 AddCircle.haarAddCircle).toReal +
            (eLpNorm (w s) 2 AddCircle.haarAddCircle).toReal) :=
        circle_real_sobolevNorm_le_derivative_endpoints w
          (periodicCircleJet_hasDerivAt _ _ _) s
      _ ≤ (2 : ℝ) ^ s *
          (B 1 * (∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i)) +
            circleVectorCompositionCoefficient m s R B *
              ∑ i, circleRealSobolevNorm (s : ℝ) (circleComponent (f 0) i)) :=
        mul_le_mul_of_nonneg_left (add_le_add hbase' hhigh) (by positivity)
      _ = _ := by rw [circleVectorCompositionConstant, if_neg hs]; ring

end ContinuousFlexibility.Analysis
