import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.N01cReferenceDifferenceBounds

/-! The full actual multilinear jet is normalized once, after every
distributed spatial product has been estimated. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem MixedPowerBounds.positive_oneHigh
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
    {f : X → PolarPoint → ℝ}
    (hf : MixedPowerBounds p center base loss U Ω H E f)
    (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    (K s : ℕ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ω, ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f x) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ C * H q * E q ^ A *
          oneHighVariationWeight p base (s + loss) (x - center) v := by
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, fun k hk hkpos a b hab q hq J x hx hlow => ?_⟩
  have hW : 0 ≤ C * H q * E q ^ A :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC) (hH q hq))
      (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _)
  have hn := multilinear_bound_of_unitBall (J.D k x) (normSeminorm ℝ ℝ)
    (p base) (p (s + loss)) hW (a := 1 + p (s + loss) (x - center)) (fun v hv => by
      let R : ℝ := (1 + p (s + loss) (x - center)) + ∑ i, p (s + loss) (v i)
      have hsum : 0 ≤ ∑ i, p (s + loss) (v i) :=
        Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p (s + loss)) (x - center)]
      have hxR : p (s + loss) (x - center) ≤ R := by dsimp only [R]; linarith
      have hvR (i : Fin k) : p (s + loss) (v i) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left (by positivity))
      have hh := hb k hk a b hab q hq J x hx hlow v (fun i => (hv i).le)
        R hR hxR hvR
      have hpow := Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one hab)
      have hh' : ‖J.D k x v‖ ≤ C * H q * E q ^ A * R := by
        have hraw : ‖J.D k x v‖ ≤ C * H q * E q ^ A *
            R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
          simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos),
            mul_assoc, mul_left_comm, mul_comm] using hh
        exact hraw.trans (mul_le_mul_of_nonneg_left hpow hW)
      simpa only [coe_normSeminorm, R] using hh')
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight] using hn

theorem smoothDirections_D_sub_constant
    {U : Set X} {f : X → ℝ} {c : ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U (fun x => f x - c))
    {k : ℕ} (hk : 0 < k) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    K.D k x v = J.D k x v := by
  let JC := smoothDirections_constant J.open_domain (-c)
  let JS := (smoothDirectionsAdd J JC).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  have heq := HasProjectiveJetsOn.unique J.open_domain
    K.hasProjectiveJetsOn JS.hasProjectiveJetsOn k x hx
  have h := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
  simpa only [JS, SmoothDirections.congr, smoothDirectionsAdd, add_apply,
    smoothDirections_D_constant JC hk hx v, add_zero] using h

/-- The zeroth difference uses the genuine first derivative along the
reference segment; positive jets are unchanged by the fixed reference. -/
theorem smoothDirections_difference_allOrders_bound
    {U : Set X} {f : X → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (center x : X)
    (hx : x ∈ U) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (hlow : p base (x - center) ≤ 1) {k : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j : ℕ, j ≤ max 1 k → 0 < j → ∀ y ∈ U, ∀ v : Fin j → X,
      ‖J.D j y v‖ ≤ M * oneHighVariationWeight p base high (y - center) v)
    (K : SmoothDirections U (fun y => f y - f center)) (v : Fin k → X) :
    ‖K.D k x v‖ ≤ (2 * M) * oneHighVariationWeight p base high (x - center) v := by
  by_cases hk : k = 0
  · subst k
    rw [smoothDirections_D_zero_apply K hx v]
    have hh := smoothDirections_difference_oneHigh_bound J p base high center (x - center)
      hseg hlow hM (fun y hy w => by
        simpa only [Real.norm_eq_abs] using hb 1 (le_max_left _ _) zero_lt_one y hy w)
    have hcenter : center + (x - center) = x := by abel
    simpa only [hcenter, Real.norm_eq_abs, oneHighVariationWeight,
      Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, mul_one, add_zero] using hh
  · rw [smoothDirections_D_sub_constant J K (Nat.pos_of_ne_zero hk) hx v]
    exact (hb k (le_max_right _ _) (Nat.pos_of_ne_zero hk) x hx v).trans
      (mul_le_mul_of_nonneg_right (by linarith : M ≤ 2 * M)
        (oneHighVariationWeight_nonneg p base high (x - center) v))

end ContinuousFlexibility.Analysis
