import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerAlgebra
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Normalize the complete weighted jet once

The radial endpoint factor is a fixed scalar at each evaluation point.
It therefore scales the genuine parameter multilinear map. Unit-ball
normalization applies to that complete map, and the actual first-jet
segment theorem supplies the zeroth reference difference.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
  {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
  {f : I → X → PolarPoint → ℝ}

theorem EndpointMixedPowerBounds.positive_oneHigh
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    (K s : ℕ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m k, k ≤ K → 0 < k → ∀ a b, a + b ≤ s → ∀ q ∈ Ω m,
      ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f m x) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ v : Fin k → X,
        δ m q ^ a * ‖J.D k x v‖ ≤ C * H m q * E m q ^ A *
          oneHighVariationWeight p base (s + loss) (x - center) v := by
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, fun m k hk hkpos a b hab q hq J x hx hlow => ?_⟩
  have hδa : 0 ≤ δ m q ^ a := pow_nonneg (hδ m q hq) a
  have hM : 0 ≤ C * H m q * E m q ^ A :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC) (hH m q hq))
      (Real.rpow_nonneg (zero_le_one.trans (hE m q hq)) _)
  let Jscaled : X [×k]→L[ℝ] ℝ := (δ m q ^ a) • J.D k x
  have hnorm (v : Fin k → X) : ‖Jscaled v‖ = δ m q ^ a * ‖J.D k x v‖ := by
    simp only [Jscaled, smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hδa]
  have hn := multilinear_bound_of_unitBall Jscaled (normSeminorm ℝ ℝ)
    (p base) (p (s + loss)) hM (a := 1 + p (s + loss) (x - center)) (fun v hv => by
      let R : ℝ := (1 + p (s + loss) (x - center)) + ∑ i, p (s + loss) (v i)
      have hsum : 0 ≤ ∑ i, p (s + loss) (v i) :=
        Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p (s + loss)) (x - center)]
      have hxR : p (s + loss) (x - center) ≤ R := by dsimp only [R]; linarith
      have hvR (i : Fin k) : p (s + loss) (v i) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left (by positivity))
      have hh := hb m k hk a b hab q hq J x hx hlow v (fun i => (hv i).le)
        R hR hxR hvR
      have hpow := Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one hab)
      have hraw : δ m q ^ a * ‖J.D k x v‖ ≤
          C * H m q * E m q ^ A * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
        simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos),
          mul_assoc, mul_left_comm, mul_comm] using hh
      have hh' := hraw.trans (mul_le_mul_of_nonneg_left hpow hM)
      simpa only [coe_normSeminorm, hnorm, R] using hh')
  simpa only [coe_normSeminorm, hnorm, multilinearTameSize, oneHighVariationWeight] using hn

/-- The complete weighted reference-subtracted family has one-high
bounds at every parameter order, including zero. -/
theorem EndpointMixedPowerBounds.difference_oneHigh
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m))
    (hΩ : ∀ m, IsOpen (Ω m))
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    (hcenter : center ∈ U)
    (hunit : ∀ x ∈ U, p base (x - center) ≤ 1)
    (hseg : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (k s : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ m a b, a + b ≤ s → ∀ q ∈ Ω m,
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun t => f m x t - f m center t) q),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m q ^ a * ‖J.D k x v‖ ≤ C * H m q * E m q ^ A *
          oneHighVariationWeight p base (s + loss) (x - center) v := by
  obtain ⟨C, A, hC, hA, hb⟩ := hf.positive_oneHigh hδ hH hE (max 1 k) s
  refine ⟨2 * C, A, mul_pos (by norm_num) (zero_lt_one.trans_le hC), hA, ?_⟩
  intro m a b hab q hq J x hx v
  let f0 : X → ℝ := fun y => mixedDerivative a b (f m y) q
  let J0 := (F m).parameter a b q hq
  let JD : SmoothDirections U (fun y => f0 y - f0 center) :=
    J.congr (fun y hy => mixedDerivative_sub_of_contDiffOn (hΩ m)
      ((F m).spatial y hy) ((F m).spatial center hcenter) a b hq)
  let L : ℝ →L[ℝ] ℝ := (δ m q ^ a) • ContinuousLinearMap.id ℝ ℝ
  let JS := smoothDirections_postcompCLM J0 L
  let KS : SmoothDirections U (fun y => L (f0 y) - L (f0 center)) :=
    (smoothDirections_postcompCLM JD L).congr
      (fun y _ => L.map_sub (f0 y) (f0 center))
  have hδa : 0 ≤ δ m q ^ a := pow_nonneg (hδ m q hq) a
  have hM : 0 ≤ C * H m q * E m q ^ A :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC) (hH m q hq))
      (Real.rpow_nonneg (zero_le_one.trans (hE m q hq)) _)
  have hh := smoothDirections_difference_allOrders_bound JS p base (s + loss)
    center x hx (hseg x hx) (hunit x hx) hM
    (fun j hj hjpos y hy w => by
      have h := hb m j hj hjpos a b hab q hq J0 y hy (hunit y hy) w
      simpa only [JS, smoothDirections_postcompCLM_D_apply, L, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hδa] using h)
    KS v
  simpa only [KS, JD, SmoothDirections.congr, smoothDirections_postcompCLM_D_apply, L, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hδa,
    mul_assoc] using hh

end ContinuousFlexibility.Analysis
