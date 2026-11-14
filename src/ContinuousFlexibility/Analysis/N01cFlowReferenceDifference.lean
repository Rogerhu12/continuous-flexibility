module

public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-! Transfer positive parameter jets to the actual reference difference.
The endpoint factor is fixed along the reference segment, so the zeroth
order is obtained from the first derivative with the same endpoint weight. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem smoothDirections_weighted_difference_allOrders_bound
    {U : Set X} {f : X → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (center x : X)
    (hx : x ∈ U)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (hlow : p base (x - center) ≤ 1) {k : ℕ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hb : ∀ j : ℕ, j ≤ max 1 k → 0 < j → ∀ y ∈ U, ∀ v : Fin j → X,
      δ * ‖J.D j y v‖ ≤ M * oneHighVariationWeight p base high (y - center) v)
    (K : SmoothDirections U (fun y => f y - f center)) (v : Fin k → X) :
    δ * ‖K.D k x v‖ ≤
      (2 * M) * oneHighVariationWeight p base high (x - center) v := by
  have hraw : ∀ j : ℕ, j ≤ max 1 k → 0 < j → ∀ y ∈ U, ∀ w : Fin j → X,
      ‖J.D j y w‖ ≤
        (M / δ) * oneHighVariationWeight p base high (y - center) w := by
    intro j hj hjpos y hy w
    have hmul : ‖J.D j y w‖ * δ ≤
        M * oneHighVariationWeight p base high (y - center) w := by
      simpa only [mul_comm] using hb j hj hjpos y hy w
    simpa only [div_mul_eq_mul_div] using (le_div_iff₀ hδ).2 hmul
  have hh := smoothDirections_difference_allOrders_bound
    J p base high center x hx hseg hlow (div_nonneg hM hδ.le) hraw K v
  calc
    δ * ‖K.D k x v‖ ≤
        δ * ((2 * (M / δ)) * oneHighVariationWeight p base high (x - center) v) :=
      mul_le_mul_of_nonneg_left hh hδ.le
    _ = (2 * M) * oneHighVariationWeight p base high (x - center) v := by
      field_simp [hδ.ne'] <;> ring

theorem smoothDirections_weighted_mixedDifference_allOrders_bound
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (center x : X)
    (hcenter : center ∈ U) (hx : x ∈ U)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (hlow : p base (x - center) ≤ 1) (a b : ℕ) (q : PolarPoint) (hq : q ∈ Ω)
    (J : SmoothDirections U (fun y => mixedDerivative a b (f y) q))
    {k : ℕ} {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hb : ∀ j : ℕ, j ≤ max 1 k → 0 < j → ∀ y ∈ U, ∀ v : Fin j → X,
      δ * ‖J.D j y v‖ ≤ M * oneHighVariationWeight p base high (y - center) v)
    (K : SmoothDirections U
      (fun y => mixedDerivative a b (fun q => f y q - f center q) q))
    (v : Fin k → X) :
    δ * ‖K.D k x v‖ ≤
      (2 * M) * oneHighVariationWeight p base high (x - center) v := by
  let L : SmoothDirections U
      (fun y => mixedDerivative a b (f y) q - mixedDerivative a b (f center) q) :=
    K.congr (fun y hy =>
      mixedDerivative_sub_of_contDiffOn hΩ (hf y hy) (hf center hcenter) a b hq)
  have hh := smoothDirections_weighted_difference_allOrders_bound
    J p base high center x hx hseg hlow hM hδ hb L v
  simpa only [L, SmoothDirections.congr] using hh

/-- A finite prefix of genuine positive jets suffices for every order of
the reference difference, including order zero. The common domain and base
are fixed before either the parameter order or the spatial order. -/
theorem mixedDifference_weighted_prefix_bounds
    {I : Type*} {U : Set X} (Ω : I → Set PolarPoint)
    (hΩ : ∀ i, IsOpen (Ω i)) (f : I → X → PolarPoint → ℝ)
    (hf : ∀ i x, x ∈ U → ContDiffOn ℝ ∞ (f i x) (Ω i))
    (P : I → PolarPoint → Prop) (hP : ∀ i q, P i q → q ∈ Ω i)
    (p : ℕ → Seminorm ℝ X) (base loss : ℕ) (center : X)
    (hcenter : center ∈ U)
    (hseg : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (δ : I → ℕ → PolarPoint → ℝ)
    (hδ : ∀ i a q, P i q → 0 < δ i a q)
    (H E : I → ℝ) (hH : ∀ i, 0 ≤ H i) (hE : ∀ i, 1 ≤ E i)
    (hpos : ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i a b q, a + b ≤ s → P i q →
      ∃ J : SmoothDirections U (fun x => mixedDerivative a b (f i x) q),
        ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
          δ i a q * |J.D j x v| ≤
            B * H i ^ (3 / 4 : ℝ) * E i ^ B *
              oneHighVariationWeight p base (s + loss + d) (x - center) v) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i a b q, a + b ≤ s → P i q →
      ∃ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun q => f i x q - f i center q) q),
        ∀ x ∈ U, ∀ v : Fin k → X,
          δ i a q * |J.D k x v| ≤
            B * H i ^ (3 / 4 : ℝ) * E i ^ B *
              oneHighVariationWeight p base (s + loss + d) (x - center) v := by
  intro k
  obtain ⟨d, hd⟩ := hpos (max 1 k)
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hd s
  refine ⟨2 * B, mul_pos (by norm_num) hB, fun i a b q hab hq => ?_⟩
  obtain ⟨J, hJ⟩ := hb i a b q hab hq
  let K := smoothDirections_mixedDifference
    (hΩ i) (hf i) center hcenter a b q (hP i q hq) J
  refine ⟨K, fun x hx v => ?_⟩
  have hHpow : 0 ≤ H i ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hH i) _
  have hEpow : 0 ≤ E i ^ B := Real.rpow_nonneg (zero_le_one.trans (hE i)) _
  have hM : 0 ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B :=
    mul_nonneg (mul_nonneg hB.le hHpow) hEpow
  have hh := smoothDirections_weighted_mixedDifference_allOrders_bound
    (hΩ i) (hf i) p base (s + loss + d) center x hcenter hx
    (hseg x hx) (hlow x hx) a b q (hP i q hq) J hM (hδ i a q hq)
    (fun j hj hjpos y hy w => by
      simpa only [Real.norm_eq_abs] using hJ j hj hjpos y hy w) K v
  have hW := oneHighVariationWeight_nonneg p base (s + loss + d) (x - center) v
  have hEB : E i ^ B ≤ E i ^ (2 * B) :=
    Real.rpow_le_rpow_of_exponent_le (hE i) (by linarith)
  calc
    δ i a q * |K.D k x v| ≤
        (2 * (B * H i ^ (3 / 4 : ℝ) * E i ^ B)) *
          oneHighVariationWeight p base (s + loss + d) (x - center) v := by
      simpa only [Real.norm_eq_abs] using hh
    _ = (2 * B) * H i ^ (3 / 4 : ℝ) * E i ^ B *
        oneHighVariationWeight p base (s + loss + d) (x - center) v := by ring
    _ ≤ (2 * B) * H i ^ (3 / 4 : ℝ) * E i ^ (2 * B) *
        oneHighVariationWeight p base (s + loss + d) (x - center) v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEB (mul_nonneg (by positivity) hHpow)) hW

end ContinuousFlexibility.Analysis
