module

public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Point bounds after subtraction of a fixed spatial reference

The complete existence statement is proved with an abstract parameter
space and an opaque output family. Positive jets use the distributed
mixed-power estimate; the zeroth jet uses the actual first derivative
along the reference segment. Every transport of a chosen tower is
performed before specialization to the physical state space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A genuine mixed-power estimate gives the complete reference-difference
point bound, for every tower of an extensionally equal output family. -/
theorem mixedPowerBounds_difference_point_bound
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
    {f : X → PolarPoint → ℝ} {F : ℕ → ℕ → PolarPoint → X → ℝ}
    (hΩ : IsOpen Ω)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω)
    (J0 : ∀ a b : ℕ, ∀ q ∈ Ω,
      SmoothDirections U (fun x => mixedDerivative a b (f x) q))
    (hraw : MixedPowerBounds p center base loss U Ω H E f)
    (hcenter : center ∈ U)
    (hsegment : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      center + t • (x - center) ∈ U)
    (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    (hF : ∀ a b : ℕ, ∀ q ∈ Ω, ∀ x ∈ U,
      F a b q x = mixedDerivative a b (fun y => f x y - f center y) q)
    (k s : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ Ω,
      ∀ J : SmoothDirections U (F a b q),
      ∀ x ∈ U, ∀ v : Fin k → X,
        |J.D k x v| ≤ B * H q * E q ^ A *
          oneHighVariationWeight p base (s + loss) (x - center) v := by
  obtain ⟨B, A, hB, hA, hb⟩ :=
    hraw.positive_oneHigh hH hE (max 1 k) s
  refine ⟨2 * B, A, mul_pos (by norm_num) (zero_lt_one.trans_le hB), hA, ?_⟩
  intro a b hab q hq J x hx v
  let JD : SmoothDirections U
      (fun y => mixedDerivative a b (f y) q - mixedDerivative a b (f center) q) :=
    J.congr (fun y hy =>
      (hF a b q hq y hy).trans
        (mixedDerivative_sub_of_contDiffOn hΩ (hf y hy) (hf center hcenter) a b hq))
  let M : ℝ := B * H q * E q ^ A
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (zero_le_one.trans hB) (hH q hq))
    (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _)
  have hh := smoothDirections_difference_allOrders_bound (J0 a b q hq)
    p base (s + loss) center x hx (hsegment x hx) (hlow x hx) hM
    (fun j hj hjpos y hy w =>
      hb j hj hjpos a b hab q hq (J0 a b q hq) y hy (hlow y hy) w) JD v
  simpa only [JD, SmoothDirections.congr, Real.norm_eq_abs, M, mul_assoc] using hh

end ContinuousFlexibility.Analysis
