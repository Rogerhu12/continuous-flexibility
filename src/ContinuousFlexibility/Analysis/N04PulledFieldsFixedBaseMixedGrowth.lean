import ContinuousFlexibility.Analysis.FlatMixedDiagonalOperations

/-!
# Mixed growth with one low base for every parameter order

The low parameter seminorm is chosen once. Each finite parameter prefix
may have its own spatial loss, chosen before the spatial order. This
retains the flat component factor of the actual coefficient correction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

def N04PulledFieldsFixedBaseMixedGrowth
    (p : ℕ → Seminorm ℝ E) (W F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ, FlatMixedDiagonalGrowth p W F J n B L

theorem N04PulledFieldsFixedBaseMixedGrowth.toHasFlatMixedTameGrowth
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : N04PulledFieldsFixedBaseMixedGrowth p W F J) :
    HasFlatMixedTameGrowth p W F J := by
  obtain ⟨B, hb⟩ := h
  exact fun n => ⟨B, hb n⟩

theorem N04PulledFieldsFixedBaseMixedGrowth.congr
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    {f g : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : N04PulledFieldsFixedBaseMixedGrowth p W F J)
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (g i))
    (hV : ∀ i, IsOpen (V i)) (heq : ∀ i, EqOn (f i) (g i) (U ×ˢ V i)) :
    N04PulledFieldsFixedBaseMixedGrowth p W F K := by
  obtain ⟨B, hb⟩ := h
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  exact ⟨L, hL.congr K hV heq⟩

/-- Taking a finite parameter prefix changes only the high loss. -/
theorem N04PulledFieldsFixedBaseMixedGrowth.of_each_diagonal_order
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ w, p B w ≤ 1 →
      ∀ y ∈ V i, ∀ a b : ℕ, a + b ≤ s →
        |jointMixedDiagonal (J i) n a b x w y| ≤
          C * F i * W i ^ Q * (1 + p (s + L) x + p (s + L) w)) :
    N04PulledFieldsFixedBaseMixedGrowth p W F J := by
  classical
  obtain ⟨B, hb⟩ := h
  refine ⟨B, fun n => ?_⟩
  choose L hL using fun k : Fin (n + 1) => hb k.val
  let L₀ : ℕ := ∑ k : Fin (n + 1), L k
  have hLk (k : Fin (n + 1)) : L k ≤ L₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  refine ⟨L₀, fun R hR s => ?_⟩
  choose C Q hC hQ hc using fun k : Fin (n + 1) => hL k R hR s
  let C₀ : ℝ := ∑ k : Fin (n + 1), C k
  let Q₀ : ℝ := ∑ k : Fin (n + 1), Q k
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun k _ => hC k)
  have hQ₀ : 0 ≤ Q₀ := Finset.sum_nonneg (fun k _ => hQ k)
  refine ⟨C₀, Q₀, hC₀, hQ₀, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  let t : Fin (n + 1) := ⟨k, by omega⟩
  have hCt : C t ≤ C₀ := Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ t)
  have hQt : Q t ≤ Q₀ := Finset.single_le_sum (fun u _ => hQ u) (Finset.mem_univ t)
  have hcoef : C t * F i * W i ^ Q t ≤ C₀ * F i * W i ^ Q₀ :=
    mul_le_mul (mul_le_mul_of_nonneg_right hCt (hF i))
      (Real.rpow_le_rpow_of_exponent_le (hW i) hQt)
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (mul_nonneg hC₀ (hF i))
  have hhigh : 1 + p (s + L t) x + p (s + L t) w ≤
      1 + p (s + L₀) x + p (s + L₀) w :=
    add_le_add (add_le_add le_rfl (hp (Nat.add_le_add_left (hLk t) s) x))
      (hp (Nat.add_le_add_left (hLk t) s) w)
  exact (hc t i x hx hxB w hw y hy a b hab).trans
    (mul_le_mul hcoef hhigh (by positivity)
      (mul_nonneg (mul_nonneg hC₀ (hF i))
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)))

theorem N04PulledFieldsFixedBaseMixedGrowth.of_mixed_oneHigh
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ y ∈ V i, ∀ v : Fin n → E,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (fun q => (J i).D n (x, q) (fun j => (v j, 0))) y| ≤
          C * F i * W i ^ Q * oneHighVariationWeight p B (s + L) x v) :
    N04PulledFieldsFixedBaseMixedGrowth p W F J := by
  obtain ⟨B, hb⟩ := h
  apply N04PulledFieldsFixedBaseMixedGrowth.of_each_diagonal_order hp hW hF
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, Q, hC, hQ, hc⟩ := hL R hR s
  refine ⟨C * ((n : ℝ) + 1), Q, by positivity, hQ,
    fun i x hx hxB w hw y hy a b hab => ?_⟩
  have hunit := multilinearTameSize_le_affine (p B) (p (s + L)) n
    (a := 1 + p (s + L) x)
    (add_nonneg zero_le_one (apply_nonneg (p (s + L)) x))
    (fun _ : Fin n => w) (fun _ => hw)
  have hunit' : oneHighVariationWeight p B (s + L) x (fun _ : Fin n => w) ≤
      1 + p (s + L) x + (n : ℝ) * p (s + L) w := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hunit
  have hweight : oneHighVariationWeight p B (s + L) x (fun _ : Fin n => w) ≤
      ((n : ℝ) + 1) * (1 + p (s + L) x + p (s + L) w) := by
    apply hunit'.trans
    nlinarith [apply_nonneg (p (s + L)) x, apply_nonneg (p (s + L)) w,
      Nat.cast_nonneg (α := ℝ) n]
  exact (hc i x hx hxB y hy (fun _ => w) a b hab).trans
    ((mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (mul_nonneg hC (hF i))
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) _))).trans_eq (by ring))

theorem UniformWeightedJointGrowth.n04PulledFields_fixedBaseMixedGrowth
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {B L : ℕ}
    (h : UniformWeightedJointGrowth p W J B L)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i)) :
    N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) J := by
  apply N04PulledFieldsFixedBaseMixedGrowth.of_mixed_oneHigh hp hW (fun _ => zero_le_one)
  refine ⟨B, fun n => ⟨n + L, fun R hR s => ?_⟩⟩
  obtain ⟨C, Q, hC, hQ, hb⟩ := h.mixed_parameter_oneHigh hp hW hV hc R hR n s
  exact ⟨C, Q, hC, hQ, by simpa only [mul_one] using hb⟩

theorem N04PulledFieldsFixedBaseMixedGrowth.linear_combination
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f g h : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)}
    (H : ∀ i, SmoothDirections (U ×ˢ V i) (h i)) (hV : ∀ i, IsOpen (V i))
    (α β : ℝ)
    (hvalue : ∀ i x, x ∈ U → ∀ y ∈ V i,
      h i (x, y) = α * f i (x, y) + β * g i (x, y))
    (hJ : N04PulledFieldsFixedBaseMixedGrowth p W F J)
    (hK : N04PulledFieldsFixedBaseMixedGrowth p W F K) :
    N04PulledFieldsFixedBaseMixedGrowth p W F H := by
  obtain ⟨B₀, hJB⟩ := hJ
  obtain ⟨B₁, hKB⟩ := hK
  refine ⟨max B₀ B₁, fun n => ?_⟩
  obtain ⟨L₀, hJL⟩ := hJB n
  obtain ⟨L₁, hKL⟩ := hKB n
  refine ⟨max L₀ L₁, ?_⟩
  exact (hJL.mono hp (fun i => zero_le_one.trans (hW i)) hF
    (le_max_left _ _) (le_max_left _ _)).linear_combination hW hF H hV α β hvalue
      (hKL.mono hp (fun i => zero_le_one.trans (hW i)) hF
        (le_max_right _ _) (le_max_right _ _))

theorem N04PulledFieldsFixedBaseMixedGrowth.reflect_angle
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    {f g : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (g i))
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hmap : ∀ i y, y ∈ V i → (y.1, -y.2) ∈ V i)
    (hvalue : ∀ i x, x ∈ U → ∀ y ∈ V i, g i (x, y) = f i (x, (y.1, -y.2)))
    (h : N04PulledFieldsFixedBaseMixedGrowth p W F J) :
    N04PulledFieldsFixedBaseMixedGrowth p W F K := by
  obtain ⟨B, hb⟩ := h
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  exact ⟨L, hL.reflect_angle K hU hV hmap hvalue⟩

/-- A uniform comparison of the component factors changes only the
numerical coefficient, leaving the common base and every loss fixed. -/
theorem N04PulledFieldsFixedBaseMixedGrowth.factor_le
    {p : ℕ → Seminorm ℝ E} {W F G : I → ℝ}
    (hW : ∀ i, 0 ≤ W i) {K : ℝ} (hK : 0 ≤ K)
    (hFG : ∀ i, F i ≤ K * G i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : N04PulledFieldsFixedBaseMixedGrowth p W F J) :
    N04PulledFieldsFixedBaseMixedGrowth p W G J := by
  obtain ⟨B, hb⟩ := h
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, Q, hC, hQ, hc⟩ := hL R hR s
  refine ⟨C * K, Q, mul_nonneg hC hK, hQ,
    fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  apply (hc i x hx hxB w hw y hy k hk a b hab).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hFG i) hC)
      (Real.rpow_nonneg (hW i) Q))
    (show 0 ≤ 1 + p (s + L) x + p (s + L) w by positivity)
  exact hh.trans_eq (by ring)

end ContinuousFlexibility.Analysis
