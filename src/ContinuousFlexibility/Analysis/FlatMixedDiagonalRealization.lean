import ContinuousFlexibility.Analysis.FlatMixedDiagonalGrowth

/-!
# Finite parameter budgets and the actual multilinear mixed jets

A separate fixed loss for each parameter arity suffices: a finite
maximum is chosen before the spatial order. Conversely, symmetry of
the genuine tower and algebraic multilinear normalization recover the
full one-high bound from its diagonal. Neither operation changes the
retained flat label factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

def HasFlatMixedTameGrowth
    (p : ℕ → Seminorm ℝ E) (W F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)) : Prop :=
  ∀ n : ℕ, ∃ B L : ℕ, FlatMixedDiagonalGrowth p W F J n B L

theorem HasFlatMixedTameGrowth.of_each_diagonal_order
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : ∀ n : ℕ, ∃ B L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ w, p B w ≤ 1 →
      ∀ y ∈ V i, ∀ a b : ℕ, a + b ≤ s →
        |jointMixedDiagonal (J i) n a b x w y| ≤
          C * F i * W i ^ Q * (1 + p (s + L) x + p (s + L) w)) :
    HasFlatMixedTameGrowth p W F J := by
  classical
  intro n
  choose B L hb using fun k : Fin (n + 1) => h k.val
  let B₀ : ℕ := ∑ k : Fin (n + 1), B k
  let L₀ : ℕ := ∑ k : Fin (n + 1), L k
  have hBk (k : Fin (n + 1)) : B k ≤ B₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hLk (k : Fin (n + 1)) : L k ≤ L₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  refine ⟨B₀, L₀, fun R hR s => ?_⟩
  choose C Q hC hQ hc using fun k : Fin (n + 1) => hb k R hR s
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
  exact (hc t i x hx ((hp (hBk t) x).trans hxB) w ((hp (hBk t) w).trans hw)
    y hy a b hab).trans (mul_le_mul hcoef hhigh (by positivity)
      (mul_nonneg (mul_nonneg hC₀ (hF i))
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)))

theorem HasFlatMixedTameGrowth.of_mixed_oneHigh
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (h : ∀ n : ℕ, ∃ B L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ y ∈ V i, ∀ v : Fin n → E,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (fun q => (J i).D n (x, q) (fun j => (v j, 0))) y| ≤
          C * F i * W i ^ Q * oneHighVariationWeight p B (s + L) x v) :
    HasFlatMixedTameGrowth p W F J := by
  apply HasFlatMixedTameGrowth.of_each_diagonal_order hp hW hF
  intro n
  obtain ⟨B, L, hb⟩ := h n
  refine ⟨B, L, fun R hR s => ?_⟩
  obtain ⟨C, Q, hC, hQ, hc⟩ := hb R hR s
  refine ⟨C * ((n : ℝ) + 1), Q, by positivity, hQ,
    fun i x hx hxB w hw y hy a b hab => ?_⟩
  have hunit : oneHighVariationWeight p B (s + L) x (fun _ : Fin n => w) ≤
      1 + p (s + L) x + ∑ _i : Fin n, p (s + L) w :=
    multilinearTameSize_le_affine (p B) (p (s + L)) n
      (a := 1 + p (s + L) x)
      (add_nonneg zero_le_one (apply_nonneg (p (s + L)) x))
      (fun _ : Fin n => w) (fun _ => hw)
  have hunit' : oneHighVariationWeight p B (s + L) x (fun _ : Fin n => w) ≤
      1 + p (s + L) x + (n : ℝ) * p (s + L) w := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hunit
  have hweight : oneHighVariationWeight p B (s + L) x (fun _ : Fin n => w) ≤
      ((n : ℝ) + 1) * (1 + p (s + L) x + p (s + L) w) := by
    apply hunit'.trans
    nlinarith [apply_nonneg (p (s + L)) x, apply_nonneg (p (s + L)) w,
      Nat.cast_nonneg (α := ℝ) n]
  exact (hc i x hx hxB y hy (fun _ => w) a b hab).trans
    ((mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (mul_nonneg hC (hF i))
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) _))).trans_eq (by ring))

theorem UniformWeightedJointGrowth.hasFlatMixedTameGrowth
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {B L : ℕ}
    (h : UniformWeightedJointGrowth p W J B L)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i)) :
    HasFlatMixedTameGrowth p W (fun _ => 1) J := by
  apply HasFlatMixedTameGrowth.of_mixed_oneHigh hp hW (fun _ => zero_le_one)
  intro n
  refine ⟨B, n + L, fun R hR s => ?_⟩
  obtain ⟨C, Q, hC, hQ, hb⟩ := h.mixed_parameter_oneHigh hp hW hV hc R hR n s
  exact ⟨C, Q, hC, hQ, by simpa only [mul_one] using hb⟩

theorem HasFlatMixedTameGrowth.mul
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    {W F G : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    (hF : ∀ i, 0 ≤ F i) (hG : ∀ i, 0 ≤ G i)
    {f g h : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)}
    (L : ∀ i, SmoothDirections (U ×ˢ V i) (h i))
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (hprod : ∀ i x, x ∈ U → ∀ y ∈ V i, h i (x, y) = f i (x, y) * g i (x, y))
    (hJ : HasFlatMixedTameGrowth p W F J)
    (hK : HasFlatMixedTameGrowth p W G K) :
    HasFlatMixedTameGrowth p W (fun i => F i * G i) L := by
  intro n
  obtain ⟨B₀, L₀, hJ⟩ := hJ n
  obtain ⟨B₁, L₁, hK⟩ := hK n
  obtain ⟨B, M, _, hb⟩ := hJ.mul hp hI hW hF hG L hU hV hc hprod hK
  exact ⟨B, M, hb⟩

/-- Symmetry and normalization recover the full actual mixed multilinear
estimate with the same spatial loss and the same label factor. -/
theorem FlatMixedDiagonalGrowth.mixed_oneHigh
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    {n B L : ℕ} (h : FlatMixedDiagonalGrowth p W F J n B L)
    (R : ℝ) (hR : 0 ≤ R) (s : ℕ) :
    ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ y ∈ V i, ∀ v : Fin n → E,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (fun q => (J i).D n (x, q) (fun j => (v j, 0))) y| ≤
          C * F i * W i ^ Q * oneHighVariationWeight p B (s + L) x v := by
  obtain ⟨K, hK, hpolar⟩ := exists_symmetric_multilinear_diagonal_affine_bound n
  obtain ⟨C, Q, hC, hQ, hb⟩ := h R hR s
  refine ⟨K * C, Q, mul_nonneg hK hC, hQ, fun i x hx hxB y hy v a b hab => ?_⟩
  let A := (J i).mixedParameterMultilinearMap (hV i) n a b x hx y hy
  have hAperm : ∀ u (σ : Equiv.Perm (Fin n)), A (u ∘ σ) = A u :=
    fun u σ => (J i).mixedParameterMultilinearMap_comp_perm (hV i) (hc i)
      n a b x hx y hy u σ
  have hC' : 0 ≤ C * F i * W i ^ Q := mul_nonneg (mul_nonneg hC (hF i))
    (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  have hdiag (w : E) (hw : p B w ≤ 1) : |A (fun _ => w)| ≤
      (C * F i * W i ^ Q) * (1 + p (s + L) x + p (s + L) w) :=
    hb i x hx hxB w hw y hy n le_rfl a b hab
  have hall := hpolar E (p B) (p (s + L)) A hAperm x _ hC' hdiag
  have hnorm := multilinearMap_bound_of_unitBall A (normSeminorm ℝ ℝ)
    (p B) (p (s + L)) (mul_nonneg hK hC')
    (fun u hu => by
      simpa only [coe_normSeminorm, Real.norm_eq_abs] using
        hall u (fun t => (hu t).le)) v
  have hnorm' : |A v| ≤ (K * (C * F i * W i ^ Q)) *
      oneHighVariationWeight p B (s + L) x v := by
    simpa only [coe_normSeminorm, Real.norm_eq_abs, multilinearTameSize,
      oneHighVariationWeight] using hnorm
  exact hnorm'.trans_eq (by ring)

end ContinuousFlexibility.Analysis
