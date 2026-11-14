module

public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseAffineProduct
public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseMixedGrowth

/-!
# Fixed-base multiplication of genuine mixed jets

The three-index Leibniz formula is the existing genuine tower identity.
The scalar interpolation estimate keeps its low base independent of the
parameter prefix; only the high derivative loss changes with that prefix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

private theorem n04PulledFields_flatMixed_mul_at_fixedBase
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F G : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    (hF : ∀ i, 0 ≤ F i) (hG : ∀ i, 0 ≤ G i)
    {f g h : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)}
    (L : ∀ i, SmoothDirections (U ×ˢ V i) (h i))
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (hprod : ∀ i x, x ∈ U → ∀ y ∈ V i, h i (x, y) = f i (x, y) * g i (x, y))
    {n B₀ L₀ B₁ L₁ B M : ℕ}
    (hJ : FlatMixedDiagonalGrowth p W F J n B₀ L₀)
    (hK : FlatMixedDiagonalGrowth p W G K n B₁ L₁)
    (hB : max B₀ B₁ ≤ B)
    (hinterp : ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ x w : E, p B x ≤ R → p B w ≤ 1 →
        (1 + p (a + L₀) x + p (a + L₀) w) *
          (1 + p (b + L₁) x + p (b + L₁) w) ≤
            C * (1 + p (s + M) x + p (s + M) w)) :
    FlatMixedDiagonalGrowth p W (fun i => F i * G i) L n B M := by
  classical
  intro R hR s
  obtain ⟨A, P, hA, hP, hAb⟩ := hJ.spatial_orders hW hF R hR s
  obtain ⟨A', P', hA', hP', hA'b⟩ := hK.spatial_orders hW hG R hR s
  obtain ⟨D, hD, hDb⟩ := hinterp R hR s
  let N : ℝ := ∑ k : Fin (n + 1), ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
    mixedLeibnizMass k.val a.val b.val
  have hN : 0 ≤ N := Finset.sum_nonneg (fun k _ =>
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
      (fun b _ => mixedLeibnizMass_nonneg k.val a.val b.val)))
  refine ⟨N * A * A' * D, P + P', by positivity, add_nonneg hP hP', ?_⟩
  intro i x hx hxB w hw y hy k hk a b hab
  have hFi : 0 ≤ F i := hF i
  have hGi : 0 ≤ G i := hG i
  have hWi : 0 < W i := zero_lt_one.trans_le (hW i)
  have hx₀ : p B₀ x ≤ R := (hp ((le_max_left _ _).trans hB) x).trans hxB
  have hx₁ : p B₁ x ≤ R := (hp ((le_max_right _ _).trans hB) x).trans hxB
  have hw₀ : p B₀ w ≤ 1 := (hp ((le_max_left _ _).trans hB) w).trans hw
  have hw₁ : p B₁ w ≤ 1 := (hp ((le_max_right _ _).trans hB) w).trans hw
  let H : ℝ := 1 + p (s + M) x + p (s + M) w
  let Z : ℝ := A * A' * D * (F i * G i) * W i ^ (P + P') * H
  have hZ : 0 ≤ Z := by dsimp only [Z, H]; positivity
  have hterm : ∀ v ≤ b, ∀ u ≤ a, ∀ t ≤ k,
      |jointMixedDiagonal (J i) t u v x w y| *
        |jointMixedDiagonal (K i) (k - t) (a - u) (b - v) x w y| ≤ Z := by
    intro v hv u hu t ht
    have hf := hAb i x hx hx₀ w hw₀ y hy t (ht.trans hk) u v (by omega)
    have hg := hA'b i x hx hx₁ w hw₁ y hy (k - t) (by omega)
      (a - u) (b - v) (by omega)
    have hbudget := hDb (u + v) (a - u + (b - v)) (by omega) x w hxB hw
    have hf0 : 0 ≤ A * F i * W i ^ P *
        (1 + p (u + v + L₀) x + p (u + v + L₀) w) := by positivity
    apply (mul_le_mul hf hg (abs_nonneg _) hf0).trans
    calc
      _ = (A * A' * (F i * G i) * W i ^ (P + P')) *
          ((1 + p (u + v + L₀) x + p (u + v + L₀) w) *
            (1 + p (a - u + (b - v) + L₁) x + p (a - u + (b - v) + L₁) w)) := by
        rw [Real.rpow_add hWi]
        ring
      _ ≤ (A * A' * (F i * G i) * W i ^ (P + P')) * (D * H) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = Z := by dsimp only [Z]; ring
  have hpoint := jointMixedDiagonal_mul_le (J i) (K i) (L i) hU (hV i) (hc i)
    (hprod i) k a b x w hx hy Z hterm
  let kn : Fin (n + 1) := ⟨k, by omega⟩
  let an : Fin (s + 1) := ⟨a, by omega⟩
  let bn : Fin (s + 1) := ⟨b, by omega⟩
  have hmass : mixedLeibnizMass k a b ≤ N :=
    flatMixed_triple_sum_bound
      (fun (k' : Fin (n + 1)) (a' b' : Fin (s + 1)) =>
        mixedLeibnizMass k'.val a'.val b'.val)
      (fun k' a' b' => mixedLeibnizMass_nonneg k'.val a'.val b'.val) kn an bn
  exact hpoint.trans ((mul_le_mul_of_nonneg_right hmass hZ).trans_eq
    (by dsimp only [Z, H]; ring))

theorem N04PulledFieldsFixedBaseMixedGrowth.mul
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
    (hJ : N04PulledFieldsFixedBaseMixedGrowth p W F J)
    (hK : N04PulledFieldsFixedBaseMixedGrowth p W G K) :
    N04PulledFieldsFixedBaseMixedGrowth p W (fun i => F i * G i) L := by
  obtain ⟨B₀, hJB⟩ := hJ
  obtain ⟨B₁, hKB⟩ := hK
  obtain ⟨B, hB, hb⟩ :=
    n04PulledFields_affine_mixed_product_fixedBase p hp hI (max B₀ B₁)
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L₀, hJL⟩ := hJB n
  obtain ⟨L₁, hKL⟩ := hKB n
  obtain ⟨M, hM⟩ := hb L₀ L₁
  exact ⟨M, n04PulledFields_flatMixed_mul_at_fixedBase hp hW hF hG L
    hU hV hc hprod hJL hKL hB hM⟩

end ContinuousFlexibility.Analysis
