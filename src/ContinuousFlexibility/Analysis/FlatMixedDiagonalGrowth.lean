import ContinuousFlexibility.Analysis.JointMixedDiagonalCalculus
import ContinuousFlexibility.Analysis.MixedAffineInterpolation
import ContinuousFlexibility.Analysis.MixedParameterSymmetry
import ContinuousFlexibility.Analysis.SymmetricMultilinearDiagonalBounds

/-!
# Products of mixed jets at a fixed parameter order

Only finitely many parameter arities are used in a product. The radial
and angular orders retain their exact complementary Leibniz budgets.
Interpolation therefore gives a loss chosen before every spatial order,
even when the low order of a factor depends on its parameter arity.
The independent flat label factor is retained through multiplication.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

def FlatMixedDiagonalGrowth
    (p : ℕ → Seminorm ℝ E) (W F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (n low loss : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
    ∀ i x, x ∈ U → p low x ≤ R → ∀ w, p low w ≤ 1 →
    ∀ y ∈ V i, ∀ k : ℕ, k ≤ n → ∀ a b : ℕ, a + b ≤ s →
      |jointMixedDiagonal (J i) k a b x w y| ≤
        C * F i * W i ^ Q * (1 + p (s + loss) x + p (s + loss) w)

theorem FlatMixedDiagonalGrowth.mono
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W F : I → ℝ} (hW : ∀ i, 0 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {n low loss low' loss' : ℕ}
    (h : FlatMixedDiagonalGrowth p W F J n low loss)
    (hb : low ≤ low') (hl : loss ≤ loss') :
    FlatMixedDiagonalGrowth p W F J n low' loss' := by
  intro R hR s
  obtain ⟨C, Q, hC, hQ, hbnd⟩ := h R hR s
  refine ⟨C, Q, hC, hQ, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  apply (hbnd i x hx ((hp hb x).trans hxB) w ((hp hb w).trans hw)
    y hy k hk a b hab).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg hC (hF i)) (Real.rpow_nonneg (hW i) Q))
  exact add_le_add (add_le_add le_rfl (hp (Nat.add_le_add_left hl s) x))
    (hp (Nat.add_le_add_left hl s) w)

theorem FlatMixedDiagonalGrowth.congr
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    {f g : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {n low loss : ℕ} (h : FlatMixedDiagonalGrowth p W F J n low loss)
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (g i))
    (hV : ∀ i, IsOpen (V i)) (heq : ∀ i, EqOn (f i) (g i) (U ×ˢ V i)) :
    FlatMixedDiagonalGrowth p W F K n low loss := by
  intro R hR s
  obtain ⟨C, Q, hC, hQ, hb⟩ := h R hR s
  refine ⟨C, Q, hC, hQ, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  rw [← jointMixedDiagonal_congr (J i) (K i) (hV i) (heq i) k a b x w hx hy]
  exact hb i x hx hxB w hw y hy k hk a b hab

/-- A common coefficient and component exponent for all smaller spatial
orders, retaining each smaller order in its own high seminorm. -/
theorem FlatMixedDiagonalGrowth.spatial_orders
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {n low loss : ℕ} (h : FlatMixedDiagonalGrowth p W F J n low loss)
    (R : ℝ) (hR : 0 ≤ R) (s : ℕ) :
    ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p low x ≤ R → ∀ w, p low w ≤ 1 →
      ∀ y ∈ V i, ∀ k : ℕ, k ≤ n → ∀ a b : ℕ, a + b ≤ s →
        |jointMixedDiagonal (J i) k a b x w y| ≤
          C * F i * W i ^ Q *
            (1 + p (a + b + loss) x + p (a + b + loss) w) := by
  classical
  have hfinite (t : Fin (s + 1)) := h R hR t.val
  choose C Q hC hQ hb using hfinite
  let C₀ : ℝ := ∑ t : Fin (s + 1), C t
  let Q₀ : ℝ := ∑ t : Fin (s + 1), Q t
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun t _ => hC t)
  have hQ₀ : 0 ≤ Q₀ := Finset.sum_nonneg (fun t _ => hQ t)
  refine ⟨C₀, Q₀, hC₀, hQ₀, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  let t : Fin (s + 1) := ⟨a + b, by omega⟩
  have hCt : C t ≤ C₀ := Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ t)
  have hQt : Q t ≤ Q₀ := Finset.single_le_sum (fun u _ => hQ u) (Finset.mem_univ t)
  have hpow := Real.rpow_le_rpow_of_exponent_le (hW i) hQt
  have hfactor : C t * F i * W i ^ Q t ≤ C₀ * F i * W i ^ Q₀ :=
    mul_le_mul (mul_le_mul_of_nonneg_right hCt (hF i)) hpow
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (mul_nonneg hC₀ (hF i))
  exact (hb t i x hx hxB w hw y hy k hk a b le_rfl).trans
    (mul_le_mul_of_nonneg_right hfactor (by positivity))

private def mixedLeibnizMass (n a b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
    ∑ k ∈ Finset.range (n + 1),
      (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ)

private theorem mixedLeibnizMass_nonneg (n a b : ℕ) : 0 ≤ mixedLeibnizMass n a b := by
  unfold mixedLeibnizMass
  positivity

private theorem nonnegative_entry_le_triple_sum
    (M : ℕ → ℕ → ℕ → ℝ) (hM : ∀ i j k, 0 ≤ M i j k)
    {n s k a b : ℕ} (hk : k ≤ n) (hab : a + b ≤ s) :
    M k a b ≤
      ∑ t : Fin (n + 1), ∑ u : Fin (s + 1), ∑ v : Fin (s + 1),
        M t.val u.val v.val := by
  classical
  let kn : Fin (n + 1) := ⟨k, by omega⟩
  let an : Fin (s + 1) := ⟨a, by omega⟩
  let bn : Fin (s + 1) := ⟨b, by omega⟩
  calc
    M k a b ≤
        ∑ v : Fin (s + 1), M k a v.val :=
      Finset.single_le_sum
        (f := fun v : Fin (s + 1) => M k a v.val)
        (fun v _ => hM k a v.val) (Finset.mem_univ bn)
    _ ≤ ∑ u : Fin (s + 1), ∑ v : Fin (s + 1),
        M k u.val v.val :=
      Finset.single_le_sum
        (f := fun u : Fin (s + 1) =>
          ∑ v : Fin (s + 1), M k u.val v.val)
        (fun u _ => Finset.sum_nonneg
          (fun v _ => hM k u.val v.val)) (Finset.mem_univ an)
    _ ≤ ∑ t : Fin (n + 1), ∑ u : Fin (s + 1), ∑ v : Fin (s + 1),
        M t.val u.val v.val :=
      Finset.single_le_sum
        (f := fun t : Fin (n + 1) =>
          ∑ u : Fin (s + 1), ∑ v : Fin (s + 1),
            M t.val u.val v.val)
        (fun t _ => Finset.sum_nonneg (fun u _ => Finset.sum_nonneg
          (fun v _ => hM t.val u.val v.val)))
        (Finset.mem_univ kn)


private theorem mixedLeibnizMass_le_total
    {n s k a b : ℕ} (hk : k ≤ n) (hab : a + b ≤ s) :
    mixedLeibnizMass k a b ≤
      ∑ t : Fin (n + 1), ∑ u : Fin (s + 1), ∑ v : Fin (s + 1),
        mixedLeibnizMass t.val u.val v.val := by
  exact nonnegative_entry_le_triple_sum mixedLeibnizMass
    mixedLeibnizMass_nonneg (n := n) (s := s) (k := k) (a := a) (b := b) hk hab

private theorem jointMixedDiagonal_mul_le
    {f g h : E × PolarPoint → ℝ} {V₀ : Set PolarPoint}
    (J : SmoothDirections (U ×ˢ V₀) f) (K : SmoothDirections (U ×ˢ V₀) g)
    (L : SmoothDirections (U ×ˢ V₀) h)
    (hU : IsOpen U) (hV : IsOpen V₀) (hc : Convex ℝ (U ×ˢ V₀))
    (hprod : ∀ x ∈ U, ∀ p ∈ V₀, h (x, p) = f (x, p) * g (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {y : PolarPoint} (hy : y ∈ V₀)
    (Z : ℝ)
    (hterm : ∀ j ≤ b, ∀ i ≤ a, ∀ k ≤ n,
      |jointMixedDiagonal J k i j x w y| *
        |jointMixedDiagonal K (n - k) (a - i) (b - j) x w y| ≤ Z) :
    |jointMixedDiagonal L n a b x w y| ≤ mixedLeibnizMass n a b * Z := by
  rw [jointMixedDiagonal_mul J K L hU hV hc hprod n a b x w hx hy]
  calc
    _ ≤ ∑ j ∈ Finset.range (b + 1),
        ∑ i ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (n + 1),
          |(b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
            jointMixedDiagonal J k i j x w y *
              jointMixedDiagonal K (n - k) (a - i) (b - j) x w y| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (b + 1),
        ∑ i ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (n + 1),
          ((b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ)) * Z := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      have hj' : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hi' : i ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤
        (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) by positivity)]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (hterm j hj' i hi' k hk') (by positivity)
    _ = mixedLeibnizMass n a b * Z := by
      simp only [mixedLeibnizMass, Finset.sum_mul]

/-- The product has a fixed loss at each fixed parameter order and
retains the product of its two label factors. -/
theorem FlatMixedDiagonalGrowth.mul
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
    {n B₀ L₀ B₁ L₁ : ℕ}
    (hJ : FlatMixedDiagonalGrowth p W F J n B₀ L₀)
    (hK : FlatMixedDiagonalGrowth p W G K n B₁ L₁) :
    ∃ B M : ℕ, max B₀ B₁ ≤ B ∧
      FlatMixedDiagonalGrowth p W (fun i => F i * G i) L n B M := by
  classical
  obtain ⟨B, M, hB, hinterp⟩ :=
    hasInterpolation_affine_mixed_product p hp hI L₀ L₁ (max B₀ B₁)
  refine ⟨B, M, hB, fun R hR s => ?_⟩
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
        rw [Real.rpow_add (zero_lt_one.trans_le (hW i))]
        ring
      _ ≤ (A * A' * (F i * G i) * W i ^ (P + P')) * (D * H) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = Z := by dsimp only [Z]; ring
  have hpoint := jointMixedDiagonal_mul_le (J i) (K i) (L i) hU (hV i) (hc i)
    (hprod i) k a b x w hx hy Z hterm
  have hmass : mixedLeibnizMass k a b ≤ N :=
    mixedLeibnizMass_le_total (n := n) (s := s) (k := k) (a := a) (b := b) hk hab
  exact hpoint.trans ((mul_le_mul_of_nonneg_right hmass hZ).trans_eq
    (by dsimp only [Z, H]; ring))

end ContinuousFlexibility.Analysis
