import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Tame transport for the actual Nash--Moser spaces

The finite products in the nonlinear statement use sums of seminorms, whereas
the literal projective-limit product uses maxima.  These elementary transfer
lemmas keep the derivative towers and the same finite derivative loss while
changing between uniformly comparable gradings.  Linear precomposition also
covers restriction to a closed affine tangent space after translation of the
base point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

section ProductEstimate

private theorem solve_product_le {k : ℕ} (a b : Fin k → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, a i ≤ A * b i) (t : Finset (Fin k)) :
    (∏ i ∈ t, a i) ≤ A ^ k * ∏ i ∈ t, b i := by
  have ht : t.card ≤ k := by simpa using Finset.card_le_univ t
  calc
    (∏ i ∈ t, a i) ≤ ∏ i ∈ t, A * b i :=
      Finset.prod_le_prod₀ (fun i _ => ha i) (fun i _ => hab i)
    _ = A ^ t.card * ∏ i ∈ t, b i := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ A ^ k * ∏ i ∈ t, b i :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA ht)
        (Finset.prod_nonneg fun i _ => hb i)

/-- A common bound on the grading of a linear change of variables controls
the one-high-factor expression with the same derivative loss. -/
theorem solve_oneHighWeight_le
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (L : X →ₗ[ℝ] Y) (A : ℝ) (hA : 1 ≤ A)
    (hL : ∀ n x, q n (L x) ≤ A * p n x)
    (b s : ℕ) (x : X) {k : ℕ} (v : Fin k → X) :
    ((1 + q s (L x)) * ∏ i, q b (L (v i)) +
      ∑ i : Fin k, q s (L (v i)) * ∏ j ∈ Finset.univ.erase i, q b (L (v j))) ≤
    A ^ (k + 1) *
      ((1 + p s x) * ∏ i, p b (v i) +
        ∑ i : Fin k, p s (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hprod (t : Finset (Fin k)) :
      (∏ i ∈ t, q b (L (v i))) ≤ A ^ k * ∏ i ∈ t, p b (v i) :=
    solve_product_le _ _ A hA (fun _ => apply_nonneg _ _)
      (fun _ => apply_nonneg _ _) (fun i => hL b (v i)) t
  have hfirst :
      (1 + q s (L x)) * ∏ i, q b (L (v i)) ≤
        A ^ (k + 1) * ((1 + p s x) * ∏ i, p b (v i)) := by
    have hp : 1 + q s (L x) ≤ A * (1 + p s x) := by
      nlinarith only [hL s x, hA]
    have h := mul_le_mul hp (hprod Finset.univ)
      (Finset.prod_nonneg fun i _ => apply_nonneg _ _)
      (mul_nonneg hA0 (add_nonneg zero_le_one (apply_nonneg _ _)))
    calc
      (1 + q s (L x)) * ∏ i, q b (L (v i)) ≤
        (A * (1 + p s x)) * (A ^ k * ∏ i, p b (v i)) := h
      _ = A ^ (k + 1) * ((1 + p s x) * ∏ i, p b (v i)) := by
        rw [pow_succ]; ring
  have hterm (i : Fin k) :
      q s (L (v i)) * ∏ j ∈ Finset.univ.erase i, q b (L (v j)) ≤
        A ^ (k + 1) * (p s (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)) := by
    have h := mul_le_mul (hL s (v i)) (hprod (Finset.univ.erase i))
      (Finset.prod_nonneg fun j _ => apply_nonneg _ _)
      (mul_nonneg hA0 (apply_nonneg _ _))
    calc
      q s (L (v i)) * ∏ j ∈ Finset.univ.erase i, q b (L (v j)) ≤
        (A * p s (v i)) * (A ^ k * ∏ j ∈ Finset.univ.erase i, p b (v j)) := h
      _ = A ^ (k + 1) * (p s (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)) := by
        rw [pow_succ]; ring
  calc
    _ ≤ A ^ (k + 1) * ((1 + p s x) * ∏ i, p b (v i)) +
        ∑ i : Fin k, A ^ (k + 1) *
          (p s (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)) :=
      add_le_add hfirst (Finset.sum_le_sum fun i _ => hterm i)
    _ = _ := by rw [← Finset.mul_sum, ← mul_add]

end ProductEstimate

section TameTransport

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- Pull back the actual directional derivative tower along a continuous
linear map. No nonlinear chain rule is used. -/
def solveSmoothDirectionsPrecomp {U : Set Y} {f : Y → Z}
    (J : SmoothDirections U f) (L : X →L[ℝ] Y) :
    SmoothDirections (L ⁻¹' U) (fun x => f (L x)) where
  open_domain := J.open_domain.preimage L.continuous
  D := fun n x => (J.D n (L x)).compContinuousLinearMap (fun _ => L)
  zero := by
    intro x hx
    have e : (fun i : Fin 0 => L (Fin.elim0 i)) = Fin.elim0 := by
      funext i; exact i.elim0
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, e] using J.zero (L x) hx
  continuous := by
    intro n
    have hc : Continuous (fun p : X × (Fin n → X) => (L p.1, fun i => L (p.2 i))) :=
      (L.continuous.comp continuous_fst).prodMk
        (continuous_pi fun i => L.continuous.comp ((continuous_apply i).comp continuous_snd))
    exact (J.continuous n).comp hc.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)
  derivative := by
    intro n x hx v w
    have e : (fun i => L ((Fin.cons w v : Fin (n + 1) → X) i)) =
        (Fin.cons (L w) (fun i => L (v i)) : Fin (n + 1) → Y) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, e] using
      HasProjectiveLineDerivAt.comp_linear L.toLinearMap
        (J.derivative n (L x) hx (fun i => L (v i)) (L w))

/-- Smooth tameness is stable under a uniformly bounded linear change of
the input grading, including a closed tangent-space inclusion. -/
theorem solve_smoothTameOn_precomp
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {U : Set Y} {f : Y → Z} (h : SmoothTameOn q r U f)
    (L : X →L[ℝ] Y) {A : ℝ} (hA : 1 ≤ A)
    (hL : ∀ n x, q n (L x) ≤ A * p n x) :
    SmoothTameOn p r (L ⁻¹' U) (fun x => f (L x)) := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨solveSmoothDirectionsPrecomp J L, fun k x0 hx0 => ?_⟩
  obtain ⟨loss, base, ε, hε, hs⟩ := hJ k (L x0) hx0
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨loss, base, ε / A, div_pos hε hApos, fun s hs' => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hs s hs'
  refine ⟨C * A ^ (k + 1), mul_nonneg hC (pow_nonneg hApos.le _),
    fun x hx hxε v => ?_⟩
  have hxε' : q base (L x - L x0) < ε := by
    rw [← map_sub]
    have hsmall : A * p base (x - x0) < ε := by
      simpa only [mul_comm] using (lt_div_iff₀ hApos).mp hxε
    exact (hL base (x - x0)).trans_lt hsmall
  have hw := solve_oneHighWeight_le p q L.toLinearMap A hA hL base (s + loss) x v
  have hb := hbound (L x) hx hxε' (fun i => L (v i))
  change r s ((J.D k (L x)) (fun i => L (v i))) ≤ _
  calc
    _ ≤ C *
        ((1 + q (s + loss) (L x)) * ∏ i, q base (L (v i)) +
          ∑ i : Fin k, q (s + loss) (L (v i)) *
            ∏ j ∈ Finset.univ.erase i, q base (L (v j))) := hb
    _ ≤ C * (A ^ (k + 1) *
        ((1 + p (s + loss) x) * ∏ i, p base (v i) +
          ∑ i : Fin k, p (s + loss) (v i) *
            ∏ j ∈ Finset.univ.erase i, p base (v j))) :=
      mul_le_mul_of_nonneg_left hw hC
    _ = _ := by rw [mul_assoc]

/-- Postcompose a directional derivative tower by a continuous linear map. -/
def solveSmoothDirectionsPostcomp {U : Set X} {f : X → Y}
    (J : SmoothDirections U f) (L : Y →L[ℝ] Z) :
    SmoothDirections U (fun x => L (f x)) where
  open_domain := J.open_domain
  D := fun n x => L.compContinuousMultilinearMap (J.D n x)
  zero := by
    intro x hx
    change L (J.D 0 x Fin.elim0) = L (f x)
    rw [J.zero x hx]
  continuous := fun n => L.continuous.comp_continuousOn (J.continuous n)
  derivative := fun n x hx v w => (J.derivative n x hx v w).clm_comp L

/-- A uniformly bounded change of output grading preserves the same tame
loss and local input neighbourhood. -/
theorem solve_smoothTameOn_postcomp
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {U : Set X} {f : X → Y} (h : SmoothTameOn p q U f)
    (L : Y →L[ℝ] Z) {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ n y, r n (L y) ≤ B * q n y) :
    SmoothTameOn p r U (fun x => L (f x)) := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨solveSmoothDirectionsPostcomp J L, fun k x0 hx0 => ?_⟩
  obtain ⟨loss, base, ε, hε, hs⟩ := hJ k x0 hx0
  refine ⟨loss, base, ε, hε, fun s hs' => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hs s hs'
  refine ⟨B * C, mul_nonneg hB hC, fun x hx hxε v => ?_⟩
  change r s (L (J.D k x v)) ≤ _
  exact (hL s _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound x hx hxε v) hB)

end TameTransport

section SmoothingComparison

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- Uniformly equivalent gradings have the same smoothing families, with
unchanged smoothing loss and new scalar constants. -/
theorem solve_hasSmoothing_of_comparable
    {p q : ℕ → Seminorm ℝ X} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpq : ∀ n x, p n x ≤ A * q n x)
    (hqp : ∀ n x, q n x ≤ B * p n x)
    (hp : HasSmoothing p) : HasSmoothing q := by
  obtain ⟨base, loss, S, hforward, hbackward, happrox⟩ := hp
  refine ⟨base, loss, S, ?_, ?_, happrox⟩
  · intro m n hm hmn
    obtain ⟨C, hC, hc⟩ := hforward m n hm hmn
    refine ⟨B * C * A, mul_nonneg (mul_nonneg hB hC) hA, fun N x => ?_⟩
    calc
      q n (S N x) ≤ B * p n (S N x) := hqp n _
      _ ≤ B * (C * Real.exp (((n : ℝ) - m + loss) * N) * p m x) :=
        mul_le_mul_of_nonneg_left (hc N x) hB
      _ ≤ B * (C * Real.exp (((n : ℝ) - m + loss) * N) * (A * q m x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hpq m x) (mul_nonneg hC (Real.exp_pos _).le)) hB
      _ = _ := by ring
  · intro m n hm hmn
    obtain ⟨C, hC, hc⟩ := hbackward m n hm hmn
    refine ⟨B * C * A, mul_nonneg (mul_nonneg hB hC) hA, fun N x => ?_⟩
    calc
      q m (x - S N x) ≤ B * p m (x - S N x) := hqp m _
      _ ≤ B * (C * Real.exp (-((n : ℝ) - m - loss) * N) * p n x) :=
        mul_le_mul_of_nonneg_left (hc N x) hB
      _ ≤ B * (C * Real.exp (-((n : ℝ) - m - loss) * N) * (A * q n x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hpq n x) (mul_nonneg hC (Real.exp_pos _).le)) hB
      _ = _ := by ring

end SmoothingComparison

end ContinuousFlexibility.Analysis
