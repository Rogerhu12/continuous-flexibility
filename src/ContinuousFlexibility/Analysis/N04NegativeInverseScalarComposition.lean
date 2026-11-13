import ContinuousFlexibility.Analysis.N01cCompositionJetBounds
import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget

/-!
# Smooth finite-dimensional composition with the saved inverse degree

Every positive inner block has degree `spatial + shift * parameter - 1`.
The sum over a nonempty partition is at most the same degree of the
original tuple.  The first positive parameter height factor is kept;
only additional copies enter a uniform coefficient.

The intermediate space is any normed space. This covers a fixed scalar
root transition as well as multiplication of two scalar fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04NegativeInverse_slotDegree_sum_le
    {n : ℕ} (hn : 0 < n) (κ β : Fin n → ℕ)
    (shift : ℕ) (hshift : 1 ≤ shift) (hpart : ∀ i, 0 < κ i + β i) :
    (∑ i, (β i + shift * κ i - 1)) ≤
      (∑ i, β i) + shift * (∑ i, κ i) - 1 := by
  have hp (i : Fin n) : β i + shift * κ i - 1 + 1 = β i + shift * κ i := by
    have hκ : κ i ≤ shift * κ i := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (κ i) hshift
    have h := hpart i
    omega
  have hs : (∑ i, (β i + shift * κ i - 1)) + n =
      (∑ i, β i) + shift * (∑ i, κ i) := by
    calc
      _ = ∑ i, (β i + shift * κ i - 1 + 1) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one]
      _ = ∑ i, (β i + shift * κ i) := Finset.sum_congr rfl (fun i _ => hp i)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  omega

theorem n04NegativeInverse_heightWeight_prod_le
    {H L : ℝ} (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    {n : ℕ} (κ : Fin n → ℕ) :
    (∏ i, parameterHeightWeight H (κ i)) ≤
      L ^ n * parameterHeightWeight H (∑ i, κ i) := by
  induction n with
  | zero =>
      simp only [Fin.prod_univ_zero, Fin.sum_univ_zero, pow_zero,
        parameterHeightWeight, ite_true, one_mul, le_refl]
  | succ n ih =>
      have ht := ih (Fin.tail κ)
      have hh := n01c_parameterHeightWeight_mul_le hH hHL hL
        (κ 0) (∑ i : Fin n, κ i.succ)
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      calc
        _ ≤ parameterHeightWeight H (κ 0) *
            (L ^ n * parameterHeightWeight H (∑ i : Fin n, κ i.succ)) :=
          mul_le_mul_of_nonneg_left ht (parameterHeightWeight_nonneg hH _)
        _ = L ^ n * (parameterHeightWeight H (κ 0) *
            parameterHeightWeight H (∑ i : Fin n, κ i.succ)) := by ring
        _ ≤ L ^ n * (L * parameterHeightWeight H (κ 0 + ∑ i : Fin n, κ i.succ)) :=
          mul_le_mul_of_nonneg_left hh (pow_nonneg (zero_le_one.trans hL) _)
        _ = _ := by rw [pow_succ]; ring

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A genuine composed tower retains the exact saved degree and the
height factor determined by the original parameter slots. -/
theorem n04NegativeInverse_contDiff_comp_sharp_bound
    {U : Set X} {V : Set Y} {f : X → Y} {g : Y → Z}
    (J : SmoothDirections U f) (K : SmoothDirections U (g ∘ f))
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n)
    (shift : ℕ) (hshift : 1 ≤ shift) {x : X} (hx : x ∈ U)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (houter : ∀ j : ℕ, j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (v : Fin n → X)
    (hinner : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ ≤
        M * parameterHeightWeight H (w.restrict (c.emb i)).stateArity *
          t ^ ((w.restrict (c.emb i)).angleArity +
            shift * (w.restrict (c.emb i)).stateArity - 1)) :
    ‖K.D n x v‖ ≤ C * (Fintype.card (OrderedFinpartition n) : ℝ) *
      (M * L) ^ n * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) := by
  classical
  let JK := smoothDirections_contDiff_comp J hV hg hmap
  have heval : K.D n x v = JK.D n x v :=
    congrArg (fun A : X [×n]→L[ℝ] Z => A v) (K.unique JK n x hx)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hHκ : 0 ≤ parameterHeightWeight H w.stateArity := parameterHeightWeight_nonneg hH _
  have hterm (c : OrderedFinpartition n) :
      (∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖) ≤
        (M * L) ^ n * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) := by
    let κ : Fin c.length → ℕ := fun i => (w.restrict (c.emb i)).stateArity
    let β : Fin c.length → ℕ := fun i => (w.restrict (c.emb i)).angleArity
    have hcost : (∑ i, (β i + shift * κ i - 1)) ≤
        w.angleArity + shift * w.stateArity - 1 := by
      have h := n04NegativeInverse_slotDegree_sum_le (c.length_pos hn) κ β shift hshift
        (fun i => by rw [show κ i + β i = c.partSize i from
          (w.restrict (c.emb i)).arity_sum]; exact c.partSize_pos i)
      simpa only [κ, β, w.sum_restrict_stateArity c, w.sum_restrict_angleArity c] using h
    have hheight : (∏ i, parameterHeightWeight H (κ i)) ≤
        L ^ n * parameterHeightWeight H w.stateArity := by
      have hh := n04NegativeInverse_heightWeight_prod_le hH hHL hL κ
      have he : (∑ i, κ i) = w.stateArity := w.sum_restrict_stateArity c
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hL c.length_le) hHκ)
    have hprod : (∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖) ≤
        M ^ c.length * (∏ i, parameterHeightWeight H (κ i)) *
          t ^ (∑ i, (β i + shift * κ i - 1)) := by
      calc
        _ ≤ ∏ i : Fin c.length,
            M * parameterHeightWeight H (κ i) * t ^ (β i + shift * κ i - 1) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hinner c i)
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow_eq_pow_sum]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hupper : M ^ c.length * (∏ i, parameterHeightWeight H (κ i)) *
        t ^ (∑ i, (β i + shift * κ i - 1)) ≤
        M ^ n * (L ^ n * parameterHeightWeight H w.stateArity) *
          t ^ (w.angleArity + shift * w.stateArity - 1) :=
      mul_le_mul
        (mul_le_mul (pow_le_pow_right₀ hM c.length_le) hheight
          (Finset.prod_nonneg (fun i _ => parameterHeightWeight_nonneg hH _))
          (pow_nonneg hM0 _))
        (pow_le_pow_right₀ ht hcost) (pow_nonneg ht0 _)
        (mul_nonneg (pow_nonneg hM0 _) (mul_nonneg (pow_nonneg hL0 _) hHκ))
    exact (hprod.trans hupper).trans_eq (by rw [mul_pow]; ring)
  calc
    _ = ‖JK.D n x v‖ := congrArg norm heval
    _ ≤ C * ∑ c : OrderedFinpartition n,
        ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ :=
      smoothDirections_contDiff_comp_D_norm_le_of_outer_bound J hV hg hmap n x C houter v
    _ ≤ C * ∑ _c : OrderedFinpartition n,
        (M * L) ^ n * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity - 1) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hterm c)) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeInverse_contDiff_comp_sharp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeInverse_contDiff_comp_sharp_bound
