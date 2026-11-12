import ContinuousFlexibility.Analysis.SpacesInterpolationProducts
import ContinuousFlexibility.Analysis.TameTopologicalComposition
import ContinuousFlexibility.Analysis.TameMultilinearNormalization
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Ordered-partition composition with one fixed low base

The public finite-product interpolation theorem is applied to the original
inputs. Parameter-order losses are assigned differential orders in that
product. They never become additional low-neighborhood hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

/-- The base and loss precede both finite arities and every assigned order. -/
theorem spaces_interpolation_affine_product_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (hI : HasInterpolation (pairGrading realGrading p)) :
    ∃ B L : ℕ, ∀ k m : ℕ, ∀ order : Fin m → ℕ, ∀ s : ℕ,
      (∑ j, order j) ≤ s → ∀ R : ℝ, 0 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin (k + 1) → E,
        (∀ i, p B (x i) ≤ R) →
        (∏ j, (1 + ∑ i, p (order j) (x i))) ≤
          C * (1 + ∑ i, p (s + L) (x i)) := by
  classical
  let q := pairGrading realGrading p
  have hq : Monotone q := tamePairGrading_monotone (fun _ _ _ _ => le_rfl) hp
  have hqone (t : ℕ) (x : E) : q t (1, x) = 1 + p t x := by
    simp only [q, pairGrading_apply, realGrading, coe_normSeminorm, norm_one]
  obtain ⟨B, L, hprod⟩ := spaces_interpolation_product_bound q (fun x _ _ h => hq h x) hI
  refine ⟨B, L, fun k m order s hs R hR => ?_⟩
  cases m with
  | zero =>
      refine ⟨1, zero_le_one, fun x _ => ?_⟩
      simp only [Fin.prod_univ_zero, one_mul]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  | succ m =>
      obtain ⟨A, hA, ha⟩ := hprod order s hs
      let M : ℝ := (k + 1 : ℕ)
      refine ⟨M ^ (m + 1) * A * (m + 1 : ℕ) * (1 + R) ^ (m + 1),
        by dsimp [M]; positivity, fun x hx => ?_⟩
      have hmax (j : Fin (m + 1)) : ∃ i : Fin (k + 1),
          ∀ l : Fin (k + 1), q (order j) (1, x l) ≤ q (order j) (1, x i) := by
        obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image
          (fun l : Fin (k + 1) => q (order j) (1, x l)) Finset.univ_nonempty
        exact ⟨i, fun l => hi l (Finset.mem_univ l)⟩
      choose pick hpick using hmax
      let P : ℝ := 1 + ∑ i, p (s + L) (x i)
      have hP : 0 ≤ P := by dsimp [P]; positivity
      have hfactor (j : Fin (m + 1)) :
          1 + ∑ i, p (order j) (x i) ≤ M * q (order j + 2) (1, x (pick j)) := by
        calc
          _ ≤ ∑ i : Fin (k + 1), q (order j) (1, x i) := by
            simp only [hqone, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            exact add_le_add_right (by exact_mod_cast Nat.succ_pos k) _
          _ ≤ ∑ _i : Fin (k + 1), q (order j + 2) (1, x (pick j)) :=
            Finset.sum_le_sum (fun i _ => (hpick j i).trans (hq (by omega) _))
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, M]
      have hlow (j : Fin (m + 1)) : q B (1, x (pick j)) ≤ 1 + R := by
        rw [hqone]; exact add_le_add_left (hx _) 1
      have hhigh (j : Fin (m + 1)) : q (s + L) (1, x (pick j)) ≤ P := by
        rw [hqone]
        exact add_le_add_left (Finset.single_le_sum (fun _ _ => apply_nonneg _ _)
          (Finset.mem_univ (pick j))) 1
      have herase (j : Fin (m + 1)) :
          (∏ l ∈ Finset.univ.erase j, q B (1, x (pick l))) ≤ (1 + R) ^ (m + 1) := by
        calc
          _ ≤ ∏ _l ∈ Finset.univ.erase j, (1 + R) :=
            Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun l _ => hlow l)
          _ ≤ ∏ _l : Fin (m + 1), (1 + R) :=
            Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset _ _)
              (fun _ _ => by positivity) (fun _ _ _ => by linarith)
          _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hsum : (∑ j, q (s + L) (1, x (pick j)) *
          ∏ l ∈ Finset.univ.erase j, q B (1, x (pick l))) ≤
          (m + 1 : ℕ) * (P * (1 + R) ^ (m + 1)) := by
        calc
          _ ≤ ∑ _j : Fin (m + 1), P * (1 + R) ^ (m + 1) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul (hhigh j) (herase j)
              (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hP)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      calc
        _ ≤ ∏ j, M * q (order j + 2) (1, x (pick j)) :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hfactor j)
        _ = M ^ (m + 1) * ∏ j, q (order j + 2) (1, x (pick j)) := by
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ M ^ (m + 1) * (A * ((m + 1 : ℕ) * (P * (1 + R) ^ (m + 1)))) :=
          mul_le_mul_of_nonneg_left ((ha (fun j => (1, x (pick j)))).trans
            (mul_le_mul_of_nonneg_left hsum hA)) (by dsimp [M]; positivity)
        _ = _ := by dsimp only [P]; ring

private theorem tameJetSize_selected_unit_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B t L n m : ℕ) (x : E) (v : Fin n → E)
    (σ : Fin m → Fin n) (hv : ∀ i, p B (v i) ≤ 1) :
    tameJetSize p m t L B x (v ∘ σ) ≤
      (m + 1 : ℕ) * (1 + ∑ i, p (t + L) ((Fin.cons x v : Fin (n + 1) → E) i)) := by
  let P : ℝ := 1 + ∑ i, p (t + L) ((Fin.cons x v : Fin (n + 1) → E) i)
  have hslot (i : Fin (n + 1)) : p (t + L) ((Fin.cons x v : Fin (n + 1) → E) i) ≤ P :=
    (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hx : 1 + p (t + L) x ≤ P := by
    dsimp [P]
    rw [Fin.sum_univ_succ]
    exact add_le_add_left (le_add_of_nonneg_right
      (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))) 1
  have hs : (∑ j, p (t + L) (v (σ j))) ≤ (m : ℝ) * P := by
    calc
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hslot (Fin.succ (σ j)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  exact (multilinearTameSize_le_affine (p B) (p (t + L)) m
    (by positivity) (v ∘ σ) (fun i => hv (σ i))).trans
      ((add_le_add hx hs).trans_eq (by dsimp only [P]; push_cast; ring))

private theorem tameJetSize_uniform_slots
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (q : ℕ → Seminorm ℝ F) (n s L B : ℕ) (x : F) (v : Fin n → F)
    (A H : ℝ) (hA : 1 ≤ A) (hH : 1 ≤ H)
    (hx : q (s + L) x ≤ H) (hv : ∀ i, q (s + L) (v i) ≤ H)
    (hlow : ∀ i, q B (v i) ≤ A) :
    tameJetSize q n s L B x v ≤ ((n : ℝ) + 2) * H * A ^ n := by
  have hp (S : Finset (Fin n)) : (∏ i ∈ S, q B (v i)) ≤ A ^ n := by
    calc
      _ ≤ ∏ _i ∈ S, A := Finset.prod_le_prod₀
        (fun _ _ => apply_nonneg _ _) (fun i _ => hlow i)
      _ ≤ ∏ _i : Fin n, A := Finset.prod_le_prod_of_subset_of_one_le₀
        (Finset.subset_univ _) (fun _ _ => zero_le_one.trans hA) (fun _ _ _ => hA)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbase : 1 + q (s + L) x ≤ 2 * H := by linarith
  have hsum : (∑ i, q (s + L) (v i) * ∏ j ∈ Finset.univ.erase i, q B (v j)) ≤
      (n : ℝ) * (H * A ^ n) := by
    calc
      _ ≤ ∑ _i : Fin n, H * A ^ n := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hv i) (hp _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
          (zero_le_one.trans hH))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  exact (add_le_add (mul_le_mul hbase (hp _)
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (by linarith)) hsum).trans_eq (by ring)

end ContinuousFlexibility.Analysis
