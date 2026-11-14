import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Fixed low-order bounds under the endpoint's linear parameter maps

The endpoint circle operations use a linear map from sector parameters
to one or two circle entries. A uniform seminorm bound for that map
preserves the one-high expression with the same low order and loss.
Only a numerical factor depending on the parameter order is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

/-- A map bounded by a fixed scalar in every grading preserves the
actual one-high expression. No new low order is chosen. -/
theorem n04PositiveGeometry_endpointBounds_linearImage
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (L : E → F) {A : ℝ} (hA : 1 ≤ A)
    (hL : ∀ s x, q s (L x) ≤ A * p s x)
    (k s loss base : ℕ) (x : E) (v : Fin k → E) :
    tameJetSize q k s loss base (L x) (fun i => L (v i)) ≤
      A ^ (k + 1) * tameJetSize p k s loss base x v := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hprod (I : Finset (Fin k)) :
      (∏ i ∈ I, q base (L (v i))) ≤ A ^ k * ∏ i ∈ I, p base (v i) := by
    have hcard : I.card ≤ k := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I)
    calc
      _ ≤ ∏ i ∈ I, A * p base (v i) :=
        Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun i _ => hL base (v i))
      _ = A ^ I.card * ∏ i ∈ I, p base (v i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ A ^ k * ∏ i ∈ I, p base (v i) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hcard)
          (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  have hstate : 1 + q (s + loss) (L x) ≤ A * (1 + p (s + loss) x) := by
    have h := hL (s + loss) x
    nlinarith only [h, hA]
  have hhead : (1 + q (s + loss) (L x)) * ∏ i, q base (L (v i)) ≤
      A ^ (k + 1) * ((1 + p (s + loss) x) * ∏ i, p base (v i)) := by
    calc
      _ ≤ (A * (1 + p (s + loss) x)) * (A ^ k * ∏ i, p base (v i)) :=
        mul_le_mul hstate (hprod Finset.univ)
          (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
          (mul_nonneg hA0 (add_nonneg zero_le_one (apply_nonneg _ _)))
      _ = _ := by rw [pow_succ]; ring
  have hslot (i : Fin k) :
      q (s + loss) (L (v i)) * ∏ j ∈ Finset.univ.erase i, q base (L (v j)) ≤
      A ^ (k + 1) * (p (s + loss) (v i) *
        ∏ j ∈ Finset.univ.erase i, p base (v j)) := by
    calc
      _ ≤ (A * p (s + loss) (v i)) *
          (A ^ k * ∏ j ∈ Finset.univ.erase i, p base (v j)) :=
        mul_le_mul (hL (s + loss) (v i)) (hprod (Finset.univ.erase i))
          (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
          (mul_nonneg hA0 (apply_nonneg _ _))
      _ = _ := by rw [pow_succ]; ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hslot i)
  exact (add_le_add hhead hsum).trans_eq (by
    rw [← Finset.mul_sum, ← mul_add]
    rfl)

end ContinuousFlexibility.Analysis
