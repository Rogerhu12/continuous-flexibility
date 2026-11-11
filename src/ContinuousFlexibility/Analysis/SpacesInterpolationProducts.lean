import ContinuousFlexibility.Statements.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max

/-!
# One high factor from interpolation

A finite product of interpolation bounds has one high factor when the
interpolation exponents sum to at most one. The low base can absorb the
fixed interpolation and point-evaluation losses independently of the
number of differentiated factors.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

/-- A homogeneous finite-product inequality with exactly one high factor. -/
theorem spaces_prod_interpolation_one_high {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (hne : S.Nonempty)
    (low high θ : ι → ℝ)
    (hlow : ∀ i ∈ S, 0 ≤ low i) (hhigh : ∀ i ∈ S, low i ≤ high i)
    (hθ : ∀ i ∈ S, 0 ≤ θ i ∧ θ i < 1) (hsum : ∑ i ∈ S, θ i ≤ 1) :
    (∏ i ∈ S, (low i) ^ (1 - θ i) * (high i) ^ θ i) ≤
      ∑ i ∈ S, high i * ∏ j ∈ S.erase i, low j := by
  classical
  have hrhs : 0 ≤ ∑ i ∈ S, high i * ∏ j ∈ S.erase i, low j := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg ((hlow i hi).trans (hhigh i hi))
      (Finset.prod_nonneg (fun j hj => hlow j (Finset.mem_of_mem_erase hj)))
  by_cases hz : ∃ i ∈ S, low i = 0
  · obtain ⟨i, hi, he⟩ := hz
    have hp : ∏ j ∈ S, (low j) ^ (1 - θ j) * (high j) ^ θ j = 0 := by
      apply Finset.prod_eq_zero hi
      rw [he, Real.zero_rpow (by linarith [(hθ i hi).2] : 1 - θ i ≠ 0), zero_mul]
    rw [hp]
    exact hrhs
  have hlpos (i : ι) (hi : i ∈ S) : 0 < low i :=
    lt_of_le_of_ne (hlow i hi) (fun h => hz ⟨i, hi, h.symm⟩)
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image (fun i => high i / low i) hne
  let R : ℝ := high k / low k
  have hR : 1 ≤ R := (le_div_iff₀ (hlpos k hk)).mpr (by simpa using hhigh k hk)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hterm (i : ι) (hi : i ∈ S) :
      (low i) ^ (1 - θ i) * (high i) ^ θ i ≤ low i * R ^ θ i := by
    have hh : high i ≤ low i * R := by
      have h := (div_le_iff₀ (hlpos i hi)).mp (hmax i hi)
      simpa only [mul_comm] using h
    calc
      (low i) ^ (1 - θ i) * (high i) ^ θ i ≤
          (low i) ^ (1 - θ i) * (low i * R) ^ θ i :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow ((hlow i hi).trans (hhigh i hi)) hh (hθ i hi).1)
          (Real.rpow_nonneg (hlow i hi) _)
      _ = low i * R ^ θ i := by
        rw [Real.mul_rpow (hlow i hi) hRpos.le, ← mul_assoc,
          ← Real.rpow_add (hlpos i hi), sub_add_cancel, Real.rpow_one]
  calc
    (∏ i ∈ S, (low i) ^ (1 - θ i) * (high i) ^ θ i) ≤
        ∏ i ∈ S, low i * R ^ θ i :=
      Finset.prod_le_prod₀ (fun i hi => mul_nonneg (Real.rpow_nonneg (hlow i hi) _)
        (Real.rpow_nonneg ((hlow i hi).trans (hhigh i hi)) _)) hterm
    _ = (∏ i ∈ S, low i) * R ^ (∑ i ∈ S, θ i) := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hRpos]
    _ ≤ (∏ i ∈ S, low i) * R := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg hlow)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR hsum
    _ = high k * ∏ j ∈ S.erase k, low j := by
      rw [← Finset.mul_prod_erase S low hk]
      dsimp only [R]
      field_simp [(hlpos k hk).ne']
    _ ≤ ∑ i ∈ S, high i * ∏ j ∈ S.erase i, low j :=
      Finset.single_le_sum (f := fun i => high i * ∏ j ∈ S.erase i, low j)
        (fun i hi => mul_nonneg ((hlow i hi).trans (hhigh i hi))
        (Finset.prod_nonneg (fun j hj => hlow j (Finset.mem_of_mem_erase hj)))) hk

/-- A fixed low base absorbs both the interpolation loss and the two
orders used in point evaluation, regardless of the number of factors. -/
theorem spaces_interpolation_product_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : ∀ x, Monotone (fun n => p n x))
    (hI : Statements.HasInterpolation p) :
    ∃ base loss : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      ∀ (order : ι → ℕ) (s : ℕ), (∑ i, order i) ≤ s →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → E,
          (∏ i, p (order i + 2) (x i)) ≤ C *
            ∑ i, p (s + loss) (x i) * ∏ j ∈ Finset.univ.erase i, p base (x j) := by
  classical
  obtain ⟨base₀, ell, hI⟩ := hI
  let B := base₀ + ell + 2
  let loss := B + ell + 3
  refine ⟨B, loss, ?_⟩
  intro ι _ _ _ order s hs
  let H := s + loss
  let d : ℝ := (H : ℝ) - B
  have hBH : B ≤ H := by dsimp [H, loss]; omega
  have hd : d = (s : ℝ) + ell + 3 := by dsimp [d, H, loss]; push_cast; ring
  have hdpos : 0 < d := by rw [hd]; positivity
  have hBs : (ell : ℝ) + 2 ≤ B := by dsimp [B]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) base₀]
  have hi (i : ι) : order i ≤ s :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs
  let θ (i : ι) : ℝ := if order i + 2 ≤ B then 0 else
    ((order i : ℝ) + 2 - B + ell) / d
  have hθ (i : ι) : 0 ≤ θ i ∧ θ i < 1 := by
    by_cases h : order i + 2 ≤ B
    · simp only [θ, ite_eq_left h]
      norm_num
    · have h' : (B : ℝ) < (order i : ℝ) + 2 := by exact_mod_cast Nat.lt_of_not_ge h
      have his : (order i : ℝ) ≤ s := by exact_mod_cast hi i
      simp only [θ, ite_eq_right h]
      constructor
      · exact div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ell]) hdpos.le
      · apply (div_lt_one hdpos).mpr
        rw [hd]
        linarith [Nat.cast_nonneg (α := ℝ) B]
  have hθorder (i : ι) : θ i ≤ (order i : ℝ) / d := by
    by_cases h : order i + 2 ≤ B
    · simp only [θ, ite_eq_left h]
      positivity
    · simp only [θ, ite_eq_right h]
      exact div_le_div_of_nonneg_right (by linarith) hdpos.le
  have hθsum : ∑ i, θ i ≤ 1 := by
    calc
      (∑ i, θ i) ≤ ∑ i, (order i : ℝ) / d := Finset.sum_le_sum (fun i _ => hθorder i)
      _ = (∑ i, (order i : ℝ)) / d := (Finset.sum_div _ _ _).symm
      _ ≤ (s : ℝ) / d := div_le_div_of_nonneg_right (by exact_mod_cast hs) hdpos.le
      _ ≤ 1 := (div_le_one hdpos).mpr (by rw [hd]; linarith [Nat.cast_nonneg (α := ℝ) ell])
  have hb (i : ι) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      p (order i + 2) x ≤ C * (p B x) ^ (1 - θ i) * (p H x) ^ θ i := by
    by_cases h : order i + 2 ≤ B
    · refine ⟨1, zero_le_one, fun x => ?_⟩
      simpa only [θ, ite_eq_left h, sub_zero, Real.rpow_one, Real.rpow_zero, one_mul, mul_one]
        using hp x h
    · have hB₀ : base₀ ≤ B := by dsimp [B]; omega
      have htop : order i + 2 + ell < H := by dsimp [H, loss, B]; have := hi i; omega
      obtain ⟨C, hC, hbound⟩ := hI B (order i + 2) H hB₀ (Nat.lt_of_not_ge h) htop
      refine ⟨C, hC, fun x => ?_⟩
      have hlow : 1 - θ i = ((H : ℝ) - (order i + 2 : ℕ) - ell) / ((H : ℝ) - B) := by
        simp only [θ, ite_eq_right h]
        change 1 - ((order i : ℝ) + 2 - B + ell) / d =
          ((H : ℝ) - (order i + 2 : ℕ) - ell) / d
        push_cast
        field_simp
        dsimp [d]
        ring
      rw [hlow]
      simpa only [θ, ite_eq_right h, d, Nat.cast_add, Nat.cast_ofNat] using hbound x
  choose C hC hbound using hb
  refine ⟨∏ i, C i, Finset.prod_nonneg (fun i _ => hC i), fun x => ?_⟩
  have hprod := spaces_prod_interpolation_one_high Finset.univ Finset.univ_nonempty
    (fun i => p B (x i)) (fun i => p H (x i)) θ
    (fun i _ => apply_nonneg (p B) (x i)) (fun i _ => hp (x i) hBH)
    (fun i _ => hθ i) hθsum
  calc
    (∏ i, p (order i + 2) (x i)) ≤
        ∏ i, C i * ((p B (x i)) ^ (1 - θ i) * (p H (x i)) ^ θ i) := by
      apply Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _)
      intro i _
      simpa only [mul_assoc] using hbound i (x i)
    _ = (∏ i, C i) * ∏ i, (p B (x i)) ^ (1 - θ i) * (p H (x i)) ^ θ i :=
      Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Finset.prod_nonneg (fun i _ => hC i))

/-- The bilinear specialization retains a fixed loss and one high factor. -/
theorem spaces_interpolation_pair_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : ∀ x, Monotone (fun n => p n x))
    (hI : Statements.HasInterpolation p) :
    ∃ base loss : ℕ, ∀ a b s : ℕ, a + b ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E,
      p (a + 2) x * p (b + 2) y ≤ C *
        (p (s + loss) x * p base y + p base x * p (s + loss) y) := by
  obtain ⟨base, loss, h⟩ := spaces_interpolation_product_bound p hp hI
  refine ⟨base, loss, fun a b s hs => ?_⟩
  obtain ⟨C, hC, hb⟩ := h (ι := Fin 2) ![a, b] s (by simpa using hs)
  refine ⟨C, hC, fun x y => ?_⟩
  have he : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  simpa [Fin.prod_univ_two, Fin.sum_univ_two, Finset.univ_fin2, he, mul_comm] using hb ![x, y]

/-- A single constant controls all splittings of a fixed total order. -/
theorem spaces_interpolation_pair_uniform_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : ∀ x, Monotone (fun n => p n x))
    (hI : Statements.HasInterpolation p) :
    ∃ base loss : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ x y : E,
        p (a + 2) x * p (b + 2) y ≤ C *
          (p (s + loss) x * p base y + p base x * p (s + loss) y) := by
  classical
  obtain ⟨base, loss, h⟩ := spaces_interpolation_pair_bound p hp hI
  refine ⟨base, loss, fun s => ?_⟩
  have hb (a b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E, a + b ≤ s →
      p (a + 2) x * p (b + 2) y ≤ C *
        (p (s + loss) x * p base y + p base x * p (s + loss) y) := by
    by_cases hab : a + b ≤ s
    · obtain ⟨C, hC, hbound⟩ := h a b s hab
      exact ⟨C, hC, fun x y _ => hbound x y⟩
    · exact ⟨0, le_rfl, fun _ _ hs => (hab hs).elim⟩
  choose C hC hbound using hb
  refine ⟨∑ a ∈ Finset.range (s + 1), ∑ b ∈ Finset.range (s + 1), C a b,
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hC a b)), ?_⟩
  intro a b hab x y
  have ha : a ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
  have hb : b ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
  have hle : C a b ≤ ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1), C i j :=
    (Finset.single_le_sum (f := C a) (fun j _ => hC a j) hb).trans
      (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (s + 1), C i j)
        (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)) ha)
  exact (hbound a b x y hab).trans (mul_le_mul_of_nonneg_right hle
    (add_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))))

end ContinuousFlexibility.Analysis
