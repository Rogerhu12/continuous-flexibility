module

public import ContinuousFlexibility.Analysis.N07aShiftedInterpolation
public import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# One high state or source factor in an arbitrary finite jet product

The fixed offset is absorbed by interpolation before any product is
estimated. The same low state neighborhood works for every number of
factors and every total order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

private theorem n07a_lowProduct_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 2) :
    (∏ i ∈ s, f i) ≤ (2 : ℝ) ^ Fintype.card ι := by
  calc
    _ ≤ ∏ _i ∈ s, (2 : ℝ) :=
      Finset.prod_le_prod₀ (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)
    _ ≤ ∏ _i : ι, (2 : ℝ) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ s)
        (by norm_num) (by norm_num)
    _ = _ := by simp

private theorem n07a_oneHighSum_bound {n : ℕ}
    (low high : Fin (n + 1) → ℝ) {f₀ f₁ z₁ : ℝ}
    (h0 : 0 ≤ f₀) (h1 : 0 ≤ f₁) (hz : 0 ≤ z₁)
    (hl0 : low 0 = f₀) (hh0 : high 0 = f₁)
    (hl : ∀ i, i ≠ 0 → 0 ≤ low i ∧ low i ≤ 2)
    (hh : ∀ i, i ≠ 0 → high i = z₁) :
    (∑ i, high i * ∏ j ∈ Finset.univ.erase i, low j) ≤
      ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * (f₁ + z₁ * f₀) := by
  have hterm (i : Fin (n + 1)) :
      high i * ∏ j ∈ Finset.univ.erase i, low j ≤
        2 ^ (n + 1) * (f₁ + z₁ * f₀) := by
    by_cases hi : i = 0
    · subst i
      rw [hh0]
      have hp := n07a_lowProduct_bound (Finset.univ.erase (0 : Fin (n + 1))) low
        (fun j hj => hl j (Finset.ne_of_mem_erase hj))
      simp only [Fintype.card_fin] at hp
      calc
        _ ≤ f₁ * 2 ^ (n + 1) := mul_le_mul_of_nonneg_left hp h1
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hz h0) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1))]
    · have hmem : (0 : Fin (n + 1)) ∈ Finset.univ.erase i := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact Ne.symm hi
      rw [hh i hi, ← Finset.mul_prod_erase (Finset.univ.erase i) low hmem, hl0]
      have hp := n07a_lowProduct_bound ((Finset.univ.erase i).erase 0) low
        (fun j hj => hl j (Finset.ne_of_mem_erase hj))
      simp only [Fintype.card_fin] at hp
      calc
        _ ≤ z₁ * (f₀ * 2 ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp h0) hz
        _ ≤ _ := by nlinarith [mul_nonneg h1 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1))]
  calc
    _ ≤ ∑ _i : Fin (n + 1), 2 ^ (n + 1) * (f₁ + z₁ * f₀) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

theorem n07a_finite_parameter_source_product
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasSmoothing p) (hIq : HasSmoothing q) (d : ℕ) :
    ∃ base loss : ℕ, ∀ (n : ℕ) (order : Fin n → ℕ) (t s : ℕ),
      t + (∑ i, order i) ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : E, p base z ≤ 1 → ∀ f : F,
          q (t + d) f * (∏ i, (1 + p (order i + d) z)) ≤
            C * (q (s + loss) f + (1 + p (s + loss) z) * q base f) := by
  classical
  let P : ℕ → Seminorm ℝ ((ℝ × E) × F) :=
    pairGrading (pairGrading realGrading p) q
  have hP : Monotone P :=
    tamePairGrading_monotone (tamePairGrading_monotone (fun _ _ _ => le_rfl) hp) hq
  have hPI : HasInterpolation P := hasInterpolation_of_hasSmoothing hP
    (hasSmoothing_pairGrading (hasSmoothing_pairGrading hasSmoothing_realGrading hIp) hIq)
  obtain ⟨base, loss, hb⟩ := n07a_interpolation_product_offset P hP hPI d
  refine ⟨base, loss, fun n order t s hs => ?_⟩
  let ord : Fin (n + 1) → ℕ := Fin.cases t order
  have hord : ∑ i, ord i ≤ s := by
    simpa only [Fin.sum_univ_succ, ord, Fin.cases_zero, Fin.cases_succ] using hs
  obtain ⟨C, hC, hCb⟩ := hb ord s hord
  refine ⟨C * (n + 1) * 2 ^ (n + 1), by positivity, fun z hz f => ?_⟩
  let x : Fin (n + 1) → (ℝ × E) × F :=
    Fin.cases ((0, 0), f) (fun _ => ((1, z), 0))
  have hsource (k : ℕ) : P k ((0, 0), f) = q k f := by
    simp only [P, pairGrading_apply]
    change ‖(0 : ℝ)‖ + p k 0 + q k f = q k f
    simp only [norm_zero, map_zero, zero_add]
  have hstate (k : ℕ) : P k ((1, z), (0 : F)) = 1 + p k z := by
    simp only [P, pairGrading_apply]
    change ‖(1 : ℝ)‖ + p k z + q k 0 = 1 + p k z
    simp only [norm_one, map_zero, add_zero]
  have he : (∏ i, P (ord i + d) (x i)) =
      q (t + d) f * (∏ i, (1 + p (order i + d) z)) := by
    simp only [Fin.prod_univ_succ, ord, x, Fin.cases_zero, Fin.cases_succ, hsource, hstate]
  have hlow (i : Fin (n + 1)) (hi : i ≠ 0) :
      0 ≤ P base (x i) ∧ P base (x i) ≤ 2 := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    simp only [x, Fin.cases_succ, hstate]
    exact ⟨add_nonneg zero_le_one (apply_nonneg _ _), by linarith⟩
  have hhigh (i : Fin (n + 1)) (hi : i ≠ 0) :
      P (s + loss) (x i) = 1 + p (s + loss) z := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    simp only [x, Fin.cases_succ, hstate]
  have hn := n07a_oneHighSum_bound
    (fun i => P base (x i)) (fun i => P (s + loss) (x i))
    (apply_nonneg (q base) f) (apply_nonneg (q (s + loss)) f)
    (add_nonneg zero_le_one (apply_nonneg _ _))
    (by simpa only [x, Fin.cases_zero] using hsource base)
    (by simpa only [x, Fin.cases_zero] using hsource (s + loss)) hlow hhigh
  rw [← he]
  exact (hCb x).trans ((mul_le_mul_of_nonneg_left hn hC).trans_eq (by push_cast; ring))

end ContinuousFlexibility.Analysis
