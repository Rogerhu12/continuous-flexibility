import ContinuousFlexibility.Analysis.SpacesInterpolationProducts
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Repeated low base factors in a tame product estimate

The base factors all have the same low and high bounds. Bounding their low
norm on a fixed neighborhood leaves one high base norm or one high
direction norm. The product identities also apply when some low direction
norm is zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

private theorem spaces_prod_erase_eq_prod_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (i : ι) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j, Function.update f i 1 j := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    Finset.sdiff_singleton_eq_erase]

/-- Repeated copies of the base can be absorbed into the neighborhood
constant, while keeping precisely one high factor in each summand. -/
theorem spaces_repeated_low_factors_bound (q k : ℕ) (lu hu R : ℝ) (lv hv : Fin k → ℝ)
    (hR : 1 ≤ R) (hlu : 0 ≤ lu) (hluR : lu ≤ R) (hhu : 0 ≤ hu)
    (hlv : ∀ i, 0 ≤ lv i) (hhv : ∀ i, 0 ≤ hv i) :
    (∑ i : Fin q ⊕ Fin k,
      Sum.elim (fun _ : Fin q => hu) hv i *
        ∏ j ∈ Finset.univ.erase i, Sum.elim (fun _ : Fin q => lu) lv j) ≤
      ((q : ℝ) + 1) * R ^ q *
        ((1 + hu) * (∏ i, lv i) + ∑ i, hv i * ∏ j ∈ Finset.univ.erase i, lv j) := by
  classical
  let low : Fin q ⊕ Fin k → ℝ := Sum.elim (fun _ => lu) lv
  let V : ℝ := ∏ i, lv i
  let W : ℝ := ∑ i, hv i * ∏ j ∈ Finset.univ.erase i, lv j
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hV : 0 ≤ V := Finset.prod_nonneg (fun i _ => hlv i)
  have hW : 0 ≤ W :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hhv i)
      (Finset.prod_nonneg (fun j _ => hlv j)))
  have hleft (i : Fin q) :
      (∏ j ∈ Finset.univ.erase (Sum.inl i : Fin q ⊕ Fin k), low j) ≤ R ^ q * V := by
    have he : (∏ j ∈ Finset.univ.erase (Sum.inl i : Fin q ⊕ Fin k), low j) =
        (∏ j : Fin q, if j = i then (1 : ℝ) else lu) * V := by
      rw [spaces_prod_erase_eq_prod_update, Fintype.prod_sum_type]
      simp [Function.update_apply, low, V]
    have hb : (∏ j : Fin q, if j = i then (1 : ℝ) else lu) ≤ R ^ q := by
      calc
        (∏ j : Fin q, if j = i then (1 : ℝ) else lu) ≤ ∏ _j : Fin q, R := by
          apply Finset.prod_le_prod₀
          · intro j _
            split_ifs <;> positivity
          · intro j _
            split_ifs <;> assumption
        _ = R ^ q := by simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hb hV
  have hright (i : Fin k) :
      (∏ j ∈ Finset.univ.erase (Sum.inr i : Fin q ⊕ Fin k), low j) ≤
        R ^ q * ∏ j ∈ Finset.univ.erase i, lv j := by
    have he : (∏ j ∈ Finset.univ.erase (Sum.inr i : Fin q ⊕ Fin k), low j) =
        lu ^ q * ∏ j ∈ Finset.univ.erase i, lv j := by
      rw [spaces_prod_erase_eq_prod_update, spaces_prod_erase_eq_prod_update,
        Fintype.prod_sum_type]
      simp [Function.update_apply, low]
    rw [he]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlu hluR q)
      (Finset.prod_nonneg (fun j _ => hlv j))
  have hsleft : (∑ _i : Fin q, hu * (R ^ q * V)) = (q : ℝ) * hu * R ^ q * V := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsright :
      (∑ i : Fin k, hv i * (R ^ q * ∏ j ∈ Finset.univ.erase i, lv j)) = R ^ q * W := by
    dsimp only [W]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ i : Fin q ⊕ Fin k, Sum.elim (fun _ : Fin q => hu) hv i *
    ∏ j ∈ Finset.univ.erase i, low j) ≤ ((q : ℝ) + 1) * R ^ q * ((1 + hu) * V + W)
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  calc
    (∑ i : Fin q, hu * ∏ j ∈ Finset.univ.erase (Sum.inl i : Fin q ⊕ Fin k), low j) +
        (∑ i : Fin k, hv i * ∏ j ∈ Finset.univ.erase (Sum.inr i : Fin q ⊕ Fin k), low j) ≤
        (∑ _i : Fin q, hu * (R ^ q * V)) +
          (∑ i : Fin k, hv i * (R ^ q * ∏ j ∈ Finset.univ.erase i, lv j)) :=
      add_le_add
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hleft i) hhu))
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hright i) (hhv i)))
    _ = (q : ℝ) * hu * R ^ q * V + R ^ q * W := by rw [hsleft, hsright]
    _ ≤ (q : ℝ) * hu * R ^ q * V + R ^ q * W +
        R ^ q * (((q : ℝ) + 1 + hu) * V + (q : ℝ) * W) :=
      le_add_of_nonneg_right (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
