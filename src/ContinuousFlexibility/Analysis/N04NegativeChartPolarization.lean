import ContinuousFlexibility.Analysis.MixedDiagonalOneHighBounds

/-! Polarization retains simultaneous low and high seminorm budgets. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

/-- Polarization on the intersection of two seminorm balls only costs
a constant depending on the parameter arity. -/
theorem n04NegativeChart_twoBall_polarization (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : Type*) [AddCommGroup E] [Module ℝ E]
      (p q : Seminorm ℝ E) (A : MultilinearMap ℝ (fun _ : Fin n => E) ℝ),
      (∀ v (σ : Equiv.Perm (Fin n)), A (v ∘ σ) = A v) →
      ∀ C R : ℝ, 0 ≤ C → 0 < R →
      (∀ w, p w ≤ 1 → q w ≤ R → |A (fun _ => w)| ≤ C) →
      ∀ v : Fin n → E, (∀ i, p (v i) ≤ 1) → (∀ i, q (v i) ≤ R) → |A v| ≤ K * C := by
  obtain ⟨K, hK, hb⟩ := exists_symmetric_multilinear_diagonal_affine_bound n
  refine ⟨(2 : ℝ) ^ n * K, mul_nonneg (by positivity) hK, ?_⟩
  intro E _ _ p q A hsym C R hC hR hdiag v hv hvq
  let r : Seminorm ℝ E := p + q.comp (R⁻¹ • LinearMap.id)
  have hr (w : E) : r w = p w + R⁻¹ * q w := by
    simp only [r, add_apply, Seminorm.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have hunit (i : Fin n) : r ((1 / 2 : ℝ) • v i) ≤ 1 := by
    rw [map_smul_eq_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hr]
    have hq := (mul_le_mul_of_nonneg_left (hvq i) (inv_nonneg.mpr hR.le)).trans_eq
      (inv_mul_cancel₀ hR.ne')
    linarith only [hv i, hq]
  have hbound := hb E r 0 A hsym 0 C hC (fun w hw => by
    have hp : p w ≤ 1 := (le_add_of_nonneg_right
      (mul_nonneg (inv_nonneg.mpr hR.le) (apply_nonneg q w))).trans ((hr w) ▸ hw)
    have hqw : R⁻¹ * q w ≤ 1 := (le_add_of_nonneg_left (apply_nonneg p w)).trans ((hr w) ▸ hw)
    have hqw' : q w ≤ R := by
      have hh := mul_le_mul_of_nonneg_left hqw hR.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_one] using hh
    simpa only [zero_apply, add_zero, mul_one] using hdiag w hp hqw')
    (fun i => (1 / 2 : ℝ) • v i) hunit
  have hb' : |A (fun i => (1 / 2 : ℝ) • v i)| ≤ K * C := by
    simpa only [zero_apply, Finset.sum_const_zero, add_zero, mul_one] using hbound
  have hscale : A (fun i => (1 / 2 : ℝ) • v i) = (1 / 2 : ℝ) ^ n * A v := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      A.map_smul_univ (fun _ => (1 / 2 : ℝ)) v
  have heq : A v = (2 : ℝ) ^ n * A (fun i => (1 / 2 : ℝ) • v i) := by
    rw [hscale, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    |A v| = (2 : ℝ) ^ n * |A (fun i => (1 / 2 : ℝ) • v i)| := by
      rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ n)]
    _ ≤ (2 : ℝ) ^ n * (K * C) := mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_twoBall_polarization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_twoBall_polarization
