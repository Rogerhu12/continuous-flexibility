import ContinuousFlexibility.Analysis.N04NegativeGeometryLinearVariationBounds
import ContinuousFlexibility.Analysis.N01cFlowForcingEnvelope

/-!
# Spatial products with one retained forcing weight

The ordinary product rule keeps the sum of the spatial orders. A
distinguished factor then retains its entire amplitude, independently
of which factor receives a high derivative. This applies to the finite
products in the genuine state-variation forcing.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff BigOperators

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Every individual amplitude occurs once in the finite product.
The finite-order constant precedes the factors and their amplitudes. -/
theorem n04NegativeGeometry_weighted_finiteProduct_jet_le (L N : ℕ)
    (f : Fin L → Q → ℝ) (x : Q)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x)
    (A : Fin L → ℝ) (hA : ∀ i, 0 ≤ A i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbound : ∀ i j, j ≤ N → ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A i * ρ ^ j) :
    ∀ k, k ≤ N →
      ‖iteratedFDeriv ℝ k (fun y : Q => ∏ i, f i y) x‖ ≤
        ((2 : ℝ) ^ N) ^ L * (∏ i, A i) * ρ ^ k := by
  induction L with
  | zero =>
    intro k hk
    have he : (fun y : Q => ∏ i : Fin 0, f i y) = fun _ : Q => (1 : ℝ) := by
      funext y
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [he]
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero, norm_one, pow_zero,
        Finset.univ_eq_empty, Finset.prod_empty, one_mul, le_refl]
    | succ k =>
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, pow_zero,
        Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      exact pow_nonneg hρ _
  | succ L ih =>
    intro k hk
    let g : Q → ℝ := fun y => ∏ i : Fin L, f i.succ y
    have hg : ContDiffAt ℝ ∞ g x := contDiffAt_prod (fun i _ => hf i.succ)
    have htail (j : ℕ) (hj : j ≤ N) :
        ‖iteratedFDeriv ℝ j g x‖ ≤
          ((2 : ℝ) ^ N) ^ L * (∏ i : Fin L, A i.succ) * ρ ^ j :=
      ih (fun i => f i.succ) (fun i => hf i.succ)
        (fun i => A i.succ) (fun i => hA i.succ)
        (fun i j hj => hbound i.succ j hj) j hj
    have htail0 : 0 ≤ ((2 : ℝ) ^ N) ^ L * (∏ i : Fin L, A i.succ) :=
      mul_nonneg (pow_nonneg (pow_nonneg (by norm_num) N) L)
        (Finset.prod_nonneg fun i _ => hA i.succ)
    have hb := n04NegativeGeometry_weighted_product_jet_le (hf 0) hg
      (hA 0) htail0 hρ hk
      (fun j hj => hbound 0 j (hj.trans hk))
      (fun j hj => htail j (hj.trans hk))
    have he : (fun y : Q => ∏ i : Fin (L + 1), f i y) = fun y => f 0 y * g y := by
      funext y
      exact Fin.prod_univ_succ (fun i => f i y)
    rw [he]
    refine hb.trans_eq ?_
    rw [Fin.prod_univ_succ, pow_succ]
    ring

/-- An arbitrary marked amplitude survives once. The other factors
are charged only to their common polynomial envelope. -/
theorem n04NegativeGeometry_marked_finiteProduct_jet_le
    (L N : ℕ) (i₀ : Fin L) (f : Fin L → Q → ℝ) (x : Q)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x)
    {W M ρ : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hmarked : ∀ j, j ≤ N → ‖iteratedFDeriv ℝ j (f i₀) x‖ ≤ W * M * ρ ^ j)
    (hother : ∀ i, i ≠ i₀ → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ M * ρ ^ j) :
    ∀ k, k ≤ N →
      ‖iteratedFDeriv ℝ k (fun y : Q => ∏ i, f i y) x‖ ≤
        ((2 : ℝ) ^ N) ^ L * W * M ^ L * ρ ^ k := by
  classical
  let A : Fin L → ℝ := fun i => if i = i₀ then W * M else M
  have hA (i : Fin L) : 0 ≤ A i := by
    by_cases hi : i = i₀
    · simpa only [A, if_pos hi] using mul_nonneg hW hM
    · simpa only [A, if_neg hi] using hM
  have hb (i : Fin L) (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A i * ρ ^ j := by
    by_cases hi : i = i₀
    · subst i
      simpa only [A, if_pos rfl] using hmarked j hj
    · simpa only [A, if_neg hi] using hother i hi j hj
  have hprod : (∏ i, A i) ≤ W * M ^ L := by
    have hp := n01c_prod_le_marked_factor Finset.univ i₀ (Finset.mem_univ i₀) A
      (fun i _ => hA i) hW hM
      (by simp only [A, if_pos rfl, le_refl])
      (fun i _ hi => by simp only [A, if_neg hi, le_refl])
    simpa only [Finset.card_univ, Fintype.card_fin] using hp
  intro k hk
  calc
    _ ≤ ((2 : ℝ) ^ N) ^ L * (∏ i, A i) * ρ ^ k :=
      n04NegativeGeometry_weighted_finiteProduct_jet_le L N f x hf A hA hρ hb k hk
    _ ≤ ((2 : ℝ) ^ N) ^ L * (W * M ^ L) * ρ ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (pow_nonneg (pow_nonneg (by norm_num) N) L))
        (pow_nonneg hρ k)
    _ = _ := by ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_marked_finiteProduct_jet_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_marked_finiteProduct_jet_le
