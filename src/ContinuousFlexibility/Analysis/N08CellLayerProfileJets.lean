module

public import ContinuousFlexibility.Analysis.N08CellLayerTest
public import ContinuousFlexibility.Analysis.N08LayerCutoffJets

/-! # Uniform ordinary jets and exact support of the radial cell tests -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

theorem n08_iteratedDeriv_tsupport (f : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, subset_refl]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem n08CellLayerProfile_tsupport (D : ReferenceData) (A : ℝ) (m : ℕ) :
    tsupport (n08CellLayerProfile D A m) ⊆ tsupport (n08CellLayerCutoff D A m) := by
  apply closure_mono
  intro r hr
  exact right_ne_zero_of_mul hr

theorem n08CellLayerProfile_jet_zero {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m s : ℕ) {r : ℝ}
    (hr : r ∉ Analysis.intervalEndpointLayer D.a D.b
      (n08CellLayerInner A (D.cellIndex m)) (n08CellLayerOuter A (D.cellIndex m))) :
    iteratedDeriv s (n08CellLayerProfile D A m) r = 0 := by
  by_contra hn
  exact hr (n08CellLayerCutoff_tsupport hA m
    (n08CellLayerProfile_tsupport D A m
      (n08_iteratedDeriv_tsupport _ s (subset_closure hn))))

theorem n08CellLayerProfile_jet_bound (D : ReferenceData) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 1 ≤ A → ∀ m r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08CellLayerProfile D A m) r| ≤
        K * (n08CellLayerInner A (D.cellIndex m))⁻¹ ^ (4 * s) := by
  choose K hK hKb using fun j : Fin (s + 1) => n08_intervalLayerCutoff_jet_bound j.val
  let P : ℝ := ∑ j, K j
  let B : ℝ := |D.a| + |D.b| + 1
  have hP : 0 ≤ P := Finset.sum_nonneg (fun j _ => hK j)
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [abs_nonneg D.a, abs_nonneg D.b]
  refine ⟨(2 : ℝ) ^ s * B * P, by positivity, fun A hA m r hr => ?_⟩
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let δ : ℝ := n08CellLayerInner A (D.cellIndex m)
  have hδ : 0 < δ := n08CellLayerInner_pos hA0 _
  have hδ1 : δ ≤ 1 := n08CellLayerInner_le_one hA _
  have hR : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hδΔ : δ ≤ n08CellLayerOuter A (D.cellIndex m) := n08CellLayerInner_le_outer hA _
  have hid (j : ℕ) (_ : j ≤ s) : |iteratedDeriv j (fun t : ℝ => t) r| ≤ B := by
    rw [iteratedDeriv_fun_id]
    split_ifs
    · apply abs_le.mpr
      constructor <;> dsimp only [B] <;>
        linarith only [hr.1, hr.2, neg_abs_le D.a, le_abs_self D.b,
          abs_nonneg D.a, abs_nonneg D.b]
    · simpa only [abs_one] using hB
    · simpa only [abs_zero] using zero_le_one.trans hB
  have hcut (j : ℕ) (hj : j ≤ s) :
      |iteratedDeriv j (n08CellLayerCutoff D A m) r| ≤ P * δ⁻¹ ^ (4 * s) := by
    let k : Fin (s + 1) := ⟨j, by omega⟩
    have hk : K k ≤ P := Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ k)
    exact (hKb k D.a D.b δ (n08CellLayerOuter A (D.cellIndex m)) hδ hδ1 hδΔ r).trans
      (mul_le_mul hk (pow_le_pow_right₀ hR (Nat.mul_le_mul_left 4 hj))
        (pow_nonneg (inv_nonneg.mpr hδ.le) _) hP)
  have h := n08_jetPrefix_mul_bound (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
    (n08CellLayerCutoff_contDiff D A m) (zero_le_one.trans hB)
    (mul_nonneg hP (pow_nonneg (inv_nonneg.mpr hδ.le) _)) hid hcut s le_rfl
  exact h.trans_eq (by ring)

end ContinuousFlexibility.Statements
