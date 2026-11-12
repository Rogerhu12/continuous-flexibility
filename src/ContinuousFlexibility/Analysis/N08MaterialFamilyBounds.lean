import ContinuousFlexibility.Scalar.WeightedMaterialRadiusJets

/-!
# Material-coordinate bounds for a uniformly controlled family

The actual radius has bounded jets of every order. Composing with it
preserves an arbitrary pointwise majorant, uniformly over the family index.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

theorem n08_comp_materialRadius_majorant
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {I : Type*} {f : I → ℝ → ℝ} {N : I → ℝ} {W : ℝ → ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo D.a D.b))
    (hN : ∀ i, 0 ≤ N i) (hW : ∀ r ∈ Ioo D.a D.b, 0 ≤ W r)
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv n (f i) r| ≤ C * N i * W r) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      |iteratedDeriv n (fun t => f i (T.radius t)) x| ≤ C * N i * W (T.radius x) := by
  classical
  have hradius := hT.2.2.2.2.2.2.1
  have hinside := hT.2.2.2.2.2.2.2.1
  have houter (j : Fin (n + 1)) := hb j.val
  have hinner (j : Fin (n + 1)) := iteratedDeriv_materialRadius_bounded hT j.val
  choose A hA hAb using houter
  choose B hB hBb using hinner
  let K : ℝ := ∑ j : Fin (n + 1), A j
  let L : ℝ := 1 + ∑ j : Fin (n + 1), B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hA j)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith only [Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hB j)]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLpow (j : ℕ) (hj : 1 ≤ j) : L ≤ L ^ j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    calc
      L = 1 * L := (one_mul _).symm
      _ ≤ L ^ k * L := mul_le_mul_of_nonneg_right (one_le_pow₀ hL) hL0
      _ = L ^ (k + 1) := (pow_succ _ _).symm
  refine ⟨(n.factorial : ℝ) * K * L ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) (pow_nonneg hL0 _), ?_⟩
  intro i x
  have hr := (hinside x).1
  have hout (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDerivWithin ℝ j (f i) (Ioo D.a D.b) (T.radius x)‖ ≤
        K * N i * W (T.radius x) := by
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioo hr, Real.norm_eq_abs]
    let k : Fin (n + 1) := ⟨j, by omega⟩
    exact (hAb k i _ hr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ k)) (hN i)) (hW _ hr))
  have hin (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      ‖iteratedFDeriv ℝ j T.radius x‖ ≤ L ^ j := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    let k : Fin (n + 1) := ⟨j, by omega⟩
    have hk : B k ≤ L := by
      have hs := Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ k)
      dsimp only [L]
      linarith only [hs]
    exact (hBb k x).trans (hk.trans (hLpow j hj))
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := f i) (f := T.radius) (n := n)
    (t := Ioo D.a D.b) (by
      rintro r ⟨x, rfl⟩
      exact (hinside x).1) isOpen_Ioo.uniqueDiffOn (hf i) hradius (by simp) x hout hin
  have hfinal : |iteratedDeriv n (fun t => f i (T.radius t)) x| ≤
      (n.factorial : ℝ) * (K * N i * W (T.radius x)) * L ^ n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Function.comp_def] using hcomp
  exact hfinal.trans_eq (by ring)

end ContinuousFlexibility.Statements
