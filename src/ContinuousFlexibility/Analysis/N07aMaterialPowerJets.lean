import ContinuousFlexibility.Scalar.WeightedMaterialScale

/-!
# Actual material-envelope powers retain their power under differentiation

The positive-order logarithmic jets of M are bounded in the material
coordinate. Exponentiation therefore preserves the chosen power of M in
every derivative, including negative powers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData}

theorem n07a_materialM_rpow_contDiff (hT : IsMaterialData D T) (q : ℝ) :
    ContDiff ℝ ∞ (fun x => T.M (T.radius x) ^ q) := by
  have hs := hT.1 T.M (by simp)
  have hp : ∀ r ∈ Ioo D.a D.b, 0 < T.M r :=
    fun r hr => zero_lt_one.trans_le (hT.2.1 r hr).2.2.2
  exact (hs.rpow_const_of_ne (fun r hr => (hp r hr).ne')).comp_contDiff
    hT.2.2.2.2.2.2.1 (fun x => (hT.2.2.2.2.2.2.2.1 x).1)

theorem n07a_iteratedDeriv_materialM_rpow_bound
    (hT : IsMaterialData D T) (q : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => T.M (T.radius t) ^ q) x| ≤
        C * T.M (T.radius x) ^ q := by
  have hp : ∀ r ∈ Ioo D.a D.b, 0 < T.M r :=
    fun r hr => zero_lt_one.trans_le (hT.2.1 r hr).2.2.2
  let L : ℝ → ℝ := fun x => q * Real.log (T.M (T.radius x))
  have hL : ContDiff ℝ ∞ L :=
    contDiff_const.mul (contDiff_materialLog_pullback hT (hT.1 T.M (by simp)) hp)
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hCb⟩ := iteratedDeriv_materialLogs_bound hT k hk
    refine ⟨|q| * C, mul_nonneg (abs_nonneg _) hC, fun x => ?_⟩
    simp only [L, iteratedDeriv_const_mul_field, abs_mul]
    exact mul_le_mul_of_nonneg_left (hCb x).2.1 (abs_nonneg _)
  have he : (fun x => T.M (T.radius x) ^ q) = fun x => Real.exp (L x) := by
    funext x
    rw [Real.rpow_def_of_pos (hp _ (hT.2.2.2.2.2.2.2.1 x).1)]
    dsimp only [L]
    rw [mul_comm]
  obtain ⟨C, hC, hCb⟩ := iteratedDeriv_exp_majorant hL hLb n
  refine ⟨C, hC, fun x => ?_⟩
  rw [he, congrFun he x]
  exact hCb x

theorem n07a_iteratedDeriv_materialM_pow_bound
    (hT : IsMaterialData D T) (c n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => T.M (T.radius t) ^ c) x| ≤
        C * T.M (T.radius x) ^ c := by
  simpa only [Real.rpow_natCast] using n07a_iteratedDeriv_materialM_rpow_bound hT c n

end ContinuousFlexibility.Analysis
