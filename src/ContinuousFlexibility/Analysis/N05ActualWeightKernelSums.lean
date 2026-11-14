module

public import ContinuousFlexibility.Analysis.N05ActualWeightKernel
public import ContinuousFlexibility.Analysis.N05IndexFiberSums

/-!
# Uniform Schur sums for the actual sampled weights

The real fiber cardinality hypothesis yields summability of the numerical
reciprocal-material majorant. The actual kernel is then summable in each
variable, with one common row and column bound. The material loss is four
for every source exponent and coefficient power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n05_actualWeightKernel_sums {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (cell : ℕ → ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ n, {m | D.cellIndex (cell m) = n}.Finite ∧
      ({m | D.cellIndex (cell m) = n}.ncard : ℝ) ≤ B * radialE n ^ B)
    (t c ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      (∀ k m, 0 ≤ n05ActualWeightKernel D T cell t c ε k m) ∧
      (∀ k, Summable (fun m => n05ActualWeightKernel D T cell t c ε k m) ∧
        (∑' m, n05ActualWeightKernel D T cell t c ε k m) ≤ A) ∧
      (∀ m, Summable (fun k => n05ActualWeightKernel D T cell t c ε k m) ∧
        (∑' k, n05ActualWeightKernel D T cell t c ε k m) ≤ A) := by
  obtain ⟨K, hK, hkernel⟩ := n05_actualWeightKernel_pointwise hD hT cell t c ε hε
  let w : ℕ → ℝ := fun k => Real.exp (-Radial.logM (D.cellIndex (cell k)))
  have hw (k : ℕ) : 0 ≤ w k := (Real.exp_pos _).le
  have hw1 (k : ℕ) : w k ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (zero_le_one.trans (Radial.logM_ge_one _))
  have hs : Summable w :=
    n05_referenceReciprocalMaterial_fiber_summable
      (fun k => D.cellIndex (cell k)) hB hfiber
  let A : ℝ := K * ((∑' k, w k) + 1)
  have hA : 0 < A := by
    have hsum0 : 0 ≤ ∑' k, w k := tsum_nonneg hw
    dsimp only [A]
    positivity
  have hsum_le : K * (∑' k, w k) ≤ A := by
    dsimp only [A]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hK.le
  have hrow (k m : ℕ) :
      n05ActualWeightKernel D T cell t c ε k m ≤ K * w m := by
    calc
      _ ≤ K * w k * w m := (hkernel k m).2
      _ ≤ K * 1 * w m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw1 k) hK.le) (hw m)
      _ = _ := by rw [mul_one]
  have hcol (k m : ℕ) :
      n05ActualWeightKernel D T cell t c ε k m ≤ K * w k := by
    calc
      _ ≤ K * w k * w m := (hkernel k m).2
      _ ≤ K * w k * 1 := mul_le_mul_of_nonneg_left (hw1 m) (mul_nonneg hK.le (hw k))
      _ = _ := mul_one _
  have hsum_bound (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ K * w n) :
      Summable f ∧ (∑' n, f n) ≤ A := by
    have hmajor := hs.mul_left K
    have hsf := hmajor.of_nonneg_of_le hf hle
    have hb := Summable.tsum_le_tsum hle hsf hmajor
    rw [tsum_mul_left] at hb
    exact ⟨hsf, hb.trans hsum_le⟩
  refine ⟨A, hA, fun k m => (hkernel k m).1, fun k => ?_, fun m => ?_⟩
  · exact hsum_bound _ (fun m => (hkernel k m).1) (hrow k)
  · exact hsum_bound _ (fun k => (hkernel k m).1) (fun k => hcol k m)

end ContinuousFlexibility.Statements

