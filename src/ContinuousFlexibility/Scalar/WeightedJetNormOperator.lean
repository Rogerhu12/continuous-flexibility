module

public import ContinuousFlexibility.Scalar.WeightedJetNorm
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Passing uniform jet estimates to an actual field operation

The constant for a physical norm is selected from its finite set of jet
indices before the input field is chosen. The input order is the output
order plus the one fixed loss in the supplied jet estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped BigOperators ENNReal

theorem physicalNorm_bound_of_operator_jet_bounds
    {D : ReferenceData} {T : MaterialData} {γ δ : ℝ} {loss : ℕ}
    {op : (PolarPoint → ℝ) → PolarPoint → ℝ}
    (hjets : ∀ a b c : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
        MemLp (weightedPhysicalJet T δ a b c (op f)) 2 materialCylinderMeasure ∧
        (eLpNorm (weightedPhysicalJet T δ a b c (op f)) 2 materialCylinderMeasure).toReal ≤
          C * physicalNorm T γ (a + b + c + loss) f)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      physicalNorm T δ s (op f) ≤ C * physicalNorm T γ (s + loss) f := by
  classical
  choose B hB hBx using fun j : JetIndex s =>
    hjets (j.val 0).val (j.val 1).val (j.val 2).val
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hB j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun f hf => ?_⟩
  have hN : 0 ≤ physicalNorm T γ (s + loss) f := Real.sqrt_nonneg _
  have hmem (a b c : ℕ) (_ : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T δ a b c (op f)) 2 materialCylinderMeasure := by
    obtain ⟨_, _, hb⟩ := hjets a b c
    exact (hb f hf).1
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T δ a b c (op f)) 2 materialCylinderMeasure).toReal ≤
        K * physicalNorm T γ (s + loss) f := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj : (eLpNorm (weightedPhysicalJet T δ a b c (op f))
        2 materialCylinderMeasure).toReal ≤ B j * physicalNorm T γ (a + b + c + loss) f := by
      simpa [j] using (hBx j f hf).2
    exact hj.trans ((mul_le_mul_of_nonneg_left
      (physicalNorm_monotone_of_heightMember hf (by omega)) (hB j)).trans
        (mul_le_mul_of_nonneg_right (hBK j) hN))
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK hN) hmem hbound).trans_eq (by ring)

end ContinuousFlexibility.Statements
