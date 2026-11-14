module

public import ContinuousFlexibility.Analysis.N04PositiveReferenceMaterialBounds
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# One sampled material envelope for the fixed reference jet prefix

The retained reference certificate bounds each inverse order at the
same positive component sample. This file collects the finite prefix
before choosing the component or evaluation point, and absorbs the
reference normalization into the enlarged material cost used by
CurrentJets. No reference field is selected again.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

/-- The coordinate, genuine inverse, height and reciprocal height have
one common sampled cost at every requested finite prefix. -/
theorem n04PositiveGeometry_reference_prefix_material_cost
    {ι : Type*} {T : MaterialData} {cell : ι → ℕ} {Y H : ι → ℝ → ℝ}
    (hfloor : ∀ x, 1 ≤ T.E0 x)
    (h : N04PositiveReferenceMaterialBounds T cell Y H) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i, ∀ k : ℕ, k ≤ N → ∀ x : ℝ,
      let E := (enlargedMaterialData T).E0 (T.sample (cell i))
      |iteratedDeriv (k + 1) (Y i) x| ≤ B * E ^ B ∧
      |iteratedDeriv (k + 1) (Function.invFun (Y i)) x| ≤ B * E ^ B ∧
      |iteratedDeriv k (H i) x| ≤ B * E ^ B ∧
      |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤ B * E ^ B := by
  classical
  obtain ⟨C0, hC0, hC0E, hjet⟩ := h
  choose M hM hj using hjet
  let P : ℝ := 1 + ∑ j : Fin (N + 1), M j.val
  have hP : 1 ≤ P := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hM j.val)))
  have hMP (k : ℕ) (hk : k ≤ N) : M k ≤ P :=
    (Finset.single_le_sum
      (f := fun j : Fin (N + 1) => M j.val)
      (fun j _ => zero_le_one.trans (hM j.val))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)))).trans
        (le_add_of_nonneg_left zero_le_one)
  obtain ⟨B0, hB0, hpack⟩ := coefficientEnvelope_pack (P * C0 ^ P) P
  let B := max 1 B0
  have hB : 1 ≤ B := le_max_left _ _
  have hBB : B0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro i k hk x
  let E := (enlargedMaterialData T).E0 (T.sample (cell i))
  have hEU : T.E0 (T.sample (cell i)) ≤ E := le_enlargedMaterialData_E0 T _
  have hE : 1 ≤ E := (hfloor _).trans hEU
  have hCE : 1 ≤ C0 * E := one_le_mul_of_one_le_of_one_le hC0 hE
  have hbase : 0 ≤ C0 * T.E0 (T.sample (cell i)) :=
    mul_nonneg (zero_le_one.trans hC0) (zero_le_one.trans (hfloor _))
  have hcost : M k * (C0 * T.E0 (T.sample (cell i))) ^ M k ≤ B * E ^ B := by
    calc
      _ ≤ M k * (C0 * E) ^ M k :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hbase
            (mul_le_mul_of_nonneg_left hEU (zero_le_one.trans hC0))
            (zero_le_one.trans (hM k))) (zero_le_one.trans (hM k))
      _ ≤ P * (C0 * E) ^ P :=
        mul_le_mul (hMP k hk) (Real.rpow_le_rpow_of_exponent_le hCE (hMP k hk))
          (Real.rpow_nonneg (zero_le_one.trans hCE) _) (zero_le_one.trans hP)
      _ = (P * C0 ^ P) * E ^ P := by
        rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans hE)]
        ring
      _ ≤ B0 * E ^ B0 := hpack E hE
      _ ≤ B * E ^ B := mul_le_mul hBB (Real.rpow_le_rpow_of_exponent_le hE hBB)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hfields := (hj k i).1 k le_rfl x
  exact ⟨hfields.1.trans hcost, ((hj k i).2 x).trans hcost,
    hfields.2.1.trans hcost, hfields.2.2.trans hcost⟩

end ContinuousFlexibility.Analysis
