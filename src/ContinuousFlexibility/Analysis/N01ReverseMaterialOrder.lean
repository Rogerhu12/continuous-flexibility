module

public import ContinuousFlexibility.Analysis.MaterialSampleBalancedConstraint
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# One fixed material order from the actual control-label constraint

The coefficient on the two height powers is identical. The only
reindexing used here is the bounded index displacement already present
in N01; the cell on the right may be an independently supplied actual
containing radial cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem N01Properties.material_order_transfer_of_balanced_constraint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {K A N : ℝ} (hK : 0 < K) :
    ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m j : ℕ,
      1 ≤ K * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A *
        T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.M (T.sample j) ^ N →
      T.M (T.sample m) ^ s ≤ Cs * T.M (T.sample j) ^ (s + 1) := by
  obtain ⟨B, hB, hlabel⟩ := hN.2.2.2.2.1
  intro s
  obtain ⟨Cs, hCs, hb⟩ := materialSample_M_rpow_of_reindexed_balanced_height_constraint
    hT hN.1.1 C.cell hB.le hlabel (A := A) (N := N)
      (by norm_num : (0 : ℝ) < 3 / 4) hK (Nat.cast_nonneg s) (by norm_num : (0 : ℝ) < 1)
  refine ⟨Cs, hCs, fun m j hraw => ?_⟩
  have h := hb m j hraw
  have horder : (s : ℝ) + 1 = ((s + 1 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [horder, Real.rpow_natCast, Real.rpow_natCast] at h
  exact h

end ContinuousFlexibility.Statements
