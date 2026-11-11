import ContinuousFlexibility.Blueprint.N01c.Statements
import ContinuousFlexibility.Analysis.N01cCoefficientTameBounds
import ContinuousFlexibility.Analysis.N01cMaterialNormalization

/-!
# N01c: coefficient families

The normalized N01b witness retains its original control placement and
cutoff support. The actual mixed coefficient estimates then hold on one
smaller neighbourhood with one fixed base and loss.
Source: readable §7, Proposition 7.8 and its coefficient/weight estimates.
Task: `docs/tasks/N01c-Coefficients.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01cCoefficients (hN01b : N01bStatement) : N01CoefficientStatement := by
  obtain ⟨A, T, S, C, base, ε, hT, hS, hA, hε, hB, hG, hE⟩ :=
    n01b_exists_normalized_material hN01b
  obtain ⟨base', loss, hbase, hcoef⟩ :=
    n01_coefficientFamilyTameBounds_of_localization
      hS hT hA hε hB hE hG.1 hG.2.1
  exact ⟨A, T, S, C, base', loss, min ε (1 / 2), hT, hS, hA,
    lt_min hε (by norm_num), n01PartB_mono hB hbase (min_le_left ε (1 / 2)), hcoef, hG⟩

end ContinuousFlexibility.Blueprint
