import ContinuousFlexibility.Analysis.SpacesPhysicalSynthesisRows

/-!
# Integer cells and the fixed natural-number row model

Reindexing a square-summable family along an equivalence preserves its
Hilbert norm. We apply this to the integer radial cells to use exactly
the fixed `PhysicalModelBanach` from the statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem spacesLpReindex_mem (e : α ≃ β) (u : lp (fun _ : α => E) 2) :
    Memℓp (fun j : β => u (e.symm j)) 2 := by
  apply memℓp_gen
  exact e.symm.summable_iff.mpr ((lp.memℓp u).summable (by norm_num))

/-- Reindex a genuine square-summable family, preserving its exact norm. -/
def spacesLpReindex (e : α ≃ β) :
    lp (fun _ : α => E) 2 ≃ₗᵢ[ℝ] lp (fun _ : β => E) 2 where
  toFun u := ⟨fun j => u (e.symm j), spacesLpReindex_mem e u⟩
  invFun u := ⟨fun i => u (e i), spacesLpReindex_mem e.symm u⟩
  left_inv u := by
    apply lp.ext
    funext i
    exact congrArg u (e.symm_apply_apply i)
  right_inv u := by
    apply lp.ext
    funext j
    exact congrArg u (e.apply_symm_apply j)
  map_add' _ _ := by
    apply lp.ext
    rfl
  map_smul' _ _ := by
    apply lp.ext
    rfl
  norm_map' u := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    exact congrArg (fun r : ℝ => r ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun i : α => ‖u i‖ ^ (2 : ℝ≥0∞).toReal))

theorem spacesLpReindex_apply (e : α ≃ β) (u : lp (fun _ : α => E) 2) (j : β) :
    spacesLpReindex e u j = u (e.symm j) := rfl

theorem spacesLpReindex_symm_apply (e : α ≃ β) (u : lp (fun _ : β => E) 2) (i : α) :
    (spacesLpReindex e).symm u i = u (e i) := rfl

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

/-- The concrete integer-cell Banach space is isometric to the prescribed
natural-number cylinder-row Banach space. -/
def spacesPhysicalRowsEquiv : SpacesPhysicalIntegerRows ≃ₗᵢ[ℝ] PhysicalModelBanach :=
  Analysis.spacesLpReindex Equiv.intEquivNat

theorem spacesPhysicalRowsEquiv_norm (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalRowsEquiv u‖ = ‖u‖ := spacesPhysicalRowsEquiv.norm_map u

theorem spacesPhysicalRowsEquiv_symm_norm (u : PhysicalModelBanach) :
    ‖spacesPhysicalRowsEquiv.symm u‖ = ‖u‖ := spacesPhysicalRowsEquiv.symm.norm_map u

end ContinuousFlexibility.Statements
