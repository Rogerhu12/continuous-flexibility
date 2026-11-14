module

public import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly

/-!
# The negative component adjoining a retained positive endpoint

The retained reference has interior simple roots at every positive
endpoint. Consequently every already chosen source is a genuine negative
component, including at the right endpoint. The natural-number selector
below retains that supplied source rather than choosing a new adjacency.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- Every supplied positive endpoint source is a negative component:
the alternative ambient source contradicts the retained interior-root
certificate. Both endpoints use the same argument. -/
theorem n04PositiveGeometry_source_some
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
    ∃ m : ℕ, (X.src i side).val = some m := by
  cases hsource : (X.src i side).val with
  | none =>
      have hamb : n04PositiveEndpoint i side = (if side then W.D.b else W.D.a) := by
        simpa only [hsource] using (X.src i side).property
      have hcore : W.D.a < n04PositiveEndpoint i side ∧
          n04PositiveEndpoint i side < W.D.b := (W.roots i side).1
      cases side with
      | false => exact False.elim (hcore.1.ne' hamb)
      | true => exact False.elim (hcore.2.ne hamb)
  | some m => exact ⟨m, rfl⟩

theorem n04PositiveGeometry_rightSource_exists
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    ∃ m : ℕ, (X.src i true).val = some m :=
  n04PositiveGeometry_source_some W X i true

/-- The fixed source index used by the supplied right endpoint. -/
def n04PositiveGeometry_rightSource
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : ℕ :=
  (n04PositiveGeometry_rightSource_exists W X i).choose

theorem n04PositiveGeometry_rightSource_spec
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    (X.src i true).val = some (n04PositiveGeometry_rightSource W X i) :=
  (n04PositiveGeometry_rightSource_exists W X i).choose_spec

end ContinuousFlexibility.Analysis
