import ContinuousFlexibility.Analysis.N04PositiveGeometryActualFactorDirections

/-!
# One neighborhood for the controlled family and all actual factors

Restriction preserves each fixed-state root model and the ordinary
angular Jacobian bounds. The common neighborhood is selected before
any parameter prefix or spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem OrdinaryFlowJacobianBounds.mono
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base larger : ℕ} {ε η : ℝ}
    (h : OrdinaryFlowJacobianBounds S C base ε)
    (hb : base ≤ larger) (hε : η ≤ ε) :
    OrdinaryFlowJacobianBounds S C larger η :=
  fun z hz => h z (stateNeighborhood_mono S C hb hε hz)

theorem N04PositiveGeometryRootContext.mono
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base larger : ℕ} {ε η : ℝ} {m : ℕ} {side : Bool}
    (h : N04PositiveGeometryRootContext D S C K base ε m side)
    (hb : base ≤ larger) (hε : η ≤ ε) :
    N04PositiveGeometryRootContext D S C K larger η m side := by
  rcases h with ⟨g, R, hR, δ, hg, hg0, hfactor, hδ, hmodel⟩
  exact ⟨g, R, hR, δ, hg, hg0, hfactor, hδ,
    fun z hz hs => hmodel z (stateNeighborhood_mono S C hb hε hz) hs⟩

theorem n04PositiveGeometry_controlled_common_root_context
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (F : N04PositiveGeometryControlledFamily W X n) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ W.ε ∧ ε ≤ 1 ∧
      F.base ≤ base ∧ ε ≤ F.ε ∧ OrdinaryFlowJacobianBounds W.S W.C base ε ∧
      ∀ m side, N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side := by
  obtain ⟨b, η, hb, hη, hηW, hηone, hflow, hctx⟩ :=
    n04PositiveGeometry_common_root_context W X
  let base := max b F.base
  let ε := min η F.ε
  have hbb : b ≤ base := le_max_left _ _
  have hεη : ε ≤ η := min_le_left _ _
  exact ⟨base, ε, hb.trans hbb, lt_min hη F.radius_pos, hεη.trans hηW,
    hεη.trans hηone, le_max_right _ _, min_le_right _ _, hflow.mono hbb hεη,
    fun m side => (hctx m side).mono hbb hεη⟩

theorem n04PositiveGeometry_controlled_common_factor_context
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (F : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ W.ε ∧ ε ≤ 1 / 2 ∧
      F.base ≤ base ∧ ε ≤ F.ε ∧ OrdinaryFlowJacobianBounds W.S W.C base ε ∧
      (∀ m side, N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side) ∧
      ∀ i, Nonempty (N04PositiveGeometryFactorData F base ε i) := by
  obtain ⟨b, η, hb, hη, hηW, hηone, hFb, hηF, hflow, hctx⟩ :=
    n04PositiveGeometry_controlled_common_root_context F
  obtain ⟨low, hlow, hjoint⟩ := n04PositiveGeometry_actualFactorData_nonempty F hn
    hb hη hηW hηone hFb hηF hflow hctx
  let ε := min η (1 / 2)
  have hεη : ε ≤ η := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  exact ⟨low, ε, hb.trans hlow, lt_min hη (by norm_num), hεη.trans hηW, hεhalf,
    hFb.trans hlow, hεη.trans hηF, hflow.mono hlow hεη,
    (fun m side => (hctx m side).mono hlow hεη), hjoint low le_rfl ε hεη hεhalf⟩

end ContinuousFlexibility.Analysis
