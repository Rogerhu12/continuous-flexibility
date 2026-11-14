import ContinuousFlexibility.Analysis.N04PulledFieldsColumnCurrent

/-!
# A common neighborhood for all five retained physical fields

The actual column theorem supplies both columns on one neighborhood.
The coefficient neighborhood is intersected with it once, before
choosing a field. Monotonicity retains the actual towers and the
original sample costs on that common neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Combining coefficient data with the constructed actual columns
chooses one neighborhood for all three coefficients and both columns. -/
theorem n04PulledFields_fieldData_of_coefficientData
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η)
    (hcoeff : ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : Fin 3, G.Data η (fun _ => True) base' ε'
        (G.pulled η (G.coefficientField η i))
        (G.pulledRef η (G.coefficientField η i))) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.FieldData η base' ε' := by
  obtain ⟨bc, εc, hbc, hεc, hεcε, hc⟩ := hcoeff
  obtain ⟨bl, εl, hbl, hεl, hεlε, hl⟩ :=
    n04PulledFieldsColumn_currentData G η hadm hgeo href
  have hE := (G.cost_nonneg η).1
  have hH := (G.cost_nonneg η).2.1
  refine ⟨max bc bl, min εc εl, hbc.trans (le_max_left _ _),
    lt_min hεc hεl, (min_le_left _ _).trans hεcε, ?_⟩
  exact ⟨fun i => (hc i).mono (fun _ h => h)
      (le_max_left _ _) (min_le_left _ _) hE hH,
    (hl (G.leftColumnField η) (Or.inl rfl)).mono (fun _ h => h)
      (le_max_right _ _) (min_le_right _ _) hE hH,
    (hl (G.nuField η) (Or.inr rfl)).mono (fun _ h => h)
      (le_max_right _ _) (min_le_right _ _) hE hH⟩

end ContinuousFlexibility.Analysis
