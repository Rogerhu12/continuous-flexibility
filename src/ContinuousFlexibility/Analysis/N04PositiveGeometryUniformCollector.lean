import ContinuousFlexibility.Analysis.N04PositiveGeometryCoordinatesCollector
import ContinuousFlexibility.Analysis.N04PositiveGeometryAuxiliary
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoordinateDirections

/-!
# A uniform neighborhood for all positive geometry atoms

Three completed data families are restricted to one neighborhood.
Reciprocals are constructed at the zero auxiliary column, after which
the existing preservation theorem gives the same neighborhood for all
columns. No additional reference-jet premise is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

namespace N04RealizationGauge

theorem positiveGeometryData_of_uniform_coordinates_height
    (G : N04RealizationGauge) {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε)
    (hmaterial : N04PositiveReferenceMaterialBounds G.W.T G.X.cell G.Y G.H)
    (hC : ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space, ∀ inverse angle : Bool,
      G.Data η (G.Pos η) b δ
        (G.atomFamily η (n04PositiveGeometry_coordinateAtom inverse angle))
        (G.atomRef η (n04PositiveGeometry_coordinateAtom inverse angle)))
    (hH : ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      G.Data η (G.Pos η) b δ (G.atomFamily η .height) (G.atomRef η .height))
    (hP : ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      G.Data η (G.Pos η) b δ (G.pulledHeight η) (G.pulledHeightRef η)) :
    ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space, G.GeometryData η (G.Pos η) b δ := by
  rcases hC with ⟨bC, hbC, εC, hεC, hεCε, _, hC⟩
  rcases hH with ⟨bH, hbH, εH, hεH, _, _, hH⟩
  rcases hP with ⟨bP, hbP, εP, hεP, _, _, hP⟩
  let b := max bC (max bH bP)
  let δ := min εC (min εH εP)
  have hCb : bC ≤ b := le_max_left _ _
  have hHb : bH ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hPb : bP ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  have hb : base ≤ b := hbC.trans hCb
  have hδ : 0 < δ := lt_min hεC (lt_min hεH hεP)
  have hδC : δ ≤ εC := min_le_left _ _
  have hδH : δ ≤ εH := (min_le_right _ _).trans (min_le_left _ _)
  have hδP : δ ≤ εP := (min_le_right _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε := hδC.trans hεCε
  have hA' : G.Admissible b δ := G.admissible_mono hA hb hδ hδε
  let η₀ : (G.W.S.height (3 / 4 : ℝ)).Space := 0
  have hcost := G.cost_nonneg η₀
  have hC' (inverse angle : Bool) : G.Data η₀ (G.Pos η₀) b δ
      (G.atomFamily η₀ (n04PositiveGeometry_coordinateAtom inverse angle))
      (G.atomRef η₀ (n04PositiveGeometry_coordinateAtom inverse angle)) :=
    (hC η₀ inverse angle).mono (fun _ h => h) hCb hδC hcost.1 hcost.2.1
  have hH' := (hH η₀).mono (fun _ h => h) hHb hδH hcost.1 hcost.2.1
  have hP' := (hP η₀).mono (fun _ h => h) hPb hδP hcost.1 hcost.2.1
  obtain ⟨larger, hlarger, ρ, hρ, hρδ, hρhalf, hgeometry⟩ :=
    G.positiveGeometryData_of_coordinates_height hA' hmaterial η₀
      (hC' false false) (hC' false true) (hC' true false) (hC' true true) hH' hP'
  exact ⟨larger, hb.trans hlarger, ρ, hρ, hρδ.trans hδε, hρhalf,
    fun η => G.positiveGeometry_data_auxiliary η₀ η larger ρ hgeometry⟩

end N04RealizationGauge

end ContinuousFlexibility.Analysis
