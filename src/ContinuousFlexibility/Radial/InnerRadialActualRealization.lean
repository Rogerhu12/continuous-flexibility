import ContinuousFlexibility.Radial.InnerRadialActualPieces

/-!
# Local weak realizations from the actual model/gap dictionary

Each selected piece supplies its real source/trace solution, using the
same physical Dirichlet and Poisson maps recorded by its coefficients.
The homogeneous realization also supplies its complete conormal block.
These are proved outputs, not assumptions of finite-chain assembly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

theorem innerRadialPhysical_pieceSource (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool) (central piece : Fin (n + 1))
    (F : InnerRadialPhysicalSource D G bordered) :
    innerBorderPieceProjection (radialHilbertMeasure D)
      (fun p => Ioo (G.left p) (G.right p)) central piece F.val =
      WithLp.toLp 2 (innerRadialPhysicalForcing D G bordered F piece,
        if piece = central then innerRadialPhysicalRow D G bordered F else 0) := by
  simp only [innerBorderPieceProjection_apply, innerRadialPhysicalForcing_apply,
    innerRadialPhysicalRow_apply]

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  {piece : Fin (n + 1)} (A : InnerRadialModelChart D G bordered j central column piece)
  (hw : ContDiff ℝ ∞ D.w)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered
local notation "projection" => innerBorderPieceProjection (radialHilbertMeasure D)
  (fun p => Ioo (G.left p) (G.right p)) central piece

theorem exists_solution (F : H) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ s : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column F ξ piece,
      (WithLp.toLp 2 (s.q.1, s.borderScalar) : InnerBorderL2 (radialHilbertMeasure D)) =
        A.dirichlet (projection F.val) + A.poisson (innerChainBoundaryCLM n piece ξ) := by
  obtain ⟨s, hvalue, hscalar⟩ :=
    exists_innerRadialModelPieceSolution D G bordered j central column piece
      A.buffer_hypotheses A.localized A.height_pos A.radius_smooth A.scale_smooth
      A.chart_pos A.in_core A.weight_identity A.U A.U_nonneg A.log_deriv_bound hw
      A.potential_identity A.left_eq A.right_eq A.bordered_eq A.column_eq F ξ
  refine ⟨s, ?_⟩
  rw [hvalue, hscalar]
  simp only [InnerRadialModelChart.dirichlet, innerLiouvilleHilbertDirichlet_apply,
    innerRadialPhysical_pieceSource, WithLp.ofLp_toLp, InnerRadialModelChart.poisson_apply,
    innerChainBoundaryCLM_apply, ContinuousLinearMap.coe_coe,
    WithLp.toLp_add, WithLp.toLp_smul]

theorem exists_poisson (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ s : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column 0 ξ piece,
      (WithLp.toLp 2 (s.q.1, s.borderScalar) : InnerBorderL2 (radialHilbertMeasure D)) =
        A.poisson (innerChainBoundaryCLM n piece ξ) ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D s.q s.potential 0
          (if piece = central then column else 0) s.borderScalar
          (innerRadialAffineUnitPair D hw.continuous (G.left_pos piece)
            (G.in_core piece) (G.weight_pos piece) i) =
          Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            (Matrix.diagonal A.kappa + A.errorMatrix) (innerChainBoundaryCLM n piece ξ) i := by
  obtain ⟨s, hvalue, hscalar, hflux⟩ :=
    exists_innerRadialModelPoissonPiece D G bordered j central column piece
      A.buffer_hypotheses A.localized A.height_pos A.radius_smooth A.scale_smooth
      A.chart_pos A.in_core A.weight_identity A.U A.U_nonneg A.log_deriv_bound hw
      A.potential_identity A.left_eq A.right_eq A.bordered_eq A.column_eq ξ
  refine ⟨s, ?_, ?_⟩
  · rw [hvalue, hscalar, InnerRadialModelChart.poisson_apply]
    simp only [innerChainBoundaryCLM_apply]
  · intro i
    simpa +unfoldPartialApp only [InnerBufferLocalizedData.physicalFluxMatrix,
      InnerRadialModelChart.kappa, InnerRadialModelChart.errorMatrix] using hflux i

end InnerRadialModelChart

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)} (A : InnerRadialGapChart D G j central piece)
  (hw : ContDiff ℝ ∞ D.w) (bordered : Bool) (column : RadialModeL2 D)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered
local notation "projection" => innerBorderPieceProjection (radialHilbertMeasure D)
  (fun p => Ioo (G.left p) (G.right p)) central piece

theorem exists_solution (F : H) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ s : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column F ξ piece,
      (WithLp.toLp 2 (s.q.1, s.borderScalar) : InnerBorderL2 (radialHilbertMeasure D)) =
        A.dirichlet hw (projection F.val) +
          A.poisson hw.continuous (innerChainBoundaryCLM n piece ξ) := by
  obtain ⟨s, hvalue, hscalar, _hflux⟩ :=
    exists_innerRadialGapPieceSolution D hw G bordered j central column piece A.away_center
      A.frequency_pos A.slope A.slope_pos A.slope_lower A.columns A.columns_smooth
      A.columns_boundary A.columns_homogeneous F ξ
  refine ⟨s, ?_⟩
  rw [hvalue, hscalar, InnerRadialGapChart.dirichlet_apply,
    InnerRadialGapChart.poisson_apply, innerRadialPhysical_pieceSource, WithLp.toLp_fst]
  simp only [InnerRadialGapChart.fieldDirichlet, InnerRadialGapChart.fieldPoisson,
    ← WithLp.toLp_add, Prod.mk_add_mk, add_zero]

theorem exists_poisson (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ s : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column 0 ξ piece,
      (WithLp.toLp 2 (s.q.1, s.borderScalar) : InnerBorderL2 (radialHilbertMeasure D)) =
        A.poisson hw.continuous (innerChainBoundaryCLM n piece ξ) ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D s.q s.potential 0
          (if piece = central then column else 0) s.borderScalar
          (innerRadialAffineUnitPair D hw.continuous (G.left_pos piece)
            (G.in_core piece) (G.weight_pos piece) i) =
          Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            A.fluxMatrix (innerChainBoundaryCLM n piece ξ) i := by
  obtain ⟨s, hvalue, hscalar, hflux⟩ :=
    exists_innerRadialGapPoissonPiece D hw G bordered j central column piece A.away_center
      A.frequency_pos A.slope A.slope_pos A.slope_lower A.columns A.columns_smooth
      A.columns_boundary A.columns_homogeneous ξ
  refine ⟨s, ?_, ?_⟩
  · rw [hvalue, hscalar, InnerRadialGapChart.poisson_apply]
    simp only [InnerRadialGapChart.fieldPoisson]
  · intro i
    simpa only [InnerRadialGapChart.fluxMatrix, innerGapFluxOperator] using hflux i

end InnerRadialGapChart

namespace InnerRadialActualPiece

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  {piece : Fin (n + 1)} (A : InnerRadialActualPiece D G bordered j central column piece)
  (hw : ContDiff ℝ ∞ D.w)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered
local notation "projection" => innerBorderPieceProjection (radialHilbertMeasure D)
  (fun p => Ioo (G.left p) (G.right p)) central piece

theorem exists_solution (F : H) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ s : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column F ξ piece,
      (WithLp.toLp 2 (s.q.1, s.borderScalar) : InnerBorderL2 (radialHilbertMeasure D)) =
        A.dirichlet hw (projection F.val) +
          A.poisson hw.continuous (innerChainBoundaryCLM n piece ξ) := by
  cases A with
  | inl M => exact M.exists_solution hw F ξ
  | inr Q => exact Q.exists_solution hw bordered column F ξ

include A in
theorem solution_nonempty (F : H) (ξ : EuclideanSpace ℝ (Fin n)) :
    Nonempty (InnerRadialPieceSolution D hw.continuous G forcing rowSource
      bordered j central column F ξ piece) := by
  obtain ⟨s, _⟩ := A.exists_solution hw F ξ
  exact ⟨s⟩

theorem exists_poisson (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ s : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column 0 ξ piece,
      (WithLp.toLp 2 (s.q.1, s.borderScalar) : InnerBorderL2 (radialHilbertMeasure D)) =
        A.poisson hw.continuous (innerChainBoundaryCLM n piece ξ) ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D s.q s.potential 0
          (if piece = central then column else 0) s.borderScalar
          (innerRadialAffineUnitPair D hw.continuous (G.left_pos piece)
            (G.in_core piece) (G.weight_pos piece) i) =
          Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            (A.referenceMatrix + A.errorMatrix) (innerChainBoundaryCLM n piece ξ) i := by
  cases A with
  | inl M =>
    simpa only [poisson, referenceMatrix, kappa, gapMatrix, errorMatrix, add_zero] using
      M.exists_poisson hw ξ
  | inr Q =>
    simpa only [poisson, referenceMatrix, kappa, gapMatrix, errorMatrix,
      Matrix.diagonal_zero, zero_add, add_zero] using Q.exists_poisson hw bordered column ξ

end InnerRadialActualPiece

end ContinuousFlexibility.Radial
