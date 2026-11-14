import ContinuousFlexibility.Analysis.N04RealizationRetainedStart
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.N04bActualTypedAtlas

/-!
# The retained start of the Realization assembly as one record

`n04Realization_exists_retained_fieldStart` produces the retained seed, the
connected reference, material data, physical spaces, control geometry, return
equation and the optical correction field with Through03 and field regularity.
This file packs exactly that output into one structure, so that later
statements can quantify over every such start instead of restating it.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
  ContinuousFlexibility.Blueprint

/-- Everything `n04Realization_exists_retained_fieldStart` provides. -/
structure N04RealizationStart where
  S₀ : SelectedTailData
  K₀ : SeedCentralCutoff
  Cstar : ℝ
  requested : ℕ
  length : ℝ
  metadata : R10aSelectedMetadata Cstar requested S₀
  P : SeedRetainedPair S₀ K₀ 1 length
  Γ : ConnectedReferenceGeometry
  index : 4096 ≤ S₀.chain.index
  realizes : Γ.Realizes
  hw : Γ.reference.w = P.pair.profile
  hphi : Γ.reference.phi = P.pair.height
  construction : RadialConstructionGeometry Γ.reference
  coordinates : R11aRetainedCoordinates P Γ
  radial : IsRadialReference Γ.reference
  roots : ∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
    ∀ side : Bool, n04PositiveEndpoint i side ∈ radialCore Γ.reference ∧
      deriv Γ.reference.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv Γ.reference.w) (n04PositiveEndpoint i side) ≠ 0
  T : MaterialData
  S : PhysicalSpacesData
  C : NonlinearGeometryData S
  R : ReturnEquationData S
  base : ℕ
  loss : ℕ
  ε : ℝ
  hT : IsMaterialData Γ.reference T
  hS : IsPhysicalSpaces Γ.reference T S
  floor : ∀ r : ℝ, 1 ≤ T.E0 r
  primitive : N01PrimitiveGeometry Γ.reference T S C
  host : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m)
  base_ge : 4 ≤ base
  ε_pos : 0 < ε
  cutoff : N04bOpticalCutoffData Γ.reference S C base ε
  E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source
  through03 : NonlinearPropertiesThrough03 Γ.reference T S C R (cutoff.field E) base loss ε
  field : N04bFieldRegularity Γ.reference S C (cutoff.field E) base ε
  coefficients_eq :
    (cutoff.field E).coefficients = returnCorrectedCoefficients Γ.reference S C cutoff.cutoff
  minusFlow_eq : (cutoff.field E).minusFlow = returnCorrectedMinusFlow S C cutoff.cutoff

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The reference profile of the start. -/
abbrev D : ReferenceData := W.Γ.reference

/-- The optical correction field of the start. -/
abbrev L : ReturnCorrectionData W.S := W.cutoff.field W.E

/-- The enlarged material data used by every quantitative clause. -/
abbrev U : MaterialData := enlargedMaterialData W.T

/-- The original typed atlas for a piece enumeration. -/
abbrev A (e₀ : ℕ ≃ N04PieceIndex W.D) : CanonicalData W.S :=
  n04bActualTypedAtlas W.hT W.hS W.through03 W.field e₀

end N04RealizationStart

/-- The retained start exists. -/
theorem n04RealizationStart_nonempty : Nonempty N04RealizationStart := by
  obtain ⟨S₀, K₀, Cstar, requested, length, metadata, P, Γ, hindex, hΓ, hw, hphi, hconstr,
    hcoord, hD, hroots, T, S, C, R, base, loss, ε, hT, hS, hfloor, hG, hhost, hbase, hε,
    Q, E, hN, hfield, hcoef, hflow⟩ := n04Realization_exists_retained_fieldStart
  exact ⟨⟨S₀, K₀, Cstar, requested, length, metadata, P, Γ, hindex, hΓ, hw, hphi, hconstr,
    hcoord, hD, hroots, T, S, C, R, base, loss, ε, hT, hS, hfloor, hG, hhost, hbase, hε,
    Q, E, hN, hfield, hcoef, hflow⟩⟩

end ContinuousFlexibility.Analysis
