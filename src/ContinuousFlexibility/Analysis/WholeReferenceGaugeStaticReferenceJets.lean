module

public import ContinuousFlexibility.Analysis.WholeReferenceGaugeLengthReferenceJets
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeScaleReferenceJets
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeMaterialRatioReferenceJets

/-!
# The twelve static reference atoms on one actual whole atlas

The four length atoms, two material scales and six material ratios use
the same original typed atlas, whole-piece indices and stored samples.
Their proved finite-order bounds are combined after one explicit material
enlargement. No reference-jet estimate is assumed as an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

variable {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S₀ K₀ q length) (hS₀ : IsSelectedTail S₀)
  (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
  {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile)
  (hcoordinates : R11aRetainedCoordinates P Γ)
  {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
  (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
  (hfield : N04bFieldRegularity Γ.reference S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex Γ.reference) (e : ℕ ≃ N04WholePieceIndex Γ.reference)
  (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
  (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
  (ψ χ : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
    PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
    PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
      PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
      PolarPoint → ℝ)
  (N : Set ℝ)

include P hS₀ hband hq hΓ hw hcoordinates hcell in
/-- All twelve static atoms have the actual reference spatial regularity
and one common finite-order sample bound. The conclusion holds for every
state because these atoms are state independent; the atlas is unchanged. -/
theorem n04WholeReferenceGauge_staticReferenceJets_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let U := enlargedMaterialData T
    (∀ z m a, CanonicalFixedGeometryAtom a ∨ CanonicalMaterialRatioAtom a →
      ContDiffOn ℝ ∞ (atom Γ.reference U S C L V z m a) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom Γ.reference U S C L V z m a (p + (0, Real.pi)) =
          atom Γ.reference U S C L V z m a p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z m a,
      CanonicalFixedGeometryAtom a ∨ CanonicalMaterialRatioAtom a →
      ∀ p ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (atom Γ.reference U S C L V z m a) p| ≤
          B * U.E0 (U.sample (V.cell m)) ^ B := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let U := enlargedMaterialData T
  have hU : IsMaterialData Γ.reference U :=
    isMaterialData_enlargedMaterialData hΓ.2.1 hT
  obtain ⟨X, hX, hgeometry⟩ := n04WholeReferenceGauge_unit_material_geometry
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  obtain ⟨_, hlength⟩ := n04WholeReferenceGauge_lengthReferenceJets_enlargedMaterialData
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  have hscale := n04WholeReferenceGauge_scaleReferenceJets_enlargedMaterialData
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  obtain ⟨_, hratio⟩ := n04WholeReferenceGauge_materialRatioReferenceJets_enlargedMaterialData
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  refine ⟨?_, ?_⟩
  · intro z m a ha
    exact ⟨canonical_staticAtom_contDiffOn_of_core hU z m ha
      (fun p hp => ((hgeometry m).2.2 p hp).1),
      fun p _ => canonical_staticAtom_angle_period z m ha p⟩
  · intro s
    obtain ⟨BL, hBL, hL⟩ := hlength s
    obtain ⟨BE, hBE, hE⟩ := hscale s
    obtain ⟨BR, hBR, hR⟩ := hratio s
    let B : ℝ := 1 + BL + BE + BR
    have hB : 0 < B := by dsimp only [B]; positivity
    have hBLB : BL ≤ B := by dsimp only [B]; linarith only [hBE, hBR]
    have hBEB : BE ≤ B := by dsimp only [B]; linarith only [hBL, hBR]
    have hBRB : BR ≤ B := by dsimp only [B]; linarith only [hBL, hBE]
    refine ⟨B, hB, ?_⟩
    intro z m a ha p hp i j hij
    let t := U.E0 (U.sample (V.cell m))
    have hs := materialSample_mem_interval hΓ.2.1 hT (V.cell m)
    have hfloor : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hs
    have hpack {d : ℝ} (hd : d ≤ B) : d * t ^ d ≤ B * t ^ B :=
      mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le hfloor hd)
        (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hB.le
    rcases ha with hfixed | hratios
    · rcases hfixed with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hL z m false false p hp i j hij).trans (hpack hBLB)
      · exact (hL z m false true p hp i j hij).trans (hpack hBLB)
      · exact (hL z m true false p hp i j hij).trans (hpack hBLB)
      · exact (hL z m true true p hp i j hij).trans (hpack hBLB)
      · exact (hE z m false p hp i j hij).trans (hpack hBEB)
      · exact (hE z m true p hp i j hij).trans (hpack hBEB)
    · exact (hR z m a hratios p hp i j hij).trans (hpack hBRB)

end ContinuousFlexibility.Analysis
