import ContinuousFlexibility.Analysis.MaterialScaleSampleJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeUnitMaterialGeometry
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# The two actual scale atoms on the same whole reference atlas

The original negative half samples and the positive midpoint samples are
retained. The true whole-unit geometry supplies the sample comparison and
physical width, so the scalar scale estimates apply without a new atlas.
The explicit envelope enlargement packages the finite orders uniformly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped BigOperators

def canonicalScaleAtom (inverse : Bool) : Atom :=
  if inverse then .materialEllInverse else .materialEll

theorem canonicalScaleAtom_eq_signedScale
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (inverse : Bool) :
    atom D T S C L K z m (canonicalScaleAtom inverse) =
      fun p => if inverse then (T.ell (physicalUnitPoint K m p).1)⁻¹
        else T.ell (physicalUnitPoint K m p).1 := by
  cases inverse <;> funext p <;>
    simp only [canonicalScaleAtom, atom, Bool.false_eq_true, ite_false, ite_true]

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
theorem n04WholeReferenceGauge_scale_unit_jets
    (U : MaterialData) (hU : IsMaterialData Γ.reference U)
    (hsample : U.sample = T.sample) (inverse : Bool) (a : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ z m, ∀ p ∈ unitStrip, ∀ b : ℕ,
      |mixedDerivative a b
        (atom Γ.reference U S C L V z m (canonicalScaleAtom inverse)) p| ≤
          B * U.E0 (U.sample (V.cell m)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨X, hX, hgeometry⟩ := n04WholeReferenceGauge_unit_material_geometry
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  obtain ⟨B, A, hB, hA, hjet⟩ :=
    materialEll_signed_affine_unit_jet_bound hU hN.1.1.1.1 inverse a hX
  refine ⟨B, A, hB, hA, ?_⟩
  intro z m p hp b
  rw [canonicalScaleAtom_eq_signedScale]
  have hpoint := (hgeometry m).2.2 p hp
  have hwidth : |V.physicalRight m - V.physicalLeft m| ≤
      |Γ.reference.b - Γ.reference.a| := by
    rw [abs_of_pos (hgeometry m).1]
    exact (hgeometry m).2.1.trans (le_abs_self _)
  have hdist :
      |endpointX 1 (Statements.endpointDistance Γ.reference (physicalUnitPoint V m p).1) -
        endpointX 1 (Statements.endpointDistance Γ.reference (U.sample (V.cell m)))| ≤ X := by
    rw [hsample]
    exact hpoint.2
  exact hjet (V.physicalLeft m) (V.physicalRight m - V.physicalLeft m)
    (U.sample (V.cell m)) hwidth
    (materialSample_mem_interval hN.1.1.1.1 hU (V.cell m)) p hpoint.1 hdist b

include P hS₀ hband hq hΓ hw hcoordinates hcell in
/-- One constant covers both scale atoms and every requested finite
spatial order on the same whole atlas and explicit enlarged material data. -/
theorem n04WholeReferenceGauge_scaleReferenceJets_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let T' := enlargedMaterialData T
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z m inverse, ∀ p ∈ unitStrip,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b
          (atom Γ.reference T' S C L V z m (canonicalScaleAtom inverse)) p| ≤
            B * T'.E0 (T'.sample (V.cell m)) ^ B := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let T' := enlargedMaterialData T
  have hT' : IsMaterialData Γ.reference T' :=
    isMaterialData_enlargedMaterialData hN.1.1.1.1 hT
  have hsample : T'.sample = T.sample := rfl
  intro s
  let I := Fin (s + 1) × Bool
  have hfamily (i : I) := n04WholeReferenceGauge_scale_unit_jets
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
      T' hT' hsample i.2 i.1.val
  choose C₀ A hC₀ hA hjet using hfamily
  choose B hB hpack using fun i : I => coefficientEnvelope_pack (C₀ i) (A i)
  let M : ℝ := 1 + ∑ i : I, B i
  have hsum : 0 ≤ ∑ i : I, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hBM (i : I) : B i ≤ M :=
    (Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨M, hM, ?_⟩
  intro z m inverse p hp a b hab
  let i : I := (⟨a, by omega⟩, inverse)
  let t := T'.E0 (T'.sample (V.cell m))
  have hs := materialSample_mem_interval hN.1.1.1.1 hT (V.cell m)
  have hfloor : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hs
  calc
    _ ≤ C₀ i * t ^ A i := hjet i z m p hp b
    _ ≤ B i * t ^ B i := hpack i t hfloor
    _ ≤ M * t ^ M := mul_le_mul (hBM i)
      (Real.rpow_le_rpow_of_exponent_le hfloor (hBM i))
      (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hM.le

end ContinuousFlexibility.Analysis
