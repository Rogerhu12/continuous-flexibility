import ContinuousFlexibility.Analysis.N04RealizationLeadStart
import ContinuousFlexibility.Analysis.N04RealizationLeadReplacement
import ContinuousFlexibility.Analysis.N04RealizationCurrentJetCollector
import ContinuousFlexibility.Analysis.WholePositiveEndpointFields
import ContinuousFlexibility.Analysis.N04WholeComponentPieces
import ContinuousFlexibility.Analysis.N04bReferencePieces
import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer
import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell

/-!
# The Realization theorem from four explicit obligations

The retained start, the supplied-family gauge geometry, the auxiliary-column
replacement and the same-witness completion are proved. Four statements
remain as hypotheses:

* `N04RealizationOpticalObligation`: the optical lower bound with a material
  cost for the start's control geometry;
* `N04RealizationReferenceObligation`: one reference family and, for every
  positive transport family that is the identity at the reference state and
  every smaller neighborhood, one auxiliary column with the reference jets,
  the reference principal bounds and the auxiliary gauge;
* `N04RealizationCurrentObligation`: one positive transport family with its
  matching on a smaller neighborhood, and the current jets of every
  non-auxiliary atom of the resulting atlas;
* `N04RealizationSampleObligation`: the bounded sample displacement of the
  reference-gauged atlas.

All four are stated for the same displayed objects, so the witness is the same.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
  ContinuousFlexibility.Blueprint
open CanonicalGeometry
open scoped ContDiff

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

/-- The choices made after the start and before any canonical family. -/
structure N04RealizationChoice (W : N04RealizationStart) where
  κ : ℝ
  κ_pos : 0 < κ
  optical : ∀ m x, x ∈ Ioo (W.C.left m) (W.C.right m) →
    κ⁻¹ * W.T.E0 (W.T.sample (W.C.cell m)) ^ (-κ) *
      min (x - W.C.left m) (W.C.right m - x) ≤ -deriv W.D.w x / (x * W.D.w x)
  e₀ : ℕ ≃ N04PieceIndex W.D
  cell : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℕ
  cell_mem : ∀ i, n04PositiveMidpoint i ∈ W.D.cells (cell i)
  src : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
    ∀ side, N04PositiveEndpointSource W.C i side

/-- The reference-gauged atlas of a start, a choice, a reference family and a
positive transport family. -/
abbrev n04RealizationAtlas (W : N04RealizationStart) (X : N04RealizationChoice W)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (τ σ : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ)
    (N : Set ℝ) : CanonicalData W.S :=
  n04WholeReferenceGaugeAtlasData W.C W.L (W.A X.e₀) e X.cell
    (fun i => positiveReferenceCylinderChart (Y i))
    (fun i => positiveReferenceCylinderInverse (Y i))
    (fun i p => H i p.1) τ σ Q N

/-- Atoms whose value does not depend on the state: lengths, material
radius and the material ratios. -/
def atomIsStatic : Atom → Prop
  | .physicalLength | .physicalLengthInverse | .canonicalLength | .canonicalLengthInverse
  | .materialEll | .materialEllInverse | .ratioH | .ratioHInverse | .ratioM | .ratioMInverse
  | .ratioE0 | .ratioE0Inverse => True
  | _ => False

theorem atom_state_eq_of_static {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {a : Atom} (ha : atomIsStatic a) (z z' : AnnularState S × ℝ) (m : ℕ) :
    atom D T S C L K z m a = atom D T S C L K z' m a := by
  cases a <;> first | exact ha.elim | rfl

theorem mixedDerivative_fun_zero (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun _ : PolarPoint => (0 : ℝ)) p = 0 := by
  simp [mixedDerivative]

/-- The optical lower bound with a material cost. -/
def N04RealizationOpticalObligation : Prop :=
  ∀ W : N04RealizationStart, ∃ κ : ℝ, 0 < κ ∧
    ∀ m x, x ∈ Ioo (W.C.left m) (W.C.right m) →
      κ⁻¹ * W.T.E0 (W.T.sample (W.C.cell m)) ^ (-κ) *
        min (x - W.C.left m) (W.C.right m - x) ≤ -deriv W.D.w x / (x * W.D.w x)

/-- One reference family, then for every positive transport family that is
the identity at the reference state and every smaller neighborhood carrying
the geometry, one auxiliary column with all reference clauses. -/
def N04RealizationReferenceObligation : Prop :=
  ∀ (W : N04RealizationStart) (X : N04RealizationChoice W),
  ∃ Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ,
    N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H ∧
    ∀ (e : ℕ ≃ N04WholePieceIndex W.D)
      (τ σ : (AnnularState W.S × ℝ) →
        N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint)
      (Q : (AnnularState W.S × ℝ) →
        N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ)
      (F : Set ℝ) (buffer : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) F),
      (∀ i, τ (W.C.referenceState, 0) i = id ∧ σ (W.C.referenceState, 0) i = id ∧
        Q (W.C.referenceState, 0) i = (fun _ => (1 : ℝ))) →
      ∀ (b' : ℕ) (ε' : ℝ), W.base ≤ b' → 0 < ε' → ε' ≤ W.ε →
      let V := n04RealizationAtlas W X e Y H τ σ Q buffer.region
      CanonicalGeometry W.D W.S W.C V b' ε' → ReferenceRadial W.S W.C V →
      ∃ η : (W.S.height (3 / 4 : ℝ)).Space,
        let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
        let C' := geometryReplaceAuxiliaryColumn W.C η
        let L' := correctionReplaceAuxiliaryColumn W.L η
        let V' := canonicalReplaceAuxiliaryColumn V η
        IsPhysicalSpaces W.D W.U S' ∧
        ReferencePrincipal W.U S' C' V' ∧
        ReferenceJets W.D W.U S' C' L' V' ∧
        AuxiliaryColumnGauge S' V' ∧
        (∀ z ∈ sectorNeighborhood S' b' ε' ε', ∀ m,
          ContDiffOn ℝ ∞ (atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m
            .auxiliaryColumn) unitStrip ∧
          ∀ p ∈ unitStrip,
            atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m .auxiliaryColumn
                (p + (0, Real.pi)) =
              atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m .auxiliaryColumn p) ∧
        (∀ z ∈ sectorNeighborhood S' b' ε' ε', ∀ m i j (p : unitStrip),
          differenceJets W.D W.U S' C' L' V' z .auxiliaryColumn m i j p = 0)

/-- One positive transport family with its matching on a smaller
neighborhood, and the current jets of every non-auxiliary atom of the
resulting atlas, for every auxiliary column. -/
def N04RealizationCurrentObligation : Prop :=
  ∀ (W : N04RealizationStart) (X : N04RealizationChoice W)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ),
    N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H →
  ∀ (e : ℕ ≃ N04WholePieceIndex W.D)
    (B : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi)),
  ∃ newBase : ℕ, ∃ ε' : ℝ, W.base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ W.ε ∧
  ∃ (lower upper : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ)
    (τ σ : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ),
    (∀ z ∈ stateNeighborhood W.S W.C newBase ε', stateSector W.S z.1 → ∀ i,
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
        (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (lower i) (upper i)) ∧
    (∀ i, τ (W.C.referenceState, 0) i = id ∧ σ (W.C.referenceState, 0) i = id ∧
      Q (W.C.referenceState, 0) i = (fun _ => (1 : ℝ))) ∧
    ∀ η : (W.S.height (3 / 4 : ℝ)).Space,
      let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
      let C' := geometryReplaceAuxiliaryColumn W.C η
      let L' := correctionReplaceAuxiliaryColumn W.L η
      let V' := canonicalReplaceAuxiliaryColumn
        (n04RealizationAtlas W X e Y H τ σ Q B.region) η
      ∀ a : Atom, a ≠ .auxiliaryColumn → ¬ atomIsStatic a →
        (∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m,
          ContDiffOn ℝ ∞ (atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a)
            unitStrip ∧
          ∀ q ∈ unitStrip,
            atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a (q + (0, Real.pi)) =
              atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a q) ∧
        ∃ J : ∀ m i j (q : unitStrip),
            SmoothDirections (sectorNeighborhood S' newBase ε' ε')
              (fun z => differenceJets W.D W.U S' C' L' V' z a m i j q),
          (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m (q : unitStrip) i j, i + j ≤ s →
              |differenceJets W.D W.U S' C' L' V' z a m i j q| ≤
                B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                  W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                    parameterGrading S' (s + loss) z) ∧
          ∀ k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ v : Fin k → Parameter S',
              ∀ m (q : unitStrip) i j, i + j ≤ s →
                |(J m i j q).D k z v| ≤
                  B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                    W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                      oneHighVariationWeight (parameterGrading S') newBase (s + loss) z v

/-- The bounded sample displacement of the reference-gauged atlas. -/
def N04RealizationSampleObligation : Prop :=
  ∀ (W : N04RealizationStart) (X : N04RealizationChoice W)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (τ σ : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ)
    (N : Set ℝ),
    let V := n04RealizationAtlas W X e Y H τ σ Q N
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z m p, p ∈ physicalPieceOpen W.S V z m →
      endpointX 1 (Statements.endpointDistance W.D (W.T.sample (V.cell m))) ≤
        endpointX 1 (Statements.endpointDistance W.D p.1) + A

/-- The choices after the start exist, given the optical obligation. -/
theorem n04RealizationChoice_nonempty (hopt : N04RealizationOpticalObligation)
    (W : N04RealizationStart) : Nonempty (N04RealizationChoice W) := by
  have hD : IsAccumulatingProfile W.D := W.radial.1
  have hf : Continuous (deriv W.D.w) :=
    (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
  have he₀ := n04b_exists_piece_enumeration (D := W.D) hf
  have hcell := exists_wholePositive_midpoint_material_cells W.hT hD
  have hκ := hopt W
  exact ⟨⟨hκ.choose, hκ.choose_spec.1, hκ.choose_spec.2, he₀.some, hcell.choose,
    hcell.choose_spec.1, fun i => (n04Coordinates_exists_wholePositive_endpoint_fields
      W.hT W.hS W.through03 W.field he₀.some i).choose⟩⟩

/-- The current jets of the replaced atlas: the auxiliary atom from the
reference obligation, every other atom from the current obligation. -/
theorem n04Realization_currentJets_of_parts
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (τ σ : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (η : (W.S.height (3 / 4 : ℝ)).Space) (newBase : ℕ) (ε' : ℝ)
    (hauxReg : ∀ z ∈ sectorNeighborhood (physicalSpacesReplaceAuxiliaryColumn W.S η)
        newBase ε' ε', ∀ m,
      ContDiffOn ℝ ∞ (atom W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
        (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
        (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
        (liftSectorParameter (physicalSpacesReplaceAuxiliaryColumn W.S η)
          (geometryReplaceAuxiliaryColumn W.C η) z) m .auxiliaryColumn) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
          (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
          (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
          (liftSectorParameter (physicalSpacesReplaceAuxiliaryColumn W.S η)
            (geometryReplaceAuxiliaryColumn W.C η) z) m .auxiliaryColumn (p + (0, Real.pi)) =
        atom W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
          (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
          (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
          (liftSectorParameter (physicalSpacesReplaceAuxiliaryColumn W.S η)
            (geometryReplaceAuxiliaryColumn W.C η) z) m .auxiliaryColumn p)
    (hauxZero : ∀ z ∈ sectorNeighborhood (physicalSpacesReplaceAuxiliaryColumn W.S η)
        newBase ε' ε', ∀ m i j (p : unitStrip),
      differenceJets W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
        (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
        (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
        z .auxiliaryColumn m i j p = 0)
    (hother : let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
      let C' := geometryReplaceAuxiliaryColumn W.C η
      let L' := correctionReplaceAuxiliaryColumn W.L η
      let V' := canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η
      ∀ a : Atom, a ≠ .auxiliaryColumn → ¬ atomIsStatic a →
        (∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m,
          ContDiffOn ℝ ∞ (atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a)
            unitStrip ∧
          ∀ q ∈ unitStrip,
            atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a (q + (0, Real.pi)) =
              atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a q) ∧
        ∃ J : ∀ m i j (q : unitStrip),
            SmoothDirections (sectorNeighborhood S' newBase ε' ε')
              (fun z => differenceJets W.D W.U S' C' L' V' z a m i j q),
          (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m (q : unitStrip) i j, i + j ≤ s →
              |differenceJets W.D W.U S' C' L' V' z a m i j q| ≤
                B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                  W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                    parameterGrading S' (s + loss) z) ∧
          ∀ k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ v : Fin k → Parameter S',
              ∀ m (q : unitStrip) i j, i + j ≤ s →
                |(J m i j q).D k z v| ≤
                  B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                    W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                      oneHighVariationWeight (parameterGrading S') newBase (s + loss) z v)
    (hrefReg : ∀ m (a : Atom),
      ContDiffOn ℝ ∞ (atom W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
        (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
        (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
        (W.C.referenceState, 0) m a) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
          (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
          (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
          (W.C.referenceState, 0) m a (p + (0, Real.pi)) =
        atom W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
          (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
          (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
          (W.C.referenceState, 0) m a p) :
    CurrentJets W.D W.U (physicalSpacesReplaceAuxiliaryColumn W.S η)
      (geometryReplaceAuxiliaryColumn W.C η) (correctionReplaceAuxiliaryColumn W.L η)
      (canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η)
      newBase ε' := by
  classical
  let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
  let C' := geometryReplaceAuxiliaryColumn W.C η
  let L' := correctionReplaceAuxiliaryColumn W.L η
  let V' := canonicalReplaceAuxiliaryColumn (n04RealizationAtlas W X e Y H τ σ Q N) η
  have hD : IsAccumulatingProfile W.D := W.radial.1
  have hU : IsMaterialData W.D W.U := isMaterialData_enlargedMaterialData hD W.hT
  have hfloor : ∀ m, 1 ≤ W.U.E0 (W.U.sample (V'.cell m)) := fun m =>
    (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hopen : IsOpen (sectorNeighborhood S' newBase ε' ε') :=
    isOpen_sectorNeighborhood S' newBase ε' ε'
  have hall : ∀ a : Atom,
      (∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m,
        ContDiffOn ℝ ∞ (atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a)
          unitStrip ∧
        ∀ q ∈ unitStrip,
          atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a (q + (0, Real.pi)) =
            atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a q) ∧
      ∃ J : ∀ m i j (q : unitStrip),
          SmoothDirections (sectorNeighborhood S' newBase ε' ε')
            (fun z => differenceJets W.D W.U S' C' L' V' z a m i j q),
        (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
          ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m (q : unitStrip) i j, i + j ≤ s →
            |differenceJets W.D W.U S' C' L' V' z a m i j q| ≤
              B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                  parameterGrading S' (s + loss) z) ∧
        ∀ k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
          ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ v : Fin k → Parameter S',
            ∀ m (q : unitStrip) i j, i + j ≤ s →
              |(J m i j q).D k z v| ≤
                B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                  W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                    oneHighVariationWeight (parameterGrading S') newBase (s + loss) z v := by
    intro a
    have hcost : ∀ m, 0 ≤ 1 * W.U.E0 (W.U.sample (V'.cell m)) ^ (1 : ℝ) *
        W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) := fun m =>
      mul_nonneg (mul_nonneg zero_le_one
        (Real.rpow_nonneg (zero_le_one.trans (hfloor m)) _))
        (Real.rpow_nonneg
          (hU.2.1 _ (materialSample_mem_interval hD hU (V'.cell m))).2.1.le _)
    have hzero : (∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m i j (q : unitStrip),
        differenceJets W.D W.U S' C' L' V' z a m i j q = 0) →
        ∃ J : ∀ m i j (q : unitStrip),
            SmoothDirections (sectorNeighborhood S' newBase ε' ε')
              (fun z => differenceJets W.D W.U S' C' L' V' z a m i j q),
          (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ m (q : unitStrip) i j, i + j ≤ s →
              |differenceJets W.D W.U S' C' L' V' z a m i j q| ≤
                B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                  W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                    parameterGrading S' (s + loss) z) ∧
          ∀ k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ z ∈ sectorNeighborhood S' newBase ε' ε', ∀ v : Fin k → Parameter S',
              ∀ m (q : unitStrip) i j, i + j ≤ s →
                |(J m i j q).D k z v| ≤
                  B * W.U.E0 (W.U.sample (V'.cell m)) ^ B *
                    W.U.H (W.U.sample (V'.cell m)) ^ (3 / 4 : ℝ) *
                      oneHighVariationWeight (parameterGrading S') newBase (s + loss) z v := by
      intro hz0
      refine ⟨fun m i j q => (smoothDirections_constant hopen (0 : ℝ)).congrOn
        (fun z hz => (hz0 z hz m i j q).symm), ⟨0, fun s => ⟨1, one_pos, ?_⟩⟩,
        fun k => ⟨0, fun s => ⟨1, one_pos, ?_⟩⟩⟩
      · intro z hz m q i j _
        rw [hz0 z hz m i j q, abs_zero]
        exact mul_nonneg (hcost m) (apply_nonneg _ _)
      · intro z hz v m q i j _
        have hD0 : ((smoothDirections_constant hopen (0 : ℝ)).congrOn
            (fun z hz => (hz0 z hz m i j q).symm)).D k z v = 0 := by
          by_cases hk : k = 0
          · subst k
            exact smoothDirections_D_zero_apply (smoothDirections_constant hopen (0 : ℝ)) hz v
          · exact smoothDirections_D_constant (smoothDirections_constant hopen (0 : ℝ))
              (Nat.pos_of_ne_zero hk) hz v
        rw [hD0, abs_zero]
        exact mul_nonneg (hcost m) (oneHighVariationWeight_nonneg _ _ _ _ _)
    by_cases ha : a = .auxiliaryColumn
    · subst ha
      exact ⟨hauxReg, hzero hauxZero⟩
    by_cases hs : atomIsStatic a
    · have hsame : ∀ (z : Parameter S') m,
          atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a =
            atom W.D W.U S' C' L' V' (C'.referenceState, 0) m a :=
        fun z m => atom_state_eq_of_static hs _ _ m
      refine ⟨fun z _ m => ?_, hzero fun z _ m i j q => ?_⟩
      · rw [hsame z m]
        exact hrefReg m a
      · have hfun : (fun q : PolarPoint =>
            atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a q -
              atom W.D W.U S' C' L' V' (C'.referenceState, 0) m a q) = fun _ => 0 := by
          funext q
          rw [hsame z m, sub_self]
        change mixedDerivative i j (fun q : PolarPoint =>
            atom W.D W.U S' C' L' V' (liftSectorParameter S' C' z) m a q -
              atom W.D W.U S' C' L' V' (C'.referenceState, 0) m a q) q.val = 0
        rw [hfun]
        exact mixedDerivative_fun_zero i j q.val
    · exact hother a ha hs
  exact n04Realization_currentJets_of_atomFamilies hD hU hfloor (fun a => (hall a).1)
    (fun a => (hall a).2.choose) (fun a => (hall a).2.choose_spec.1)
    (fun a => (hall a).2.choose_spec.2)

/-- The Realization conclusion from the four obligations, on one witness. -/
theorem n04Realization_of_obligations
    (hopt : N04RealizationOpticalObligation)
    (hrefO : N04RealizationReferenceObligation)
    (hcurO : N04RealizationCurrentObligation)
    (hsampO : N04RealizationSampleObligation) :
    N04cStatement := by
  have W : N04RealizationStart := n04RealizationStart_nonempty.some
  have X : N04RealizationChoice W := (n04RealizationChoice_nonempty hopt W).some
  have hD : IsAccumulatingProfile W.D := W.radial.1
  have hborder : RadialTrueBorder W.D := W.radial.2.2.2.1
  have hf : Continuous (deriv W.D.w) :=
    (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
  have e : ℕ ≃ N04WholePieceIndex W.D := (n04WholePiece_exists_enumeration (D := W.D) hf).some
  have B : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi) :=
    (n04PositiveNormalizationBuffer_nonempty hf hborder.2.1 hborder.2.2.1).some
  have href := hrefO W X
  let Y := href.choose
  let H := href.choose_spec.choose
  have hfam : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H :=
    href.choose_spec.choose_spec.1
  have hrefJ := href.choose_spec.choose_spec.2
  have hcur := hcurO W X Y H hfam e B
  let newBase := hcur.choose
  let ε' := hcur.choose_spec.choose
  have hcur1 := hcur.choose_spec.choose_spec
  have hb : W.base ≤ newBase := hcur1.1
  have hε' : 0 < ε' := hcur1.2.1
  have hε'ε : ε' ≤ W.ε := hcur1.2.2.1
  have hcur2 := hcur1.2.2.2
  let lower := hcur2.choose
  let upper := hcur2.choose_spec.choose
  let τ := hcur2.choose_spec.choose_spec.choose
  let σ := hcur2.choose_spec.choose_spec.choose_spec.choose
  let Q := hcur2.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hcur3 := hcur2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hmatch := hcur3.1
  have hid := hcur3.2.1
  have hother := hcur3.2.2
  let V := n04RealizationAtlas W X e Y H τ σ Q B.region
  have hgeo := n04Realization_gaugeAtlas_of_family W.hT W.hS W.through03 W.field X.e₀ e
    X.cell X.src B Y H hfam τ σ Q lower upper hb hε' hε'ε hmatch hid
  have hV : CanonicalGeometry W.D W.S W.C V newBase ε' := hgeo.1
  have hcut : CanonicalCutOperatorProperties W.S W.C W.L V newBase ε' := hgeo.2.1
  have hradial : ReferenceRadial W.S W.C V := hgeo.2.2.2.1
  have htrans : TransmissionGeometry W.D W.S W.C V newBase ε' := hgeo.2.2.2.2.1
  have hqual := hgeo.2.2.2.2.2
  have hη := hrefJ e τ σ Q (tsupport W.D.chi) B hid newBase ε' hb hε' hε'ε hV hradial
  let η := hη.choose
  have hηs := hη.choose_spec
  let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
  let C' := geometryReplaceAuxiliaryColumn W.C η
  let R' := returnReplaceAuxiliaryColumn W.R η
  let L' := correctionReplaceAuxiliaryColumn W.L η
  let V' := canonicalReplaceAuxiliaryColumn V η
  have hS' : IsPhysicalSpaces W.D W.U S' := hηs.1
  have hprin : ReferencePrincipal W.U S' C' V' := hηs.2.1
  have hrefjets : ReferenceJets W.D W.U S' C' L' V' := hηs.2.2.1
  have hgauge : AuxiliaryColumnGauge S' V' := hηs.2.2.2.1
  have hU : IsMaterialData W.D W.U := isMaterialData_enlargedMaterialData hD W.hT
  have hfloor : ∀ r : ℝ, 1 ≤ W.U.E0 r := fun r =>
    (W.floor r).trans (le_enlargedMaterialData_E0 W.T r)
  have h03 : NonlinearPropertiesThrough03 W.D W.U S' C' R' L' newBase W.loss ε' :=
    nonlinearThrough03_replaceAuxiliaryColumn
      (nonlinearPropertiesThrough03_enlargedMaterialData W.hT
        (nonlinearPropertiesThrough03_restrict W.hT W.through03 hb le_rfl hε' hε'ε)) η
  have hsub := stateNeighborhood_mono W.S W.C hb hε'ε
  have hfield0 : N04bFieldRegularity W.D W.S W.C W.L newBase ε' :=
    { smooth_coefficients := fun z hz => W.field.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => W.field.periodic_coefficients z (hsub hz)
      reference_flow := W.field.reference_flow
      positive_a := fun z hz => W.field.positive_a z (hsub hz)
      negative_discriminant := fun z hz => W.field.negative_discriminant z (hsub hz) }
  have hfield' : N04bFieldRegularity W.D S' C' L' newBase ε' :=
    fieldRegularity_replaceAuxiliaryColumn η hfield0
  have hA' : N04PartA W.D S' C' V' newBase ε' := canonicalGeometry_replaceAuxiliaryColumn hV η
  have hB' : N04PartB S' C' L' V' newBase ε' := cutOperator_replaceAuxiliaryColumn η hcut
  have hcurrent : CurrentJets W.D W.U S' C' L' V' newBase ε' :=
    n04Realization_currentJets_of_parts W X e Y H τ σ Q B.region η newBase ε'
      hηs.2.2.2.2.1 hηs.2.2.2.2.2 (hother η) hrefjets.1
  have hprim : PrimitiveGeometryProperties W.D W.U S' C' L' V' newBase ε' :=
    ⟨referenceRadial_replaceAuxiliaryColumn η hradial, hprin, hrefjets, hcurrent, hgauge,
      transmissionGeometry_replaceAuxiliaryColumn η htrans⟩
  have hqual' := transportQualitative_replaceAuxiliaryColumn (D := W.D) (K := V) η
    (fun z hz hs => ⟨_, _, hqual z hz hs⟩)
  have hsamp := hsampO W X e Y H τ σ Q B.region
  have hshift : ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ stateNeighborhood W.S W.C newBase ε',
      stateSector W.S z.1 → ∀ m x, x ∈ physicalPieceOpen W.S V z m →
        endpointX 1 (Statements.endpointDistance W.D (W.U.sample (V.cell m))) ≤
          endpointX 1 (Statements.endpointDistance W.D x.1) + A :=
    ⟨hsamp.choose, hsamp.choose_spec.1, fun z _ _ m x hx => hsamp.choose_spec.2 z m x hx⟩
  have hshift' := sampleShift_replaceAuxiliaryColumn (D := W.D) (T := W.U) η hshift
  have hfinal := n04Realization_sameWitnessCompletion hU h03 hA' hB' hprim hfield' hfloor
    hqual' hshift'
  let base' := hfinal.choose
  let loss' := hfinal.choose_spec.choose
  have hf1 := hfinal.choose_spec.choose_spec.2.2
  let η' := hf1.choose
  have hf2 := hf1.choose_spec
  exact ⟨⟨W.D, W.radial⟩, W.U, S', C', R', L', normalizedCanonicalData S' V', base', loss', η',
    hU, hS', hf2.2.2.1, hf2.2.2.2.1, hf2.2.2.2.2.1, hf2.2.2.2.2.2⟩

end ContinuousFlexibility.Analysis
