module

public import ContinuousFlexibility.Analysis.N04NegativeChartData
public import ContinuousFlexibility.Analysis.N04NegativeChartReindex
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeGeometryJets
public import ContinuousFlexibility.Analysis.N04SourceColumnsData

/-!
# Reference coefficients for the selected negative chart calculus

The existing material estimates are evaluated on the same retained atlas
and its original half sample. Only the auxiliary column is replaced, and
none of the geometric atoms depends on it. The negative enumeration lets
the scalar product and reciprocal calculus use these actual reference jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry
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

variable (G : N04RealizationGauge)

/-- The original negative reference-jet theorem supplies one coefficient
before every negative piece and every geometric atom. -/
theorem negative_geometry_reference_bounds
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m, G.Neg η m → ∀ a : Atom, atomIsGeometry a →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (G.atomRef η a m) q| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hb := n04WholeReferenceGauge_negative_geometryReferenceJets_enlargedMaterialData
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.X.κ_pos s
  let V := n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N
  have hoptical : ∀ m, ∃ j, Ioo (G.W.C.left m) (G.W.C.right m) ⊆ G.W.D.cells j ∧
      ∀ r ∈ Ioo (G.W.C.left m) (G.W.C.right m),
        G.X.κ⁻¹ * G.W.T.E0 (G.W.T.sample j) ^ (-G.X.κ) *
          min (r - G.W.C.left m) (G.W.C.right m - r) ≤
            -deriv G.W.D.w r / (r * G.W.D.w r) :=
    fun m => ⟨G.W.C.cell m, G.W.host m, G.X.optical m⟩
  have hraw := hb.choose_spec.2 G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N hoptical
  refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
  intro m hm a ha q hq i j hij
  have hne : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    exact ha
  have hcase : a = .chartRadial ∨ a = .chartAngleDefect ∨ a = .inverseRadial ∨
      a = .inverseAngleDefect ∨ a = .height ∨ a = .heightInverse ∨
      a = .jacobian ∨ a = .jacobianInverse ∨ a = .sourceFactor ∨ a = .sourceFactorInverse := by
    cases a <;> simp_all only [atomIsGeometry, or_self, or_true, true_or, reduceCtorEq]
  have he : G.atomRef η a m =
      atom G.W.D G.W.U G.W.S G.W.C G.W.L V (G.W.C.referenceState, 0) m a :=
    canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L V
      η (G.W.C.referenceState, 0) m a hne
  exact (congrArg (fun f : PolarPoint → ℝ => |mixedDerivative i j f q|) he).trans_le
    (hraw m hm a hcase q hq i j hij)

/-- The scalar reference interface contains only the enumerated negative
halves and keeps each of their original cells. -/
theorem negativeChart_referenceData
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) (ha : atomIsGeometry a) :
    N04SourceReferenceData G.W.U ((G.V η).cell ∘ G.negativeChartPiece)
      (fun n => G.atomRef η a (G.negativeChartPiece n)) := by
  have hz : (0 : Parameter G.W.S) ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    ⟨(sectorGrading G.W.S G.W.base).map_zero'.trans_lt G.W.ε_pos,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt G.W.ε_pos⟩
  refine ⟨fun n => ?_, fun s => ?_⟩
  · have he : G.atomFamily η a (0 : Parameter G.W.S) (G.negativeChartPiece n) =
        G.atomRef η a (G.negativeChartPiece n) :=
      congrFun (G.atomFamily_zero η a) (G.negativeChartPiece n)
    exact Eq.mp (congrArg (fun f : PolarPoint → ℝ => ContDiffOn ℝ ∞ f unitStrip ∧
      ∀ q ∈ unitStrip, f (q + (0, Real.pi)) = f q) he)
      (G.negative_geometry_spatial η 0 hz (G.negativeChartPiece n)
        (G.negativeChartPiece_negative η n) a ha)
  · have hb := G.negative_geometry_reference_bounds η s
    exact ⟨hb.choose, hb.choose_spec.1, fun n q hq i j hij =>
      hb.choose_spec.2 (G.negativeChartPiece n) (G.negativeChartPiece_negative η n)
        a ha q hq i j hij⟩

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_referenceData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_referenceData
