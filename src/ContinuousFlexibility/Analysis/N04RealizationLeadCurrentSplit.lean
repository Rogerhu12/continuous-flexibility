import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction

/-!
# The current obligation split along the canonical formulas

Every canonical atom at a canonical unit point `y` is a fixed formula in the
inverse chart point `G y`, the height, the chart Jacobian, the physical
coefficients and the physical columns at that point. The split therefore has
an interface of pulled families:

* the inverse chart (its two atoms), the pulled height `h (G y)`,
* the pulled physical coefficients `a, b, c` at `G y`,
* the pulled left and `ν` columns at `G y`,

together with the forward chart, height and Jacobian atoms.

* `N04RealizationPositiveGeometryObligation`: one positive transport family
  with its matching, and the eight geometry atoms and the pulled height on
  positive pieces;
* `N04RealizationNegativeGeometryObligation`: the same on negative pieces;
* `N04RealizationPulledFieldObligation`: the pulled coefficients and columns
  on all pieces, given the inverse chart;
* `N04RealizationSourceColumnObligation`: the source factors and both
  columns, given the interface;
* `N04RealizationPrincipalObligation`: the principal coefficients, the
  potential and the divided coefficients, given the interface.

`n04Realization_currentObligation_of_split` proves the current obligation
from these five statements.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
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

/-- The forward and inverse chart, height and Jacobian atoms. -/
def atomIsGeometry : Atom → Prop
  | .chartRadial | .chartAngleDefect | .inverseRadial | .inverseAngleDefect
  | .height | .heightInverse | .jacobian | .jacobianInverse => True
  | _ => False

/-- The source factors and the two scalar columns. -/
def atomIsSourceColumn : Atom → Prop
  | .sourceFactor | .sourceFactorInverse | .leftColumn | .nuColumn => True
  | _ => False

/-- The principal coefficients, the potential and the divided coefficients. -/
def atomIsPrincipal : Atom → Prop
  | .principalA | .principalAInverse | .principalB | .principalC | .potential
  | .dividedA | .dividedB | .dividedC => True
  | _ => False

theorem atom_classification (a : Atom) (ha : a ≠ .auxiliaryColumn) (hs : ¬ atomIsStatic a) :
    atomIsGeometry a ∨ atomIsSourceColumn a ∨ atomIsPrincipal a := by
  cases a <;> first
    | exact Or.inl trivial
    | exact Or.inr (Or.inl trivial)
    | exact Or.inr (Or.inr trivial)
    | exact absurd rfl ha
    | exact absurd trivial hs

/-- The data of the reference-gauged atlas before the auxiliary column. -/
structure N04RealizationGauge where
  W : N04RealizationStart
  X : N04RealizationChoice W
  e : ℕ ≃ N04WholePieceIndex W.D
  Y : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ
  H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ
  τ : (AnnularState W.S × ℝ) →
    N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint
  σ : (AnnularState W.S × ℝ) →
    N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint
  Q : (AnnularState W.S × ℝ) →
    N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ
  N : Set ℝ

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- The replaced physical spaces. -/
abbrev S : PhysicalSpacesData := physicalSpacesReplaceAuxiliaryColumn G.W.S η
/-- The replaced control geometry. -/
abbrev C : NonlinearGeometryData (G.S η) := geometryReplaceAuxiliaryColumn G.W.C η
/-- The replaced correction field. -/
abbrev L : ReturnCorrectionData (G.S η) := correctionReplaceAuxiliaryColumn G.W.L η
/-- The replaced reference-gauged atlas. -/
abbrev V : CanonicalData (G.S η) :=
  canonicalReplaceAuxiliaryColumn (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) η
/-- The state of a sector parameter. -/
abbrev lift (z : Parameter (G.S η)) : AnnularState (G.S η) × ℝ :=
  liftSectorParameter (G.S η) (G.C η) z
/-- The reference state. -/
abbrev ref : AnnularState (G.S η) × ℝ := ((G.C η).referenceState, 0)

/-- Jet-difference data of the replaced atlas on pieces satisfying `P`. -/
abbrev Data (P : ℕ → Prop) (b : ℕ) (ε : ℝ)
    (f : Parameter (G.S η) → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  CurrentJetDataOn (G.S η) G.W.U (G.V η).cell P b ε f f₀

/-- The current family of an atom. -/
def atomFamily (a : Atom) : Parameter (G.S η) → ℕ → PolarPoint → ℝ := fun z m =>
  atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) (G.lift η z) m a

/-- The reference family of an atom. -/
def atomRef (a : Atom) : ℕ → PolarPoint → ℝ := fun m =>
  atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) (G.ref η) m a

/-- The inverse-chart point of a canonical unit point. -/
def pulledPoint (w : AnnularState (G.S η) × ℝ) (m : ℕ) (y : PolarPoint) : PolarPoint :=
  (G.V η).inverseChart w m (canonicalUnitPoint (G.V η) m y)

/-- A physical field family pulled back by the inverse chart. -/
def pulled (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ) :
    Parameter (G.S η) → ℕ → PolarPoint → ℝ := fun z m y =>
  F (G.lift η z) (G.pulledPoint η (G.lift η z) m y)

/-- The same physical field family pulled back at the reference state. -/
def pulledRef (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ) : ℕ → PolarPoint → ℝ :=
  fun m y => F (G.ref η) (G.pulledPoint η (G.ref η) m y)

/-- The height of a piece, as a physical field of the state. -/
def heightField (m : ℕ) : AnnularState (G.S η) × ℝ → PolarPoint → ℝ := fun w =>
  (G.V η).height w m

/-- The pulled height `h (G y)`. -/
def pulledHeight : Parameter (G.S η) → ℕ → PolarPoint → ℝ := fun z m y =>
  G.heightField η m (G.lift η z) (G.pulledPoint η (G.lift η z) m y)

/-- The pulled height at the reference state. -/
def pulledHeightRef : ℕ → PolarPoint → ℝ := fun m y =>
  G.heightField η m (G.ref η) (G.pulledPoint η (G.ref η) m y)

/-- A physical coefficient field. -/
def coefficientField (c : Fin 3) : AnnularState (G.S η) × ℝ → PolarPoint → ℝ := fun w =>
  canonicalCoefficientComponent c ((G.L η).coefficients w)

/-- The physical left column field. -/
def leftColumnField : AnnularState (G.S η) × ℝ → PolarPoint → ℝ := fun w =>
  divergenceOperator ((G.L η).coefficients w) (fun q => (G.S η).chiLeft q.1)

/-- The physical `ν` column field. -/
def nuField : AnnularState (G.S η) × ℝ → PolarPoint → ℝ := fun w =>
  nuColumnField G.W.D (G.S η) (G.C η) w

/-- Positive pieces. -/
def Pos (m : ℕ) : Prop := (G.V η).positive m = true
/-- Negative pieces. -/
def Neg (m : ℕ) : Prop := (G.V η).positive m = false

/-- The positive family is admissible on a neighborhood: it is the identity at
the reference state and matches the actual endpoint sources there. -/
def Admissible (b : ℕ) (ε : ℝ) : Prop :=
  G.W.base ≤ b ∧ 0 < ε ∧ ε ≤ G.W.ε ∧
  N04PositiveReferenceFamily (G.W.A G.X.e₀) G.X.src 4 G.Y G.H ∧
  (∀ i, G.τ (G.W.C.referenceState, 0) i = id ∧ G.σ (G.W.C.referenceState, 0) i = id ∧
    G.Q (G.W.C.referenceState, 0) i = (fun _ => (1 : ℝ))) ∧
  ∃ (B : N04PositiveNormalizationBuffer G.W.D.a G.W.D.b (deriv G.W.D.w) (tsupport G.W.D.chi))
    (lower upper : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w) → ℝ),
    G.N = B.region ∧
    ∀ z ∈ stateNeighborhood G.W.S G.W.C b ε, stateSector G.W.S z.1 → ∀ i,
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (G.X.src i side) (G.W.A G.X.e₀) z)
        (fun side => n04PositiveSourceHeight (G.X.src i side) (G.W.A G.X.e₀) z)
        (G.τ z i) (G.σ z i) (G.Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (lower i) (upper i)

/-- The geometry part of the interface on pieces satisfying `P`. -/
def GeometryData (P : ℕ → Prop) (b : ℕ) (ε : ℝ) : Prop :=
  (∀ a : Atom, atomIsGeometry a → G.Data η P b ε (G.atomFamily η a) (G.atomRef η a)) ∧
    G.Data η P b ε (G.pulledHeight η) (G.pulledHeightRef η)

/-- The pulled physical fields of the interface on all pieces. -/
def FieldData (b : ℕ) (ε : ℝ) : Prop :=
  (∀ c : Fin 3, G.Data η (fun _ => True) b ε (G.pulled η (G.coefficientField η c))
    (G.pulledRef η (G.coefficientField η c))) ∧
  G.Data η (fun _ => True) b ε (G.pulled η (G.leftColumnField η))
    (G.pulledRef η (G.leftColumnField η)) ∧
  G.Data η (fun _ => True) b ε (G.pulled η (G.nuField η)) (G.pulledRef η (G.nuField η))

end N04RealizationGauge

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem cost_nonneg (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    (∀ m, 0 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m))) ∧
      (∀ m, 0 ≤ G.W.U.H (G.W.U.sample ((G.V η).cell m))) ∧
      (∀ m, 1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m))) := by
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hU : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have h1 : ∀ m, 1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) := fun m =>
    (G.W.floor _).trans (le_enlargedMaterialData_E0 G.W.T _)
  exact ⟨fun m => zero_le_one.trans (h1 m),
    fun m => (hU.2.1 _ (materialSample_mem_interval hD hU ((G.V η).cell m))).2.1.le, h1⟩

theorem geometryData_mono (η : (G.W.S.height (3 / 4 : ℝ)).Space) {P P' : ℕ → Prop}
    {b b' : ℕ} {ε ε' : ℝ} (h : G.GeometryData η P b ε) (hP : ∀ m, P' m → P m)
    (hb : b ≤ b') (hε : ε' ≤ ε) : G.GeometryData η P' b' ε' :=
  ⟨fun a ha => (h.1 a ha).mono hP hb hε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1,
    h.2.mono hP hb hε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1⟩

theorem fieldData_mono (η : (G.W.S.height (3 / 4 : ℝ)).Space) {b b' : ℕ} {ε ε' : ℝ}
    (h : G.FieldData η b ε) (hb : b ≤ b') (hε : ε' ≤ ε) : G.FieldData η b' ε' :=
  ⟨fun c => (h.1 c).mono (fun _ h => h) hb hε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1,
    h.2.1.mono (fun _ h => h) hb hε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1,
    h.2.2.mono (fun _ h => h) hb hε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1⟩

theorem geometryData_union (η : (G.W.S.height (3 / 4 : ℝ)).Space) {b : ℕ} {ε : ℝ}
    (hp : G.GeometryData η (G.Pos η) b ε) (hn : G.GeometryData η (G.Neg η) b ε) :
    G.GeometryData η (fun _ => True) b ε := by
  have hcover : ∀ m, (fun _ : ℕ => True) m → G.Pos η m ∨ G.Neg η m := fun m _ =>
    (Bool.dichotomy ((G.V η).positive m)).symm
  exact ⟨fun a ha => (hp.1 a ha).union (hn.1 a ha) hcover (G.cost_nonneg η).2.2
      (G.cost_nonneg η).2.1,
    hp.2.union hn.2 hcover (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1⟩

theorem admissible_mono {b b' : ℕ} {ε ε' : ℝ} (h : G.Admissible b ε) (hb : b ≤ b')
    (hε' : 0 < ε') (hε : ε' ≤ ε) : G.Admissible b' ε' := by
  have hm := h.2.2.2.2.2
  exact ⟨h.1.trans hb, hε', hε.trans h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hm.choose,
    hm.choose_spec.choose, hm.choose_spec.choose_spec.choose,
    hm.choose_spec.choose_spec.choose_spec.1, fun z hz hs i =>
      hm.choose_spec.choose_spec.choose_spec.2 z
        (stateNeighborhood_mono G.W.S G.W.C hb hε hz) hs i⟩

end N04RealizationGauge

/-- One positive transport family with its matching on a smaller neighborhood,
and the geometry interface on positive pieces. -/
def N04RealizationPositiveGeometryObligation : Prop :=
  ∀ (W : N04RealizationStart) (X : N04RealizationChoice W)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ),
    N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H →
  ∀ (e : ℕ ≃ N04WholePieceIndex W.D)
    (B : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi)),
  ∃ (b : ℕ) (ε : ℝ) (lower upper : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ)
    (τ σ : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState W.S × ℝ) →
      N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → PolarPoint → ℝ),
    W.base ≤ b ∧ 0 < ε ∧ ε ≤ W.ε ∧
    (∀ z ∈ stateNeighborhood W.S W.C b ε, stateSector W.S z.1 → ∀ i,
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
        (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (lower i) (upper i)) ∧
    (∀ i, τ (W.C.referenceState, 0) i = id ∧ σ (W.C.referenceState, 0) i = id ∧
      Q (W.C.referenceState, 0) i = (fun _ => (1 : ℝ))) ∧
    ∀ η, (N04RealizationGauge.mk W X e Y H τ σ Q B.region).GeometryData η
      ((N04RealizationGauge.mk W X e Y H τ σ Q B.region).Pos η) b ε

/-- The geometry interface on negative pieces. -/
def N04RealizationNegativeGeometryObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ η, G.GeometryData η (G.Neg η) b' ε'

/-- The pulled physical coefficients and columns, given the geometry interface. -/
def N04RealizationPulledFieldObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, G.GeometryData η (fun _ => True) b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ η, G.FieldData η b' ε'

/-- The source factors and both scalar columns, given the interface. -/
def N04RealizationSourceColumnObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, G.GeometryData η (fun _ => True) b ε) → (∀ η, G.FieldData η b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ η,
      ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) →
      ∀ a : Atom, atomIsSourceColumn a →
        G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a)

/-- The principal coefficients, the potential and the divided coefficients,
given the interface. -/
def N04RealizationPrincipalObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, G.GeometryData η (fun _ => True) b ε) → (∀ η, G.FieldData η b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ η,
      ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) →
      ∀ a : Atom, atomIsPrincipal a →
        G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a)

end ContinuousFlexibility.Analysis
