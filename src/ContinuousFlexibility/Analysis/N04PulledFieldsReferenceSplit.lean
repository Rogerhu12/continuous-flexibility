import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# Compatibility of a reference-aware realization split

The parent current obligation already receives quantitative reference jets
of the same atlas. The proposed split below carries that certificate through
the positive geometry and pulled-field interfaces, while choosing every
neighborhood before the auxiliary column. The original negative-geometry
obligation is reused without alteration.

This module defines proposed obligations under a separate namespace and
proves their conditional assembly into `N04RealizationCurrentObligation`.
It changes no frozen definition and does not close a blueprint node.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.PulledFieldsReferenceRepair

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

/-- The parent's quantitative reference jets for the very same atlas. This
certificate is independent of the chosen state neighborhood. -/
abbrev ReferenceData (G : N04RealizationGauge)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) : Prop :=
  ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)

/-- One positive transport family with its matching on a smaller neighborhood,
and the geometry interface on positive pieces, conditional on the reference
certificate already supplied by the parent current obligation. -/
def PositiveGeometryObligation : Prop :=
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
    ∀ η, ReferenceData (N04RealizationGauge.mk W X e Y H τ σ Q B.region) η →
      (N04RealizationGauge.mk W X e Y H τ σ Q B.region).GeometryData η
        ((N04RealizationGauge.mk W X e Y H τ σ Q B.region).Pos η) b ε

/-- Proposed pulled-field interface: the common neighborhood precedes the
auxiliary column and its same-atlas reference certificate. -/
def PulledFieldObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, ReferenceData G η → G.GeometryData η (fun _ => True) b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ η, ReferenceData G η → G.FieldData η b' ε'

/-- The source factors and both scalar columns, given the interface. -/
def SourceColumnObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, ReferenceData G η → G.GeometryData η (fun _ => True) b ε) →
    (∀ η, ReferenceData G η → G.FieldData η b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ η,
      ReferenceData G η →
      ∀ a : Atom, atomIsSourceColumn a →
        G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a)

/-- The principal coefficients, the potential and the divided coefficients,
given the interface. -/
def PrincipalObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, ReferenceData G η → G.GeometryData η (fun _ => True) b ε) →
    (∀ η, ReferenceData G η → G.FieldData η b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ η,
      ReferenceData G η →
      ∀ a : Atom, atomIsPrincipal a →
        G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a)

/-- Conditional compatibility of the proposed split with the exact unchanged
parent. This theorem proves the assembly only; it does not supply any of its
five input obligations. The negative obligation is the original frozen one. -/
theorem currentObligation_of_referenceSplit
    (hpos : PositiveGeometryObligation)
    (hneg : N04RealizationNegativeGeometryObligation)
    (hfield : PulledFieldObligation)
    (hsrc : SourceColumnObligation)
    (hprin : PrincipalObligation) :
    N04RealizationCurrentObligation := by
  intro W X Y H hfam e B
  refine (hpos W X Y H hfam e B).elim fun b h1 => h1.elim fun ε h1 => h1.elim
    fun lower h1 => h1.elim fun upper h1 => h1.elim fun τ h1 => h1.elim fun σ h1 =>
      h1.elim fun Q hp => ?_
  let G : N04RealizationGauge := ⟨W, X, e, Y, H, τ, σ, Q, B.region⟩
  have hb : W.base ≤ b := hp.1
  have hε : 0 < ε := hp.2.1
  have hεε : ε ≤ W.ε := hp.2.2.1
  have hadm : G.Admissible b ε :=
    ⟨hb, hε, hεε, hfam, hp.2.2.2.2.1, B, lower, upper, rfl, hp.2.2.2.1⟩
  have hgeoP : ∀ η, ReferenceData G η → G.GeometryData η (G.Pos η) b ε :=
    hp.2.2.2.2.2
  have h2 := hneg G b ε hadm
  let b2 := h2.choose
  let ε2 := h2.choose_spec.choose
  have hp2 := h2.choose_spec.choose_spec
  have hadm2 : G.Admissible b2 ε2 := G.admissible_mono hadm hp2.1 hp2.2.1 hp2.2.2.1
  have hgeo2 : ∀ η, ReferenceData G η → G.GeometryData η (fun _ => True) b2 ε2 :=
    fun η href =>
      G.geometryData_union η
        (G.geometryData_mono η (hgeoP η href) (fun _ h => h) hp2.1 hp2.2.2.1)
        (hp2.2.2.2 η)
  have h3 := hfield G b2 ε2 hadm2 hgeo2
  let b3 := h3.choose
  let ε3 := h3.choose_spec.choose
  have hp3 := h3.choose_spec.choose_spec
  have hadm3 : G.Admissible b3 ε3 := G.admissible_mono hadm2 hp3.1 hp3.2.1 hp3.2.2.1
  have hgeo3 : ∀ η, ReferenceData G η → G.GeometryData η (fun _ => True) b3 ε3 :=
    fun η href => G.geometryData_mono η (hgeo2 η href) (fun _ h => h) hp3.1 hp3.2.2.1
  have hfd3 : ∀ η, ReferenceData G η → G.FieldData η b3 ε3 := hp3.2.2.2
  have h4 := hsrc G b3 ε3 hadm3 hgeo3 hfd3
  have h5 := hprin G b3 ε3 hadm3 hgeo3 hfd3
  let b4 := h4.choose
  let ε4 := h4.choose_spec.choose
  have hp4 := h4.choose_spec.choose_spec
  let b5 := h5.choose
  let ε5 := h5.choose_spec.choose
  have hp5 := h5.choose_spec.choose_spec
  let nb : ℕ := max b4 b5
  let ε' : ℝ := min ε4 ε5
  have hε' : 0 < ε' := lt_min hp4.2.1 hp5.2.1
  have hε'3 : ε' ≤ ε3 := (min_le_left _ _).trans hp4.2.2.1
  have hb3 : b3 ≤ nb := hp4.1.trans (le_max_left _ _)
  have hb2 : b2 ≤ b3 := hp3.1
  have hε32 : ε3 ≤ ε2 := hp3.2.2.1
  have hε2 : ε2 ≤ ε := hp2.2.2.1
  have hbb : b ≤ b2 := hp2.1
  have hbn : b ≤ nb := hbb.trans (hb2.trans hb3)
  have hεn : ε' ≤ ε := hε'3.trans (hε32.trans hε2)
  refine ⟨nb, ε', hb.trans hbn, hε', hεn.trans hεε, lower, upper, τ, σ, Q,
    fun z hz hs i => hp.2.2.2.1 z (stateNeighborhood_mono W.S W.C hbn hεn hz) hs i,
    hp.2.2.2.2.1, ?_⟩
  intro η _ _ _ _ hrefJ a ha hs
  have hdata : G.Data η (fun _ => True) nb ε' (G.atomFamily η a) (G.atomRef η a) :=
    (atom_classification a ha hs).elim
      (fun hg => ((hgeo3 η hrefJ).1 a hg).mono (fun _ h => h) hb3 hε'3
        (G.cost_nonneg η).1 (G.cost_nonneg η).2.1)
      (fun hr => hr.elim
        (fun hsc => (hp4.2.2.2 η hrefJ a hsc).mono (fun _ h => h) (le_max_left _ _)
          (min_le_left _ _) (G.cost_nonneg η).1 (G.cost_nonneg η).2.1)
        (fun hpr => (hp5.2.2.2 η hrefJ a hpr).mono (fun _ h => h) (le_max_right _ _)
          (min_le_right _ _) (G.cost_nonneg η).1 (G.cost_nonneg η).2.1))
  have hJ := hdata.2
  have hv := hJ.choose_spec.1
  exact ⟨fun z hz m => hdata.1 z hz m trivial, fun m => hJ.choose m trivial,
    ⟨hv.choose, fun s => ⟨(hv.choose_spec s).choose, (hv.choose_spec s).choose_spec.1,
      fun z hz m q i j hij => (hv.choose_spec s).choose_spec.2 z hz m trivial q i j hij⟩⟩,
    fun k => ⟨(hJ.choose_spec.2 k).choose, fun s =>
      ⟨((hJ.choose_spec.2 k).choose_spec s).choose,
        ((hJ.choose_spec.2 k).choose_spec s).choose_spec.1,
        fun z hz v m q i j hij =>
          ((hJ.choose_spec.2 k).choose_spec s).choose_spec.2 z hz v m trivial q i j hij⟩⟩⟩


end ContinuousFlexibility.Analysis.PulledFieldsReferenceRepair
