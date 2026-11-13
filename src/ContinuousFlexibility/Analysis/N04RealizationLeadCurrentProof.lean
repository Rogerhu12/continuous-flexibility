import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# The current obligation from its split

The five interface statements of `N04RealizationLeadCurrentSplit` give the
current obligation: the positive family and its neighborhood come from the
positive geometry statement, every later statement restricts the
neighborhood, and the data of every atom are restricted to the last one.
The geometry and field data remain conditional on the same atlas's reference
jets until the parent supplies that certificate. All neighborhood choices
still precede the auxiliary column.
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

/-- The current obligation from the five interface statements. -/
theorem n04Realization_currentObligation_of_split
    (hpos : N04RealizationPositiveGeometryObligation)
    (hneg : N04RealizationNegativeGeometryObligation)
    (hfield : N04RealizationPulledFieldObligation)
    (hsrc : N04RealizationSourceColumnObligation)
    (hprin : N04RealizationPrincipalObligation) :
    N04RealizationCurrentObligation := by
  intro W X Y H hfam hreference e
  refine (hpos W X Y H hfam hreference e).elim fun B hB =>
    hB.elim fun b h1 => h1.elim fun ε h1 => h1.elim
    fun lower h1 => h1.elim fun upper h1 => h1.elim fun τ h1 => h1.elim fun σ h1 =>
      h1.elim fun Q hp => ?_
  let G : N04RealizationGauge := ⟨W, X, e, Y, H, τ, σ, Q, B.region⟩
  have hb : W.base ≤ b := hp.1
  have hε : 0 < ε := hp.2.1
  have hεε : ε ≤ W.ε := hp.2.2.1
  have hadm : G.Admissible b ε :=
    ⟨hb, hε, hεε, hfam, hp.2.2.2.2.1, B, lower, upper, rfl, hp.2.2.2.1⟩
  have hgeoP : ∀ η, G.ReferenceData η → G.GeometryData η (G.Pos η) b ε :=
    fun η _ => hp.2.2.2.2.2 η
  have h2 := hneg G b ε hadm
  let b2 := h2.choose
  let ε2 := h2.choose_spec.choose
  have hp2 := h2.choose_spec.choose_spec
  have hadm2 : G.Admissible b2 ε2 := G.admissible_mono hadm hp2.1 hp2.2.1 hp2.2.2.1
  have hgeo2 : ∀ η, G.ReferenceData η → G.GeometryData η (fun _ => True) b2 ε2 :=
    fun η href =>
      G.geometryData_union η
        (G.geometryData_mono η (hgeoP η href) (fun _ h => h) hp2.1 hp2.2.2.1)
        (hp2.2.2.2 η)
  have h3 := hfield G b2 ε2 hadm2 hgeo2
  let b3 := h3.choose
  let ε3 := h3.choose_spec.choose
  have hp3 := h3.choose_spec.choose_spec
  have hadm3 : G.Admissible b3 ε3 := G.admissible_mono hadm2 hp3.1 hp3.2.1 hp3.2.2.1
  have hgeo3 : ∀ η, G.ReferenceData η → G.GeometryData η (fun _ => True) b3 ε3 :=
    fun η href => G.geometryData_mono η (hgeo2 η href) (fun _ h => h) hp3.1 hp3.2.2.1
  have hfd3 : ∀ η, G.ReferenceData η → G.FieldData η b3 ε3 := hp3.2.2.2
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
  refine ⟨B, nb, ε', hb.trans hbn, hε', hεn.trans hεε, lower, upper, τ, σ, Q,
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

end ContinuousFlexibility.Analysis
