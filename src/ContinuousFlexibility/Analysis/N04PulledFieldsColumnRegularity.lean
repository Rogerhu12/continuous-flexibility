module

public import ContinuousFlexibility.Analysis.N04PulledFieldsColumnPhysical
public import ContinuousFlexibility.Analysis.N04PulledFieldsSpatial

/-!
# Regularity of both actual pulled columns on one neighborhood

The uniform physical height towers of the left and distinguished columns
choose one neighborhood before the auxiliary normalizer. Intersecting it
with the admissible gauge neighborhood preserves that order of choices.
The spatial clause follows from the actual decoded fields and inverse
chart. Same-atlas reference jets are used only for the joint inverse tower
needed to form genuine mixed parameter/spatial towers.

No quantitative composition estimate or current-jet conclusion is asserted
by this regularity module.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

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

/-- A decoded scalar-height column has the full spatial clause after
pullback by the retained inverse chart. -/
theorem n04PulledFieldsColumn_spatial
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    {N : Parameter (G.S η) → ScalarHeightSpace (G.S η)}
    (heq : ∀ z ∈ sectorNeighborhood (G.S η) base ε ε,
      ((G.S η).height scalarBeta).decode (N z) = F (G.lift η z))
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.pulled η F z m) unitStrip ∧
      ∀ y ∈ unitStrip, G.pulled η F z m (y + (0, Real.pi)) = G.pulled η F z m y := by
  have hsmooth : ContDiffOn ℝ ∞ (F (G.lift η z)) (annularOpen G.W.D) :=
    (heq z hz) ▸ ((G.W.hS.1 scalarBeta).2.2.2.1 (N z)).1
  exact n04PulledFields_spatial_of_physical G η hadm F hz hsmooth
    (fun p _ => n04PulledFieldsColumn_periodic G η heq hz p) m

/-- Both actual columns satisfy the spatial clause on a common smaller
neighborhood chosen before the auxiliary normalizer. The supplied geometry
data and same-atlas reference jets then give all genuine mixed towers on
that very neighborhood, with no dependence of its choice on jet orders. -/
theorem n04PulledFieldsColumn_regularity
    (G : N04RealizationGauge) {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) :
    ∃ (base' : ℕ) (ε' : ℝ), base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space)
        (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ),
        (F = G.leftColumnField η ∨ F = G.nuField η) →
        (∀ z ∈ sectorNeighborhood (G.S η) base' ε' ε', ∀ m,
          ContDiffOn ℝ ∞ (G.pulled η F z m) unitStrip ∧
            ∀ y ∈ unitStrip,
              G.pulled η F z m (y + (0, Real.pi)) = G.pulled η F z m y) ∧
        (G.GeometryData η (fun _ => True) base ε →
          ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) →
          ∀ m, Nonempty (MixedJetRegularity
            (sectorNeighborhood (G.S η) base' ε' ε') unitStrip
            (fun z => G.pulled η F z m))) := by
  have h := n04PulledFieldsColumn_uniformHeight G
  refine h.elim fun b hb => hb.elim fun ell hell => hell.elim fun δ hδ => ?_
  let base' : ℕ := max base b
  let ε' : ℝ := min ε δ
  have hbase : base ≤ base' := le_max_left _ _
  have hε' : 0 < ε' := lt_min hadm.2.1 hδ.2.1
  have hεε : ε' ≤ ε := min_le_left _ _
  have hadm' : G.Admissible base' ε' := G.admissible_mono hadm hbase hε' hεε
  refine ⟨base', ε', hbase, hε', hεε, ?_⟩
  intro η F hF
  have hfield :
      (fun z => F (G.lift η z)) = (fun z => G.leftColumnField η (G.lift η z)) ∨
      (fun z => F (G.lift η z)) = (fun z => G.nuField η (G.lift η z)) :=
    hF.elim
      (fun hleft => Or.inl (congrArg (fun f z => f (G.lift η z)) hleft))
      (fun hnu => Or.inr (congrArg (fun f z => f (G.lift η z)) hnu))
  have hheight := hδ.2.2.2 η (fun z => F (G.lift η z)) hfield
  refine hheight.elim fun N hN => ?_
  have hsub : sectorNeighborhood (G.S η) base' ε' ε' ⊆
      sectorNeighborhood (G.S η) b δ δ :=
    sectorNeighborhood_mono (G.S η) (le_max_right _ _) (min_le_right _ _) (min_le_right _ _)
  have heq : ∀ z ∈ sectorNeighborhood (G.S η) base' ε' ε',
      ((G.S η).height scalarBeta).decode (N z) = F (G.lift η z) :=
    fun z hz => hN.2 z (hsub hz)
  refine ⟨fun z hz m => n04PulledFieldsColumn_spatial G η hadm' F heq hz m, ?_⟩
  intro hgeo href m
  have hN' : FixedNeighborhoodSmoothTame (parameterGrading (G.S η))
      (scalarHeightGrading (G.S η)) (sectorNeighborhood (G.S η) base' ε' ε')
      base' ell N :=
    (hN.1.restrict (isOpen_sectorNeighborhood (G.S η) base' ε' ε') hsub).weaken
      (n07aParameterGrading_monotone (G.S η)) (le_max_right _ _) le_rfl
  let JF := n04PulledFieldsColumn_jointDirections G η hN'.2.choose hN'.2.choose_spec heq
  have hgeo' := G.geometryData_mono η hgeo (fun _ htrue => htrue) hbase hεε
  let Jφ := n04PulledFields_admissible_inversePoint_jointDirections G η hadm' hgeo' href m
  exact ⟨n04PulledFieldsColumn_pulledMixedRegularity G η F m JF Jφ
    (n04PulledFields_pulledPoint_mapsTo G η hadm' m)⟩

end ContinuousFlexibility.Analysis
