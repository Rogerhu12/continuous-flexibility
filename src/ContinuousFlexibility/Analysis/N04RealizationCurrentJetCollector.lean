module

public import ContinuousFlexibility.Analysis.N04RealizationFiniteJetCollection
public import ContinuousFlexibility.Analysis.MaterialSampleBounds
public import Mathlib.Tactic.DeriveFintype

/-!
# The full current certificate from its actual atom families

Every scalar tower below differentiates the actual differenceJets slice
on the one supplied sector neighborhood. Finite collection enlarges only
losses and constants. The data, atlas, samples, low order and neighborhood
are unchanged. The construction of the individual atom families remains
an explicit obligation.
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

private abbrev n04Realization_atomFintype : Fintype Atom := derive_fintype% Atom

attribute [local instance] n04Realization_atomFintype

/-- The exact frozen CurrentJets predicate follows from the actual
per-atom inputs. No coordinate or coefficient representative is chosen. -/
theorem n04Realization_currentJets_of_atomFamilies
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    (hregular : ∀ a, ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m,
      ContDiffOn ℝ ∞ (atom D T S C L K (liftSectorParameter S C z) m a) unitStrip ∧
      ∀ q ∈ unitStrip,
        atom D T S C L K (liftSectorParameter S C z) m a (q + (0, Real.pi)) =
          atom D T S C L K (liftSectorParameter S C z) m a q)
    (J : ∀ a m i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => differenceJets D T S C L K z a m i j q))
    (hvalue : ∀ a, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (q : unitStrip) i j, i + j ≤ s →
        |differenceJets D T S C L K z a m i j q| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * parameterGrading S (s + loss) z)
    (hparameter : ∀ a k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        ∀ m (q : unitStrip) i j, i + j ≤ s →
          |(J a m i j q).D k z v| ≤
            B * T.E0 (T.sample (K.cell m)) ^ B *
              T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
                oneHighVariationWeight (parameterGrading S) base (s + loss) z v) :
    CurrentJets D T S C L K base ε := by
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have hheight (m : ℕ) : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_interval hD hT (K.cell m))).2.1.le _
  have hcollected := n04Realization_collect_scalarJet_bounds
    (isOpen_sectorNeighborhood S base ε ε) (differenceJets D T S C L K)
    (parameterGrading S) hp base
    (fun m => T.E0 (T.sample (K.cell m)))
    (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ))
    hfloor hheight J hvalue hparameter
  refine ⟨(fun z hz m a => hregular a z hz m), hcollected.1, ?_⟩
  simpa only [oneHighVariationWeight] using hcollected.2

end ContinuousFlexibility.Analysis
