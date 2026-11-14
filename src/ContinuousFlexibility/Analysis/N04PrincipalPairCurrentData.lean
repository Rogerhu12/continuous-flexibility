import ContinuousFlexibility.Analysis.N04PrincipalPairData
import ContinuousFlexibility.Analysis.N04PrincipalPairInverse

/-!
# Returning paired estimates to the exact current-data interface

Once the positive and negative pieces have been combined, the difference
tower exists on every piece. A final common low order and radius provide
the frozen value and tower bounds without any additional representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

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

theorem N04PrincipalPairBounds.to_currentData
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hf : N04PrincipalPairBounds (parameterGrading S)
      (fun m => T.E0 (T.sample (cell m)))
      (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
      (U := sectorNeighborhood S base ε ε) (Ω := unitStrip)
      (fun m z => f z m) f₀)
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hperiodic : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m q, q ∈ unitStrip →
      f z m (q + (0, Real.pi)) = f z m q)
    (hzero : ∀ m, EqOn (f 0 m) (f₀ m) unitStrip) :
    ∃ b : ℕ, base ≤ b ∧
      CurrentJetDataOn S T cell (fun _ => True) b (min ε (1 / 2)) f f₀ := by
  let t : ℕ := hf.choose
  let RF : ∀ m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f z m) := hf.choose_spec.choose
  let RD : ∀ m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z q => f z m q - f₀ m q) :=
    hf.choose_spec.choose_spec.choose_spec.choose
  have hD : N04PrincipalWeightedTowerBounds (parameterGrading S) t
      (fun m => T.E0 (T.sample (cell m)))
      (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) RD :=
    hf.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  let b : ℕ := max base t
  have hbase : base ≤ b := le_max_left _ _
  have hD' := n04Principal_weightedTower_monoBase (parameterGrading S)
    (n07aParameterGrading_monotone S)
    (fun m => T.E0 (T.sample (cell m)))
    (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
    hE (fun m => Real.rpow_nonneg (hH m) _) (le_max_right base t) RD hD
  let R : ∀ m : {m : ℕ // True},
      MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
        (fun z q => f z m.val q - f₀ m.val q) := fun m => RD m.val
  have hR : N04PrincipalWeightedTowerBounds (parameterGrading S) b
      (fun m : {m : ℕ // True} => T.E0 (T.sample (cell m.val)))
      (fun m : {m : ℕ // True} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) R := by
    intro k
    have hh := hD' k
    refine ⟨hh.choose, fun s => ⟨(hh.choose_spec s).choose,
      (hh.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m a c hac q hq z hz hlo v
    exact (hh.choose_spec s).choose_spec.2 m.val a c hac q hq z hz hlo v
  refine ⟨b, hbase, ?_⟩
  exact n04Principal_data_of_weightedDifference hbase
    (lt_min hε (by norm_num)) (min_le_left _ _) (min_le_right _ _)
    hE hH (fun z hz m _ => ⟨(RF m).spatial z hz, hperiodic z hz m⟩)
    (fun m _ => hzero m)
    (fun m a c q => (RD m).parameter a c q.val q.property) R hR

end ContinuousFlexibility.Analysis
