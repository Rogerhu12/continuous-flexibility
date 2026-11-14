import ContinuousFlexibility.Analysis.N04PrincipalPairData
import ContinuousFlexibility.Analysis.N04PrincipalTowerValue
import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentData

/-!
# Returning paired estimates on selected pieces to current data

The paired towers need only exist on the selected pieces. Positive
parameter jets of their actual current fields give the complete current
difference certificate, including the value bound at the same reference.
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

theorem N04PrincipalPairBounds.to_currentDataOn
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hf : N04PrincipalPairBounds (parameterGrading S)
      (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
      (fun m : {m : ℕ // P m} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ))
      (U := sectorNeighborhood S base ε ε) (Ω := unitStrip)
      (fun m z => f z m.val) (fun m => f₀ m.val))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hperiodic : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q)
    (href : ∀ m, P m → f₀ m = f 0 m) :
    ∃ b : ℕ, base ≤ b ∧
      CurrentJetDataOn S T cell P b (min ε (1 / 2)) f f₀ := by
  let t : ℕ := hf.choose
  let RF : ∀ m : {m : ℕ // P m},
      MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
        (fun z => f z m.val) := hf.choose_spec.choose
  let RD : ∀ m : {m : ℕ // P m},
      MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
        (fun z q => f z m.val q - f₀ m.val q) :=
    hf.choose_spec.choose_spec.choose_spec.choose
  have hD : N04PrincipalWeightedTowerBounds (parameterGrading S) t
      (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
      (fun m : {m : ℕ // P m} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) RD :=
    hf.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  let b : ℕ := max base t
  let δ : ℝ := min ε (1 / 2)
  have hbase : base ≤ b := le_max_left _ _
  have hsub : sectorNeighborhood S b δ δ ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hbase (min_le_left _ _) (min_le_left _ _)
  have hU : IsOpen (sectorNeighborhood S b δ δ) := isOpen_sectorNeighborhood S b δ δ
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hlow (z : Parameter S) (hz : z ∈ sectorNeighborhood S b δ δ) :
      parameterGrading S b z ≤ 1 :=
    n04Principal_parameter_low_le_one (min_le_right _ _) hz
  have hD' := n04Principal_weightedTower_monoBase (parameterGrading S)
    (n07aParameterGrading_monotone S)
    (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
    (fun m : {m : ℕ // P m} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ))
    (fun m => hE m.val) (fun m => Real.rpow_nonneg (hH m.val) _)
    (le_max_right base t) RD hD
  let J : ∀ m, P m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood S b δ δ)
        (fun z => mixedDerivative i j (f z m) q.val) := fun m hm i j q =>
    ((RF ⟨m, hm⟩).parameter i j q.val q.property).restrict hU hsub
  refine ⟨b, hbase, CurrentJetDataOn.of_positiveParameterJets
    (lt_min hε (by norm_num)) hE hH hlow
    (fun z hz m hm => ⟨(RF ⟨m, hm⟩).spatial z (hsub hz), hperiodic z (hsub hz) m hm⟩)
    href J ?_⟩
  intro k hk
  have hdk := hD' k
  refine ⟨hdk.choose, fun s => ?_⟩
  have hds := hdk.choose_spec s
  refine ⟨hds.choose, hds.choose_spec.1, ?_⟩
  intro z hz v m hm q i j hij
  let KD := (((RD ⟨m, hm⟩).parameter i j q.val q.property).restrict hU hsub).congr
    (fun x hx => mixedDerivative_sub_of_contDiffOn hΩ
      ((RF ⟨m, hm⟩).spatial x (hsub hx))
      (hf.reference_spatial ⟨m, hm⟩ x (hsub hx)) i j q.property)
  have he : ((RD ⟨m, hm⟩).parameter i j q.val q.property).D k z v =
      (J m hm i j q).D k z v :=
    smoothDirections_D_sub_constant (J m hm i j q) KD hk hz v
  have hb := hds.choose_spec.2 ⟨m, hm⟩ i j hij q.val q.property z (hsub hz) (hlow z hz) v
  exact (congrArg abs he.symm).trans_le ((Real.norm_eq_abs _).symm.trans_le hb)

end ContinuousFlexibility.Analysis
