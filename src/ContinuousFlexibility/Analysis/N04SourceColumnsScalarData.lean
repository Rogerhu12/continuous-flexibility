import ContinuousFlexibility.Analysis.N04SourceColumnsScalarFamily
import ContinuousFlexibility.Analysis.N04SourceColumnsCollector
import ContinuousFlexibility.Analysis.N04SourceColumnsSmallness

/-!
# Scalar composition of the frozen current difference data

The scalar outer jets may have material coefficient costs. A single
neighborhood, chosen before the derivative orders, carries the complete
output difference tower. This applies to the reciprocal after a uniform
lower bound for the actual source factor has been established.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

/-- A scalar outer function whose genuine outer jets have coefficient
envelopes preserves the full current difference data after one restriction. -/
theorem CurrentJetDataOn.sourceColumns_scalarComp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {cell : ℕ → ℕ} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀)
    (g : ℝ → ℝ) (V : Set ℝ) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hg₀ : N04SourceReferenceData T cell (fun m q => g (f₀ m q)))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hmap : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, MapsTo (f z m) unitStrip V)
    (houter : ∀ N : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ m q, q ∈ unitStrip → ∀ z ∈ sectorNeighborhood S base ε ε,
        ∀ a b : ℕ, a + b ≤ N →
          ‖iteratedFDeriv ℝ a (iteratedDeriv b g) (f z m q)‖ ≤
            A * T.E0 (T.sample (cell m)) ^ A) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell (fun _ => True) base' ε'
        (fun z m q => g (f z m q)) (fun m q => g (f₀ m q)) := by
  have hpmono : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have hU : IsOpen (sectorNeighborhood S base ε ε) := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let E : ℕ → ℝ := fun m => T.E0 (T.sample (cell m))
  let H : ℕ → ℝ := fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hH₀ (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  have hheight := material_sample_height_coefficient_power_bounded hD hT cell 0
    (by norm_num : 0 < (3 / 4 : ℝ))
  have hH (m : ℕ) : 0 ≤ H m ∧ H m ≤ hheight.choose :=
    ⟨Real.rpow_nonneg (hH₀ m) _, by
      simpa only [H, Real.rpow_zero, mul_one] using hheight.choose_spec.2 m⟩
  let RF (m : ℕ) := hf.sourceColumns_regularity h₀ m
  have hfull := CurrentJetDataOn.sourceColumns_fullTower hD hT hf h₀ hE
  let L : ℕ → ℕ := fun k => (hfull k).choose
  have hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m q (hq : q ∈ unitStrip) a b, a + b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF m).parameter a b q hq).D k z v| ≤
          B * E m ^ B * parameterHeightWeight (H m) k *
            oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    intro k s
    have hs := (hfull k).choose_spec s
    refine ⟨hs.choose, hs.choose_spec.1, fun m q hq a b hab z hz v => ?_⟩
    exact hs.choose_spec.2 m q hq a b hab ((RF m).parameter a b q hq) z hz v
  have hscalar := n04SourceColumns_scalarFamily_oneHigh
    (parameterGrading S) hpmono hI base L hU hΩ hV E H hheight.choose hE hH
    (fun m z => f z m) g RF hg (fun m z hz => hmap z hz m) hbound houter
  let base' : ℕ := hscalar.choose
  have hbase : base ≤ base' := hscalar.choose_spec.1
  let ε' : ℝ := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hU' : IsOpen (sectorNeighborhood S base' ε' ε') :=
    isOpen_sectorNeighborhood S base' ε' ε'
  have hsub : sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hbase hε'ε hε'ε
  have hlow : ∀ z ∈ sectorNeighborhood S base' ε' ε', parameterGrading S base' z ≤ 1 := by
    intro z hz
    have hp := n04SourceColumns_parameter_lt hz
    have hhalf : ε' ≤ 1 / 2 := min_le_right _ _
    linarith only [hp, hhalf]
  let RC (m : ℕ) : MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z q => g (f z m q)) :=
    (RF m).scalarComp hU hΩ hV hg (fun z hz => hmap z hz m)
  let RC' (m : ℕ) : MixedJetRegularity (sectorNeighborhood S base' ε' ε') unitStrip
      (fun z q => g (f z m q)) :=
    { spatial := fun z hz => (RC m).spatial z (hsub hz)
      parameter := fun a b q hq => ((RC m).parameter a b q hq).restrict hU' hsub }
  refine ⟨base', ε', hbase, hε', hε'ε, ?_⟩
  apply n04SourceColumns_data_of_positive_towers hε' hE hH₀ RC'
    (fun z hz m q hq => congrArg g ((hf.1 z (hsub hz) m trivial).2 q hq))
    (fun m => (hg₀.1 m).1)
    (fun m q hq => congrArg g (hf.sourceColumns_zero_eq hε m q hq)) hlow
  intro k hk
  have ht := hscalar.choose_spec.2 k hk
  refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
    (ht.choose_spec s).choose_spec.1, ?_⟩⟩
  intro m q hq a b hab z hz v
  exact (ht.choose_spec s).choose_spec.2 m q hq a b hab
    ((RC m).parameter a b q hq) z (hsub hz) (hlow z hz) v

end ContinuousFlexibility.Analysis
