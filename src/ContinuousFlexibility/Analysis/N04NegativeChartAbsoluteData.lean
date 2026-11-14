import ContinuousFlexibility.Analysis.N04SourceColumnsSign
import ContinuousFlexibility.Analysis.N04SourceColumnsScalarLinear
import ContinuousFlexibility.Analysis.N04SourceColumnsSmallness
import ContinuousFlexibility.Analysis.N04SourceColumnsReciprocal

/-!
# Absolute determinants and their reciprocal current data

A nonvanishing current determinant has one constant sign on each piece.
Multiplication by this fixed scalar preserves its exact current estimates.
The reference reciprocal envelope then chooses a single smaller sector on
which reciprocal composition supplies every derivative order.
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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {cell : ℕ → ℕ} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Removing the determinant sign neither changes the sector nor costs
any derivative loss. No derivative of the absolute value is assumed. -/
theorem CurrentJetDataOn.negativeChart_abs
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀) (hε : 0 < ε)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hzero : ∀ m q, q ∈ unitStrip → f 0 m q = f₀ m q)
    (hne : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m q, q ∈ unitStrip →
      f z m q ≠ 0) :
    CurrentJetDataOn S T cell (fun _ => True) base ε
      (fun z m q => |f z m q|) (fun m q => |f₀ m q|) := by
  have hU : IsPreconnected (sectorNeighborhood S base ε ε) :=
    (sectorNeighborhood_convex S base ε ε).isPreconnected
  have hV : IsPreconnected unitStrip := isPreconnected_Ioo.prod isPreconnected_univ
  have hz : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε := by
    change sectorGrading S base (0 : StateDirections S) < ε ∧ |(0 : ℝ)| < ε
    exact ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hmid : ((1 / 2 : ℝ), (0 : ℝ)) ∈ unitStrip := by
    refine ⟨?_, mem_univ _⟩
    norm_num
  have hp (m : ℕ) (q : PolarPoint) (hq : q ∈ unitStrip) :
      ContinuousOn (fun z => f z m q) (sectorNeighborhood S base ε ε) := by
    simpa only [spaces_mixedDerivative_zero] using
      ((hf.sourceColumns_regularity h₀ m).parameter 0 0 q hq).continuousOn
  have hs (m : ℕ) : ∃ σ : ℝ, |σ| = 1 ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ q ∈ unitStrip,
        |f z m q| = σ * f z m q :=
    n04SourceColumns_fixed_sign_separate hU hV (hp m)
      (fun z hz => (hf.1 z hz m trivial).1.continuousOn)
      (fun z hz q hq => hne z hz m q hq) hz hmid
  let σ : ℕ → ℝ := fun m => (hs m).choose
  have hσ : ∃ A : ℝ, 0 < A ∧ ∀ m,
      |σ m| ≤ A * T.E0 (T.sample (cell m)) ^ A := by
    refine ⟨1, zero_lt_one, fun m => ?_⟩
    simpa only [σ, (hs m).choose_spec.1, one_mul, Real.rpow_one] using hE m
  apply (hf.sourceColumns_constMul hE hH σ hσ).sourceColumns_congr
  · intro z hz m q hq
    exact ((hs m).choose_spec.2 z hz q hq).symm
  · intro m q hq
    simpa only [hzero m q hq] using ((hs m).choose_spec.2 0 hz q hq).symm

/-- A positive actual family with reference and reference reciprocal data
has reciprocal current data on one uniform sector. The lower bound is
derived from its current difference, before all later jet orders. -/
theorem CurrentJetDataOn.negativeChart_inv
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀)
    (hi₀ : N04SourceReferenceData T cell (fun m q => (f₀ m q)⁻¹))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hpos : ∀ m q, q ∈ unitStrip → 0 < f₀ m q) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      CurrentJetDataOn S T cell (fun _ => True) b δ
        (fun z m q => (f z m q)⁻¹) (fun m q => (f₀ m q)⁻¹) := by
  have hE₀ (m : ℕ) : 0 ≤ T.E0 (T.sample (cell m)) := zero_le_one.trans (hE m)
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  have hinv : ∃ A : ℝ, 0 < A ∧ ∀ m q, q ∈ unitStrip →
      (f₀ m q)⁻¹ ≤ A * T.E0 (T.sample (cell m)) ^ A := by
    obtain ⟨A, hA, hbound⟩ := hi₀.2 0
    refine ⟨A, hA, fun m q hq => ?_⟩
    simpa only [spaces_mixedDerivative_zero, abs_of_pos (inv_pos.mpr (hpos m q hq))]
      using hbound m q hq 0 0 le_rfl
  obtain ⟨b, δ, A, hb, hδ, hδε, hA, hbound⟩ :=
    hf.sourceColumns_half_reference hD hT hε hpos hinv
  have hf' := hf.mono (fun _ h => h) hb hδε hE₀ hH
  obtain ⟨b', δ', hbb', hδ', hδ'δ, hi⟩ := hf'.sourceColumns_inv_of_bound
    hD hT hI h₀ hi₀ hδ hE (2 * A) A (by positivity) hA.le
      (fun z hz m q hq => (hbound z hz m q hq).2)
  exact ⟨b', δ', hb.trans hbb', hδ', hδ'δ.trans hδε, hi⟩

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeChart_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeChart_inv
