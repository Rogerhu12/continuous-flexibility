import ContinuousFlexibility.Radial.TerminalActualCutoffColumns
import ContinuousFlexibility.Radial.TerminalInnerPoissonColumns

/-!
# Actual regional data before the terminal Poisson correction

This record contains the two regional inverse constructions, the actual
stand-in functions and physical cutoffs, and their measured source and
energy bounds. It does not contain an inner Poisson function or a bound
on its flux matrix. Those are constructed from these data.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

structure TerminalRegionalData (D : ReferenceData) where
  matching : RadialMatchingData D
  cut_order : D.a < matching.innerLeft ∧ matching.innerLeft < matching.innerRight ∧
    matching.innerRight < D.b
  column_inside : Function.support (referenceColumn D) ⊆
    Ioo matching.innerLeft matching.innerRight
  margin_pos : 0 < matching.margin
  diagonal : ∀ i, 0 < matching.boundaryScale i ∧ 0 < matching.D0 i ∧
    matching.D0 i ≤ 1 / 2 ∧
    matching.margin ≤ |matching.A i i * matching.D0 i - matching.B i i|
  boundary_off_diagonal : ∀ i k, i ≠ k → matching.A i k = 0 ∧ matching.B i k = 0
  boundary_normalized : ∀ i, matching.A i i ^ 2 + matching.B i i ^ 2 = 1
  inner_solve : ∀ F, (matching.frequency ≠ 2 → F.2 = 0) →
    ModeInnerDirichletGraph D matching
      (matching.innerInverse (matching.sourceInner F)) (matching.sourceInner F)
  inner_unique : ∀ U F, ModeInnerDirichletGraph D matching U F → matching.innerInverse F = U
  inner_source : ∀ F, matching.sourceInner F =
    modeInnerSource D matching.innerLeft matching.innerRight F
  inner_representative : ∀ F,
    ((matching.innerInverse (matching.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      matching.innerRepresentative F ∧
    ModeLocalEquation D matching.frequency (Ioo matching.innerLeft matching.innerRight)
      (matching.innerInverse (matching.sourceInner F)) (matching.sourceInner F) ∧
    ContDiffOn ℝ 1 (matching.innerRepresentative F) (Icc matching.innerLeft matching.innerRight) ∧
    (∀ r ∈ matchingOuterRegion D matching, matching.innerRepresentative F r = 0) ∧
    (if matching.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * matching.innerRepresentative F r) = F.2
     else (matching.innerInverse (matching.sourceInner F)).2 = 0) ∧
    (∀ i, matching.innerRepresentative F (matchingCut D matching i) = 0)
  outer : MatchingOuterRealizations D matching
  cutoff : Fin 2 → ℝ → ℝ
  standIn : Fin 2 → ℝ → ℝ
  cutoff_smooth : ∀ i, ContDiff ℝ ∞ (cutoff i)
  standIn_smooth : ∀ i, ContDiff ℝ ∞ (standIn i)
  standIn_equation : ∀ i r, r ∈ Ioo matching.innerLeft matching.innerRight →
    r ∈ Function.support (cutoff i) →
    radialJacobi ((matching.frequency : ℝ) ^ 2) D.w (standIn i) r = 0
  source_memLp : ∀ i,
    MemLp (terminalCapHilbertSource (matching.boundaryScale i) D.w (cutoff i) (standIn i))
      2 (radialHilbertMeasure D)
  cutoff_derivative_inside : ∀ i, tsupport (deriv (cutoff i)) ⊆
    Ioo matching.innerLeft matching.innerRight
  cutoff_disjoint : ∀ i k, i ≠ k → Disjoint (tsupport (cutoff i)) (tsupport (cutoff k))
  cutoff_column_disjoint : ∀ i,
    Disjoint (tsupport (referenceColumn D)) (tsupport (cutoff i))
  cutoff_boundary : ∀ i, cutoff i =ᶠ[𝓝 (matchingCut D matching i)] fun _ => (1 : ℝ)
  standIn_boundary : ∀ i, standIn i (matchingCut D matching i) = 1
  boundary_scale : ∀ i, matching.boundaryScale i =
    standInBoundaryScale ((matching.frequency : ℝ) ^ 2)
      (D.w (matchingCut D matching i)) (matchingCut D matching i)
  frequency_pos : (0 : ℝ) < matching.frequency
  boundary_slope : ∀ i, terminalCutoffSlope matching standIn i = matching.D0 i
  attenuation : Fin 2 → ℝ
  sourceCost : ℝ
  energyCost : ℝ
  inverseCost : ℝ
  sourceCost_nonneg : 0 ≤ sourceCost
  energyCost_nonneg : 0 ≤ energyCost
  source_bound : ∀ i,
    (eLpNorm (terminalCapHilbertSource (matching.boundaryScale i) D.w (cutoff i) (standIn i))
      2 (radialHilbertMeasure D)).toReal ≤
        (sourceCost * sqrt (matching.D0 i)) * exp (-attenuation i)
  energy_bound : ∀ i, |terminalCutoffEnergy matching cutoff standIn i| ≤
    energyCost * matching.D0 i * exp (-2 * attenuation i)
  inverse_bound : ‖matching.innerInverse‖ ≤ inverseCost
  error_budget : ∀ i k, (energyCost + inverseCost * sourceCost ^ 2) *
    exp (-attenuation i - attenuation k) ≤ matching.margin / 16

end ContinuousFlexibility.Radial
