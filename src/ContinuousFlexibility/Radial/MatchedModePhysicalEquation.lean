module

public import ContinuousFlexibility.Radial.ModeLocalMeasure

/-!
# Physical equations of the actual modal inverse

The frozen model uses the source -f / ρ and the scalar opposite to the
physical border scalar. These identities pass between its actual L²
graph and the ordinary radial weak equation without changing test classes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- A physical radial source as an element of the actual model space. -/
def matchedModePhysicalSource (D : ReferenceData) (f : ℝ → ℝ)
    (hf : MemLp (fun r => -f r / matchingDensity D r) 2 (radialHilbertMeasure D))
    (t : ℝ) : RadialModePair D :=
  (hf.toLp (fun r => -f r / matchingDensity D r), t)

theorem matchedModePhysicalSource_ae (D : ReferenceData) (f : ℝ → ℝ)
    (hf : MemLp (fun r => -f r / matchingDensity D r) 2 (radialHilbertMeasure D))
    (t : ℝ) :
    ((matchedModePhysicalSource D f hf t).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r) :=
  hf.coeFn_toLp

/-- Cancellation of the actual Hilbert density, including the model sign. -/
theorem matchedMode_physicalSource_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {F : RadialModePair D} {f : ℝ → ℝ}
    (hF : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r)) (ψ : ℝ → ℝ) :
    -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r) =
      ∫ r in D.a..D.b, f r * ψ r := by
  have he :
      (∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r) =
        ∫ r in D.a..D.b, -(f r * ψ r) := by
    apply matchingInterval_congr_ae hD
    have hcore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
      (radialHilbertMeasure_ae_iff hD).mpr (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [hF, hcore] with r hr hrc
    rw [hr]
    field_simp [(matchingDensity_pos hD hrc).ne']
    <;> ring
  rw [he, intervalIntegral.integral_neg, neg_neg]

/-- The full frozen class of modal tests is retained in this conversion. -/
theorem modeLocalEquation_physical_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {J : Set ℝ}
    {u : RadialModeL2 D} {ν : ℝ} {F : RadialModePair D} {f : ℝ → ℝ}
    (hF : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r)) :
    ModeLocalEquation D j J (u, -ν) F ↔
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Function.support ψ ⊆ J →
        (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) +
          ν * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
          ∫ r in D.a..D.b, f r * ψ r := by
  constructor
  · intro h ψ hψ hc hs
    have he := h ψ hψ hc hs
    change (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      (-ν) * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
        -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r) at he
    rw [matchedMode_physicalSource_pairing hD hF ψ] at he
    simpa only [neg_mul, sub_neg_eq_add] using he
  · intro h ψ hψ hc hs
    change (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      (-ν) * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
        -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r)
    rw [matchedMode_physicalSource_pairing hD hF ψ]
    simpa only [neg_mul, sub_neg_eq_add] using h ψ hψ hc hs

theorem modeFullGraph_physical_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ}
    {u : RadialModeL2 D} {ν : ℝ} {F : RadialModePair D} {f : ℝ → ℝ}
    (hF : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r)) :
    ModeFullGraph D j (u, -ν) F ↔
      (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Function.support ψ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) +
          ν * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
          ∫ r in D.a..D.b, f r * ψ r) ∧
      (if j = 2 then
        (∫ r in D.a..D.b, referenceColumn D r * u r) = F.2
      else ν = 0 ∧ F.2 = 0) := by
  unfold ModeFullGraph
  rw [modeLocalEquation_physical_iff hD hF]
  by_cases hj : j = 2 <;> simp only [hj, ite_true, ite_false, neg_eq_zero]

/-- The first coordinate is unchanged, and the physical scalar is -ν. -/
def matchedModePhysicalSolution {D : ReferenceData}
    (G : RadialModePair D →L[ℝ] RadialModePair D) (F : RadialModePair D) :
    RadialModePair D :=
  ((G F).1, -(G F).2)

theorem matchedModePhysicalSolution_modelGraph {D : ReferenceData} {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) (F : RadialModePair D)
    (hactive : j ≠ 2 → F.2 = 0) :
    ModeFullGraph D j
      ((matchedModePhysicalSolution G F).1, -(matchedModePhysicalSolution G F).2) F := by
  simpa only [matchedModePhysicalSolution, neg_neg, Prod.mk.eta] using hG.1 F hactive

/-- Applying the actual inverse gives the ordinary dr weak equation and
the exact bordered row at frequency two. -/
theorem matchedModePhysicalSolution_solves {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) (f : ℝ → ℝ)
    (hf : MemLp (fun r => -f r / matchingDensity D r) 2 (radialHilbertMeasure D))
    (t : ℝ) (hactive : j ≠ 2 → t = 0) :
    let U := matchedModePhysicalSolution G (matchedModePhysicalSource D f hf t)
    (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ radialCore D →
      (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) +
        U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
        ∫ r in D.a..D.b, f r * ψ r) ∧
    (if j = 2 then (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = t
      else U.2 = 0 ∧ t = 0) := by
  exact (modeFullGraph_physical_iff hD (matchedModePhysicalSource_ae D f hf t)).mp
    (matchedModePhysicalSolution_modelGraph hG
      (matchedModePhysicalSource D f hf t) hactive)

/-- Physical solutions in the frozen modal graph are the actual inverse
output, with the same sign convention in the scalar coordinate. -/
theorem matchedModePhysicalSolution_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) {F : RadialModePair D} {f : ℝ → ℝ}
    (hF : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r))
    {u : RadialModeL2 D} {ν : ℝ}
    (hEq : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ radialCore D →
      (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) +
        ν * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
        ∫ r in D.a..D.b, f r * ψ r)
    (hrow : if j = 2 then (∫ r in D.a..D.b, referenceColumn D r * u r) = F.2
      else ν = 0 ∧ F.2 = 0) :
    matchedModePhysicalSolution G F = (u, ν) := by
  have hmodel := (modeFullGraph_physical_iff hD hF).mpr ⟨hEq, hrow⟩
  have he := hG.2 (u, -ν) F hmodel
  simp only [matchedModePhysicalSolution, he, neg_neg]

end ContinuousFlexibility.Radial
