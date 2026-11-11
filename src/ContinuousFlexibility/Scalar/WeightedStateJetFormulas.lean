import ContinuousFlexibility.Scalar.WeightedCoefficientFormulas
import ContinuousFlexibility.Scalar.WeightedGeometryBounds
import Mathlib.Tactic.FinCases

/-!
# Finite-jet formulas for the actual weighted scalar state

The normalized discriminant and `Q/w` defects below are explicit functions of
the profile mean and the first two spatial height jets. The seven jet,
coframe, and connection outputs are then written without a radial primitive.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

def scalarStateProfileMean (S : PhysicalSpacesData) (x : ScalarWeightedState S) (r : ℝ) : ℝ :=
  angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (r, θ))

def scalarStateDDefect (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (p : PolarPoint) : ℝ :=
  let w := scalarStateProfile D S x p.1
  let a := x.2 * radialPartial (scalarStateIncrement S x) p
  let b := x.2 * heightAngular (scalarStateIncrement S x) p
  -2 * w * a - a ^ 2 - (1 + w ^ 2) * b ^ 2

def scalarStateQDefect (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (p : PolarPoint) : ℝ :=
  x.2 * (radialPartial (scalarStateIncrement S x) p +
    (1 + scalarStateProfile D S x p.1 ^ 2) *
      angularPartial (heightAngular (scalarStateIncrement S x)) p) /
        scalarStateProfile D S x p.1

/-- This is the explicit finite-jet expression for each frozen jet output. -/
def scalarJetFiniteFormula (D : ReferenceData) (S : PhysicalSpacesData)
    (x : ScalarWeightedState S) (i : Fin 7) (p : PolarPoint) : ℝ :=
  let w := D.w p.1 * (1 + scalarStateProfileMean S x p.1)
  let a := x.2 * radialPartial (scalarStateIncrement S x) p
  let b := x.2 * heightAngular (scalarStateIncrement S x) p
  let c := x.2 * radialPartial (heightAngular (scalarStateIncrement S x)) p
  let e := x.2 * angularPartial (heightAngular (scalarStateIncrement S x)) p
  let d := scalarStateDDefect D S x p
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => Real.sqrt (1 + d) / Real.sqrt (1 - b ^ 2) - 1
  | 3 => -(w + a) * b / Real.sqrt (1 - b ^ 2)
  | 4 => p.1 * (Real.sqrt (1 - b ^ 2) - 1)
  | 5 => (w + a) / ((1 - b ^ 2) * Real.sqrt (1 + d)) * c
  | _ => (1 / Real.sqrt (1 + d) - 1) +
      (w + a) / ((1 - b ^ 2) * Real.sqrt (1 + d)) * e

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarStateProfile_eq_mean (x : ScalarWeightedState S) (r : ℝ) :
    scalarStateProfile D S x r = D.w r * (1 + scalarStateProfileMean S x r) := rfl

theorem scalarStateProfileMean_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S) :
    ContDiff ℝ ∞ (scalarStateProfileMean S x) :=
  contDiff_angularMean_radial (scalarHeight_decode_contDiff_and_flatJets hT hS x.1.1.1).1

theorem scalarStateProfile_deriv_expansion
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (r : ℝ) :
    deriv (scalarStateProfile D S x) r =
      deriv D.w r * (1 + scalarStateProfileMean S x r) +
        D.w r * deriv (scalarStateProfileMean S x) r := by
  obtain ⟨_, hdata⟩ := hD
  have hw := hdata.1.2.2.1.1.differentiable (by simp) r
  have hm := (scalarStateProfileMean_contDiff hT hS x).differentiable (by simp) r
  exact (hw.hasDerivAt.mul ((hasDerivAt_const r 1).add hm.hasDerivAt)).deriv.trans
    (by simp only [zero_add])

theorem scalarState_discriminant_eq_one_add_defect
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p =
      1 + scalarStateDDefect D S x p := by
  rw [scalarState_discriminant_expansion hD hT hS x p]
  unfold scalarStateDDefect
  ring

theorem scalarState_Q_eq_profile_mul_one_add_defect
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0)
    (hw : scalarStateProfile D S x p.1 ≠ 0) :
    heightQ (profileEnergy (scalarStateProfile D S x) p)
      (heightRadial (scalarStateHeight D S x) p)
      (angularPartial (heightAngular (scalarStateHeight D S x)) p) =
        scalarStateProfile D S x p.1 * (1 + scalarStateQDefect D S x p) := by
  rw [scalarState_Q_expansion hD hT hS x hr]
  unfold scalarStateQDefect
  field_simp [hw]
  <;> ring

theorem scalarStateHeight_radialPartial_heightAngular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0) :
    radialPartial (heightAngular (scalarStateHeight D S x)) p =
      x.2 * radialPartial (heightAngular (scalarStateIncrement S x)) p := by
  have hh := Radial.contDiff_radialHeightField (scalarStatePrimitive_contDiff hD hT hS x)
  have hu := scalarStateIncrement_contDiff hT hS x
  change radialPartial (heightAngular (heightFamily _ _ x.2)) p = _
  rw [radialPartial_heightAngular_heightFamily hh hu hr,
    Radial.heightAngular_radialHeightField (scalarStatePrimitive_hasDerivAt hD hT hS x),
    radialPartial_const, zero_add]

/-- All seven frozen outputs equal the displayed expressions in actual
first and second jets of the increment. -/
theorem scalarJetComponent_eq_finiteFormula
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (i : Fin 7) {p : PolarPoint} (hr : p.1 ≠ 0) :
    scalarJetComponent D S x i p = scalarJetFiniteFormula D S x i p := by
  have hk := scalarStateHeight_heightRadial hD hT hS x p
  have hp := scalarStateHeight_heightAngular hD hT hS x p
  have hpr := scalarStateHeight_radialPartial_heightAngular hD hT hS x hr
  have hpt := scalarStateHeight_angularPartial_heightAngular hD hT hS x hr
  have hd := scalarState_discriminant_eq_one_add_defect hD hT hS x p
  have hw := scalarStateProfile_eq_mean (D := D) x p.1
  fin_cases i <;> simp only [scalarJetComponent, scalarJetFiniteFormula]
  · rw [hk]
    ring
  · exact hp
  · simp only [heightCoframeOne, coframeAField, coframeAValue]
    change Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p) /
      Real.sqrt (1 - heightAngular (scalarStateHeight D S x) p ^ 2) - 1 = _
    rw [hd, hp]
  · simp only [heightCoframeTwo, coframeBField, coframeBValue]
    rw [hk, hp, hw]
  · simp only [heightCoframeTwo, coframeCField, coframeCValue]
    rw [hp]
    ring
  · simp only [heightConnectionForm, connectionRadialField, connectionRadialValue, connectionB1]
    change heightRadial (scalarStateHeight D S x) p /
      ((1 - heightAngular (scalarStateHeight D S x) p ^ 2) *
        Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p)) *
      radialPartial (heightAngular (scalarStateHeight D S x)) p = _
    rw [hd, hk, hp, hpr, hw]
  · simp only [heightConnectionForm, connectionAngularField, connectionAngularValue,
      connectionInverseRoot, connectionB1]
    change (1 / Real.sqrt
      (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p) +
      heightRadial (scalarStateHeight D S x) p /
        ((1 - heightAngular (scalarStateHeight D S x) p ^ 2) *
          Real.sqrt (polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p)) *
      angularPartial (heightAngular (scalarStateHeight D S x)) p) - 1 = _
    rw [hd, hk, hp, hpt, hw]
    ring

end ContinuousFlexibility.Statements
