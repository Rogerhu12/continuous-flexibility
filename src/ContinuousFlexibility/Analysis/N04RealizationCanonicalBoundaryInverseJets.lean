module

public import ContinuousFlexibility.Analysis.N04RealizationInverseBoundaryDirections
public import ContinuousFlexibility.Analysis.CanonicalClosedInverseJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Finite parameter jets of the stored closed-strip inverse

The first inverse differential is obtained from the actual first forward
differential by smooth operator inversion. Canonical geometry supplies
the two true inverse identities, including at boundary points. Hence only
raw forward boundary jets are parameter inputs; the inverse family and
its derivatives remain the stored functions on the same parameter domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

section Differential

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set X} {A : X → E →L[ℝ] F} {B : X → F →L[ℝ] E}

/-- Actual two-sided differential identities identify smooth operator
inversion with the given inverse differential, on the original domain. -/
def n04Realization_inverseDifferential_directions
    (JA : SmoothDirections U A)
    (hAB : ∀ z ∈ U, (A z).comp (B z) = ContinuousLinearMap.id ℝ F)
    (hBA : ∀ z ∈ U, (B z).comp (A z) = ContinuousLinearMap.id ℝ E) :
    SmoothDirections U B := by
  let V : Set (E →L[ℝ] F) := {D | D.IsInvertible}
  have hV : IsOpen V := ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have houter : ContDiffOn ℝ ∞
      (ContinuousLinearMap.inverse : (E →L[ℝ] F) → F →L[ℝ] E) V := by
    intro D hD
    have hD' : D.IsInvertible := hD
    exact hD'.contDiffAt_map_inverse.contDiffWithinAt
  have hmap : MapsTo A U V := fun z hz =>
    ContinuousLinearMap.IsInvertible.of_inverse (hAB z hz) (hBA z hz)
  let J := smoothDirections_contDiff_comp JA hV houter hmap
  exact J.congr (fun z hz => ContinuousLinearMap.inverse_eq (hAB z hz) (hBA z hz))

end Differential

/-- The actual inverse ordinary jets at any supplied closed-strip points
have genuine parameter towers from the finite raw forward prefix.
No parameter tower of a newly chosen root extension is used. -/
def n04Realization_canonicalClosed_inverseJet_directions
    {P : Type*} [TopologicalSpace P] [AddCommGroup P] [Module ℝ P]
    [IsTopologicalAddGroup P] [ContinuousSMul ℝ P]
    {U : Set P} (hU : IsOpen U)
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (ζ : P → AnnularState S × ℝ)
    (hζ : ∀ z ∈ U, ζ z ∈ stateNeighborhood S C base ε)
    (hsector : ∀ z ∈ U, stateSector S (ζ z).1)
    (m : ℕ) (q : P → PolarPoint)
    (hq : ∀ z ∈ U, q z ∈ canonicalClosed S K m)
    (J1 : SmoothDirections U (fun z =>
      fderiv ℝ (K.chart (ζ z) m) (K.inverseChart (ζ z) m (q z))))
    (N : ℕ)
    (JF : ∀ j, 2 ≤ j → j ≤ N →
      SmoothDirections U (fun z =>
        iteratedFDeriv ℝ j (K.chart (ζ z) m)
          (K.inverseChart (ζ z) m (q z))))
    (n : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) (v : Fin n → PolarPoint) :
    SmoothDirections U (fun z =>
      iteratedFDeriv ℝ n (K.inverseChart (ζ z) m) (q z) v) := by
  let f : P → PolarPoint → PolarPoint := fun z => K.chart (ζ z) m
  let g : P → PolarPoint → PolarPoint := fun z => K.inverseChart (ζ z) m
  have hF : ∀ z ∈ U, ContDiffAt ℝ ∞ (f z) (g z (q z)) := by
    intro z hz
    have hclosed := hA.boundary (ζ z) (hζ z hz) (hsector z hz) m
    exact (hclosed.2.2.2.2.1 _ (hclosed.2.1 (hq z hz))).1
  have hG : ∀ z ∈ U, ContDiffAt ℝ ∞ (g z) (q z) := by
    intro z hz
    exact n04b_inverseChart_contDiffAt_closed hA (hζ z hz) (hsector z hz) m (hq z hz)
  have hcomp (z : P) (hz : z ∈ U) :=
    canonicalClosed_inverse_fderiv hA (hζ z hz) (hsector z hz) m (hq z hz)
  let JL : SmoothDirections U (fun z => fderiv ℝ (g z) (q z)) :=
    n04Realization_inverseDifferential_directions J1
      (fun z hz => (hcomp z hz).2) (fun z hz => (hcomp z hz).1)
  exact n04Realization_inverse_finiteJet_directions hU hF hG
    (fun z hz => (canonicalClosed_inverse_germs hA
      (hζ z hz) (hsector z hz) m (hq z hz)).2)
    (fun z hz => (hcomp z hz).1) JL N JF n hn hN v

end ContinuousFlexibility.Analysis
