module

public import ContinuousFlexibility.Analysis.N08CircleHeightRow
public import ContinuousFlexibility.Analysis.N08CircleReferenceDiagonal

/-!
# The control-column data from the actual derivatives

The diagonal and reciprocal act on the actual control Hilbert space. They
are defined globally by the bounded construction wherever the required
coefficient bounds hold, and by zero elsewhere. On the final neighborhood
their action and both inverse identities follow from the same coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

section DiagonalFamily

variable {Z : Type*}

def n08BoundedControlDiagonal (a : Z → ℕ → ℝ) (z : Z) :
    ControlBanach →L[ℝ] ControlBanach := by
  classical
  exact if h : ∀ m, (1 / 2 : ℝ) ≤ |a z m| ∧ |a z m| ≤ 2 then
    n08ControlDiagonal (a z) (fun m => (h m).2) else 0

def n08BoundedControlDiagonalInverse (a : Z → ℕ → ℝ) (z : Z) :
    ControlBanach →L[ℝ] ControlBanach := by
  classical
  exact if h : ∀ m, (1 / 2 : ℝ) ≤ |a z m| ∧ |a z m| ≤ 2 then
    n08ControlDiagonalInverse (a z) (fun m => (h m).1) else 0

theorem n08BoundedControlDiagonal_eq (a : Z → ℕ → ℝ) (z : Z)
    (h : ∀ m, (1 / 2 : ℝ) ≤ |a z m| ∧ |a z m| ≤ 2) :
    n08BoundedControlDiagonal a z = n08ControlDiagonal (a z) (fun m => (h m).2) := by
  rw [n08BoundedControlDiagonal, dif_pos h]

theorem n08BoundedControlDiagonalInverse_eq (a : Z → ℕ → ℝ) (z : Z)
    (h : ∀ m, (1 / 2 : ℝ) ≤ |a z m| ∧ |a z m| ≤ 2) :
    n08BoundedControlDiagonalInverse a z =
      n08ControlDiagonalInverse (a z) (fun m => (h m).1) := by
  rw [n08BoundedControlDiagonalInverse, dif_pos h]

theorem n08BoundedControlDiagonal_apply (a : Z → ℕ → ℝ) (z : Z)
    (h : ∀ m, (1 / 2 : ℝ) ≤ |a z m| ∧ |a z m| ≤ 2) (u : ControlBanach) (m : ℕ) :
    n08BoundedControlDiagonal a z u m = a z m * u m := by
  rw [n08BoundedControlDiagonal_eq a z h, n08ControlDiagonal_apply]

theorem n08BoundedControlDiagonal_inverse (a : Z → ℕ → ℝ) (z : Z)
    (h : ∀ m, (1 / 2 : ℝ) ≤ |a z m| ∧ |a z m| ≤ 2) (u : ControlBanach) :
    n08BoundedControlDiagonalInverse a z (n08BoundedControlDiagonal a z u) = u ∧
      n08BoundedControlDiagonal a z (n08BoundedControlDiagonalInverse a z u) = u := by
  rw [n08BoundedControlDiagonal_eq a z h, n08BoundedControlDiagonalInverse_eq a z h]
  exact ⟨n08ControlDiagonalInverse_left _ _ _ u, n08ControlDiagonalInverse_right _ _ _ u⟩

end DiagonalFamily

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base : ℕ} {ε : ℝ}

def n08ColumnData (hS : IsPhysicalSpaces D T S) (hR : N02Properties D T S C R base ε)
    (H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    (ν : AnnularState S × ℝ → S.Source) : ControlColumnData S where
  restriction := n08ControlRestriction S
  heightColumn := H
  nuColumn := ν
  heightRow := n08HeightRow hS hR
  circleColumn := n08CircleColumn hS hR
  J := n08BoundedControlDiagonal (n08CircleDiagonal hS hR)
  JInverse := n08BoundedControlDiagonalInverse (n08CircleDiagonal hS hR)
  diagonal := n08CircleDiagonal hS hR

end ContinuousFlexibility.Statements
