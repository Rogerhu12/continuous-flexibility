import ContinuousFlexibility.Analysis.N04RealizationLeadStart
import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapComponents
import ContinuousFlexibility.Analysis.MorseRealizationComponentOrder
import Mathlib.Data.Nat.Pairing

/-!
# Infinitely many positive components of the same retained start

The positive Morse gaps already recognized in the retained reference have
strictly increasing right endpoints on the right tail. They therefore give
an embedding of the natural numbers, and hence of pairs of natural numbers,
into the actual positive-component index type.

No new reference profile, source enumeration, or material data is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

/-- The positive gap at the indicated retained index on the right tail. -/
def n04PositiveGeometry_tailComponent (W : N04RealizationStart) (n : ℕ) :
    N04PositiveComponent W.D.a W.D.b (deriv W.D.w) :=
  (retainedReference_positive_gap_is_component W.P W.metadata.selected
    W.metadata.first_two W.realizes W.hw W.coordinates true
    (n := W.S₀.chain.index + n) (Nat.le_add_right _ _)).choose

/-- Its right endpoint is the original left turning root of the next model. -/
theorem n04PositiveGeometry_tailComponent_right (W : N04RealizationStart) (n : ℕ) :
    n04PositiveRight (n04PositiveGeometry_tailComponent W n) =
      W.P.sideRadius true * n06MorsePositiveRight W.S₀.chain true (W.S₀.chain.index + n) :=
  (retainedReference_positive_gap_is_component W.P W.metadata.selected
    W.metadata.first_two W.realizes W.hw W.coordinates true
    (n := W.S₀.chain.index + n) (Nat.le_add_right _ _)).choose_spec.1.2

/-- The original ordering of the Morse models separates these right endpoints. -/
theorem n04PositiveGeometry_tailComponent_right_strictMono (W : N04RealizationStart) :
    StrictMono (fun n => n04PositiveRight (n04PositiveGeometry_tailComponent W n)) := by
  have hreal : MorseChainRealization W.S₀.chain W.S₀.sigma
      (W.S₀.family W.S₀.sigma) W.S₀.constants :=
    (W.metadata.selected.2.2.2.1 W.S₀.sigma W.metadata.selected.2.2.1).1
  have hm := (morseRealization_turning_component_order hreal).2.1
  intro m n hmn
  change n04PositiveRight (n04PositiveGeometry_tailComponent W m) <
    n04PositiveRight (n04PositiveGeometry_tailComponent W n)
  rw [n04PositiveGeometry_tailComponent_right W m,
    n04PositiveGeometry_tailComponent_right W n]
  have hroot := hm (Nat.add_lt_add_right hmn 1)
  have hscaled := mul_lt_mul_of_pos_left hroot (W.P.sideRadius_pos true)
  simpa only [n06MorsePositiveRight, ↓reduceIte, Nat.add_assoc] using hscaled

/-- A countably infinite family of distinct actual positive components. -/
def n04PositiveGeometry_tailEmbedding (W : N04RealizationStart) :
    ℕ ↪ N04PositiveComponent W.D.a W.D.b (deriv W.D.w) where
  toFun := n04PositiveGeometry_tailComponent W
  inj' := by
    intro m n h
    exact (n04PositiveGeometry_tailComponent_right_strictMono W).injective
      (congrArg n04PositiveRight h)

/-- Paired natural indices can be assigned distinct actual components before
a proposed exponent and derivative loss are known. -/
def n04PositiveGeometry_pairEmbedding (W : N04RealizationStart) :
    (ℕ × ℕ) ↪ N04PositiveComponent W.D.a W.D.b (deriv W.D.w) where
  toFun := fun i => n04PositiveGeometry_tailEmbedding W (Nat.pair i.1 i.2)
  inj' := by
    intro i j h
    have hp := (n04PositiveGeometry_tailEmbedding W).injective h
    have hu := congrArg Nat.unpair hp
    simpa only [Nat.unpair_pair] using hu

end ContinuousFlexibility.Analysis
