import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamily
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.N01cStateAngleSelections

/-!
# The common sampled word budget of the two actual transports

Only positive joint orders are bounded. The state arity remains within
the original parameter prefix, and the estimate is used on the physical
open slab. In particular it does not bound the value of an angular lift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

def N04PositiveGeometryTransportSamplePrefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order)
    (inverse : Bool) (base : ℕ) (ε : ℝ) : Prop :=
  ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
    ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
    ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint => if inverse then
        G.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C z.1) i z.2
        else G.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2),
    ∀ x ∈ sectorNeighborhood W.S base ε ε,
    pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
    ∀ q ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ),
    ∀ R : ℝ, 1 ≤ R →
    pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
    ∀ n : ℕ, 0 < n → n ≤ K + s + 1 →
    ∀ w : StateAngleWord n, w.stateArity ≤ K →
    ∀ v : Fin n → (StateDirections W.S × ℝ) × PolarPoint,
    (∀ j, if w.isState j then (v j).2 = 0 else (v j).1 = 0) →
    (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j).1 ≤ 1 ∧
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) (v j).1 ≤ R ∧
      ‖(v j).2‖ ≤ 1) →
      ‖Q.D n (x, q) v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) w.stateArity *
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) ^
          (w.angleArity + shift * w.stateArity - 1)

abbrev N04PositiveGeometryInverseTransportSamplePrefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order) (base : ℕ) (ε : ℝ) : Prop :=
  N04PositiveGeometryTransportSamplePrefix G true base ε

end ContinuousFlexibility.Analysis
