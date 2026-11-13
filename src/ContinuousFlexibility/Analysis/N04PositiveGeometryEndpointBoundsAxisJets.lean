import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPlaneJets
import ContinuousFlexibility.Analysis.BoundaryMixedJets

/-!
# Full boundary jets from the actual finite radial traces

The model is smooth on an open set containing its entire boundary axis.
Finite coordinate words are angular derivatives of its radial traces.
Once those traces have genuine parameter towers, the original full jet
inherits their towers and bounds, with only the finite angular reserve
spent on the coordinate words.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_planeWordRadial {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ i, if w i = 0 then 1 else 0

def n04PositiveGeometry_planeWordAngular {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ i, if w i = 0 then 0 else 1

theorem n04PositiveGeometry_planeWord_orders {n : ℕ} (w : Fin n → Fin 2) :
    n04PositiveGeometry_planeWordRadial w + n04PositiveGeometry_planeWordAngular w = n := by
  unfold n04PositiveGeometry_planeWordRadial n04PositiveGeometry_planeWordAngular
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin n, (1 : ℕ) := Finset.sum_congr rfl (fun i _ => by
      by_cases hi : w i = 0 <;> simp only [hi, ite_true, ite_false, zero_add, add_zero])
    _ = n := by simp

theorem n04PositiveGeometry_axisBasis_eq_radialTrace
    {Ω : Set PolarPoint} (hΩ : IsOpen Ω) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (r : ℝ) (hr : ∀ θ, (r, θ) ∈ Ω)
    (n : ℕ) (w : Fin n → Fin 2) (θ : ℝ) :
    iteratedFDeriv ℝ n f (r, θ) (fun i => cylinderBasisVector (w i)) =
      iteratedDeriv (n04PositiveGeometry_planeWordAngular w)
        (radialBoundaryJet f r (n04PositiveGeometry_planeWordRadial w)) θ :=
  (iteratedFDeriv_cylinderBasis_eq_mixedDerivative hΩ hf n (hr θ) w).trans
    (iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hΩ hf r hr _ _ θ).symm

variable {X : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X}

/-- A fixed number of actual angular derivatives spends exactly that
many reserved orders and keeps every parameter slot. -/
theorem N04BoundaryWordBounds.angularIterate
    {f : X × ℝ → ℝ} {J : SmoothDirections (U ×ˢ univ) f}
    (b : ℕ) {K s d : ℕ} {x : X} {θ : ℝ} {P : X → Prop}
    {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s (d + b) x θ P M H t shift)
    (hx : x ∈ U) (hU : Convex ℝ U) (hP : P 0) :
    N04BoundaryWordBounds (smoothDirections_angularIterate J b)
      K s d x θ P M H t shift := by
  induction b generalizing d with
  | zero =>
      exact h.congr hx (fun y _ => by simp only [iteratedDeriv_zero])
  | succ b ih =>
      have hprev : N04BoundaryWordBounds (smoothDirections_angularIterate J b)
          K s (d + 1) x θ P M H t shift :=
        ih (d := d + 1)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      exact (hprev.angular hx hU hP).congr hx (fun y _ => by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero])

variable {n : ℕ} {A : X × ℝ → PolarPoint [×n]→L[ℝ] ℝ}
  {f : ℕ → X × ℝ → ℝ}

private def axisBasisDirections
    (J : ∀ a, a ≤ n → SmoothDirections (U ×ˢ univ) (f a))
    (he : ∀ w : Fin n → Fin 2, ∀ y ∈ U ×ˢ (univ : Set ℝ),
      A y (fun i => cylinderBasisVector (w i)) =
        iteratedDeriv (n04PositiveGeometry_planeWordAngular w)
          (fun θ => f (n04PositiveGeometry_planeWordRadial w) (y.1, θ)) y.2)
    (w : Fin n → Fin 2) :
    SmoothDirections (U ×ˢ univ)
      (fun y => A y (fun i => cylinderBasisVector (w i))) := by
  have ha : n04PositiveGeometry_planeWordRadial w ≤ n := by
    have hc := n04PositiveGeometry_planeWord_orders w
    omega
  exact (smoothDirections_angularIterate (J _ ha)
    (n04PositiveGeometry_planeWordAngular w)).congr (fun y hy => (he w y hy).symm)

/-- The field is the existing multilinear jet, not a newly chosen
extension. Only the finite radial traces need parameter regularity. -/
def n04PositiveGeometry_axisJet_directions
    (J : ∀ a, a ≤ n → SmoothDirections (U ×ˢ univ) (f a))
    (he : ∀ w : Fin n → Fin 2, ∀ y ∈ U ×ˢ (univ : Set ℝ),
      A y (fun i => cylinderBasisVector (w i)) =
        iteratedDeriv (n04PositiveGeometry_planeWordAngular w)
          (fun θ => f (n04PositiveGeometry_planeWordRadial w) (y.1, θ)) y.2) :
    SmoothDirections (U ×ˢ univ) A :=
  n04PositiveGeometry_planeBasis_directions n A (axisBasisDirections J he)

/-- Radial reserve `d + n` suffices for full spatial order `n` with
reserve `d`. The only reconstruction cost is `2 ^ n`. -/
theorem N04BoundaryWordBounds.of_axisRadialTraces
    (J : ∀ a, a ≤ n → SmoothDirections (U ×ˢ univ) (f a))
    (Q : SmoothDirections (U ×ˢ univ) A)
    (he : ∀ w : Fin n → Fin 2, ∀ y ∈ U ×ˢ (univ : Set ℝ),
      A y (fun i => cylinderBasisVector (w i)) =
        iteratedDeriv (n04PositiveGeometry_planeWordAngular w)
          (fun θ => f (n04PositiveGeometry_planeWordRadial w) (y.1, θ)) y.2)
    {K s d : ℕ} {x : X} (hx : x ∈ U) (hU : Convex ℝ U)
    {θ : ℝ} {P : X → Prop} (hP : P 0)
    {M H t : ℝ} {shift : ℕ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (h : ∀ a (ha : a ≤ n),
      N04BoundaryWordBounds (J a ha) K s (d + n) x θ P M H t shift) :
    N04BoundaryWordBounds Q K s d x θ P ((2 : ℝ) ^ n * M) H t shift := by
  apply N04BoundaryWordBounds.of_planeBasis Q (axisBasisDirections J he) hx
    hM hH (zero_le_one.trans ht)
  intro w
  have hc := n04PositiveGeometry_planeWord_orders w
  have ha : n04PositiveGeometry_planeWordRadial w ≤ n := by omega
  have hb : n04PositiveGeometry_planeWordAngular w ≤ n := by omega
  have hreserve := (h _ ha).reserve hM hH ht (Nat.add_le_add_left hb d)
  have hangle := N04BoundaryWordBounds.angularIterate
    (n04PositiveGeometry_planeWordAngular w) (d := d) hreserve hx hU hP
  exact hangle.congr hx (fun y hy => (he w y hy).symm)

end ContinuousFlexibility.Analysis
