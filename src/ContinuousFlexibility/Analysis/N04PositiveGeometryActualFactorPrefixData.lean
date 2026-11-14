import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledAngleWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRadialWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryPlaneSavedComposition

/-!
# Factor prefix estimates on the actual parameter space

The generic angle, radial, and angular inverse estimates are specialized
to the sector parameter space before the four factor bounds are assembled.
Their constants remain independent of the component and evaluation state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_actualAnglePrefixData
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order)
    (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (U : Set (StateDirections W.S × ℝ)), IsOpen U →
      ∀ state : (StateDirections W.S × ℝ) → AnnularState W.S × ℝ,
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ J : SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ =>
          G.toN04PositiveGeometryControlData.angularCoefficients (state z.1) i z.2),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          G.toN04PositiveGeometryControlData.angle (state z.1) i z.2),
      ∀ (p q : Seminorm ℝ (StateDirections W.S × ℝ)) (R H t : ℝ),
        0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ (K s shift : ℕ) (x : StateDirections W.S × ℝ), x ∈ U →
      ∀ y : PolarPoint, y.1 ∈ Icc W.D.a W.D.b →
      N04BoundaryWordBounds J K (s + K) 1 x y.2
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift →
      ∀ j : ℕ, 0 < j → j ≤ N → j ≤ K + s + 1 →
      ∀ w : StateAngleWord j, w.stateArity ≤ K →
      ∀ v : Fin j → (StateDirections W.S × ℝ) × PolarPoint,
      (∀ k, if w.isState k then (v k).2 = 0 else (v k).1 = 0) →
      (∀ k, p (v k).1 ≤ 1 ∧ q (v k).1 ≤ R ∧ ‖(v k).2‖ ≤ 1) →
        ‖Q.D j (x, y) v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) :=
  n04PositiveGeometry_controlledAngle_saved_word_bound
    (V := StateDirections W.S × ℝ) G N A RH hA

theorem n04PositiveGeometry_actualRadialPrefixData
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order) (inverse : Bool)
    (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (U : Set (StateDirections W.S × ℝ)), IsOpen U →
      ∀ state : (StateDirections W.S × ℝ) → AnnularState W.S × ℝ,
      (∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε) →
      (∀ x ∈ U, stateSector W.S (state x).1) →
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ J : SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ => fun side (k : Fin (order + 1)) =>
          G.toN04PositiveGeometryControlData.coefficients (state z.1) i side (k + 1) z.2),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint => if inverse then
          G.toN04PositiveGeometryControlData.radialInverse (state z.1) i z.2 else
          G.toN04PositiveGeometryControlData.radial (state z.1) i z.2),
      ∀ (p q : Seminorm ℝ (StateDirections W.S × ℝ)) (R H t : ℝ),
        0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ (K s shift : ℕ) (x : StateDirections W.S × ℝ), x ∈ U → ∀ y : PolarPoint,
      y.1 ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) →
      N04BoundaryWordBounds J K (s + K) 1 x y.2
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift →
      ∀ j : ℕ, 0 < j → j ≤ N → j ≤ K + s + 1 →
      ∀ w : StateAngleWord j, w.stateArity ≤ K →
      ∀ v : Fin j → (StateDirections W.S × ℝ) × PolarPoint,
      (∀ k, if w.isState k then (v k).2 = 0 else (v k).1 = 0) →
      (∀ k, p (v k).1 ≤ 1 ∧ q (v k).1 ≤ R ∧ ‖(v k).2‖ ≤ 1) →
        ‖Q.D j (x, y) v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) :=
  n04PositiveGeometry_controlledRadial_saved_word_bound
    (V := StateDirections W.S × ℝ) G inverse N A RH hA

theorem n04PositiveGeometry_actualInversePrefixData (W : N04RealizationStart) (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
    ∀ (U : Set (StateDirections W.S × ℝ)) (φ : (StateDirections W.S × ℝ) → PolarPoint → ℝ)
      (JF : SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          n04PositiveGeometry_angularGraph (φ z.1) z.2))
      (JG : SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          n04PositiveGeometry_angularGraphInverse (φ z.1) z.2)),
      (∀ z ∈ U, ContDiff ℝ ∞ (φ z)) →
      (∀ z ∈ U, ∀ y : PolarPoint, 0 < deriv (fun θ => φ z (y.1, θ)) y.2) →
      (∀ z ∈ U, ∀ r θ, φ z (r, θ + Real.pi) = φ z (r, θ) + Real.pi) →
    ∀ x ∈ U, ∀ Ω : Set PolarPoint,
      MapsTo (n04PositiveGeometry_angularGraphInverse (φ x)) Ω Ω →
    ∀ (p q : Seminorm ℝ (StateDirections W.S × ℝ)) (R M H t : ℝ),
      0 ≤ R → 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
      (∀ y ∈ Ω, |(deriv (fun θ => φ x (y.1, θ))
        (parameterizedCircleInverse (φ x) y))⁻¹| ≤ M) →
    ∀ K C : ℕ, 1 ≤ C →
      N04PlaneSavedWordBounds JF N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds JG N K C x Ω p q R (A * M ^ degree) H t :=
  n04PositiveGeometry_angularInverse_saved_prefix (E := StateDirections W.S × ℝ) N

end ContinuousFlexibility.Analysis
