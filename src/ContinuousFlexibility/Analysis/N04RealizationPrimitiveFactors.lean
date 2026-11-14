import ContinuousFlexibility.Analysis.N04RealizationPrimitiveMaterialJets

/-!
# Finite envelopes of the existing primitive factors

This proposition records estimates of existing functions only. It adds
no map, coefficient, source factor or geometric representative. Its
constructor is proved from the actual chart and scalar-atom estimates.
The final fifteen primitive estimates are not fields of this record.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

/-- All factor jets are evaluated on the same material point and piece.
The extra order supplies the derivative in the exact density drift. -/
structure N04RealizationPrimitiveFactorEnvelopes
    (X : Type*) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (W : X → ℝ) (z : X → AnnularState S × ℝ)
    (m : X → ℕ) (p : X → PolarPoint) (N : ℕ) : Prop where
  currentPoint : ∀ j : ℕ, 0 < j → j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (K.chart (z x) (m x) ∘ n07bMaterialRadiusChart T) (p x)‖)
  referencePoint : ∀ j : ℕ, 0 < j → j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (canonicalReferencePoint C K (z x) (m x) ∘ n07bMaterialRadiusChart T) (p x)‖)
  inverseDifferential : ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (fun y => fderiv ℝ (K.inverseChart (z x) (m x))
        (K.chart (z x) (m x) (n07bMaterialRadiusChart T y))) (p x)‖)
  referenceDifferential : ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (fun y => fderiv ℝ (K.chart (C.referenceState, 0) (m x))
        (canonicalReferencePoint C K (z x) (m x) (n07bMaterialRadiusChart T y))) (p x)‖)
  inverseJacobian : ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (fun y => |planeJacobian (K.inverseChart (z x) (m x))
        (K.chart (z x) (m x) (n07bMaterialRadiusChart T y))|) (p x)‖)
  referenceJacobian : ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (fun y => |planeJacobian (K.chart (C.referenceState, 0) (m x))
        (canonicalReferencePoint C K (z x) (m x) (n07bMaterialRadiusChart T y))|) (p x)‖)
  density : ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (canonicalMaterialJacobian T K (z x) (m x) ∘ n07bMaterialRadiusChart T) (p x)‖)
  inverseDensity : ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (fun y => (canonicalMaterialJacobian T K (z x) (m x)
        (n07bMaterialRadiusChart T y))⁻¹) (p x)‖)
  source : ∀ reference inv : Bool, ∀ j : ℕ, j ≤ N + 1 → HasPositiveEnvelope W
    (fun x => ‖iteratedFDeriv ℝ j
      (fun y => if inv then
        (canonicalSource S K (if reference then (C.referenceState, 0) else z x) (m x)
          (fun _ => 1) (K.chart (z x) (m x) (n07bMaterialRadiusChart T y)))⁻¹
        else canonicalSource S K (if reference then (C.referenceState, 0) else z x) (m x)
          (fun _ => 1) (K.chart (z x) (m x) (n07bMaterialRadiusChart T y))) (p x)‖)

end ContinuousFlexibility.Analysis
