import ContinuousFlexibility.Analysis.WholeReferenceGaugeRelativeFields
import ContinuousFlexibility.Analysis.CanonicalActualWholeGeometry

/-!
# The same global relative transport after fixing the reference gauge

The reference chart and height change the raw positive fields, but cancel
from the actual relative maps and height ratio. The physical pieces stay
the same. Consequently the already constructed global C3 transport and
positive height ratio belong to the new record, without a second choice
of flows, collars, or a global extension.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeReferenceGaugeAtlasData_relative_fields_eq
    (z : AnnularState S × ℝ)
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    (hχψ : ∀ i, Function.LeftInverse (χ i) (ψ i))
    (hστ : ∀ i, Function.LeftInverse (σ z i) (τ z i))
    (hh₀ : ∀ i p, h₀ i p ≠ 0) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
    ∀ m, canonicalCurrentPoint C V z m = canonicalCurrentPoint C W z m ∧
      canonicalReferencePoint C V z m = canonicalReferencePoint C W z m ∧
      n04CoordinatesCurrentHeightRatio C V z m =
        n04CoordinatesCurrentHeightRatio C W z m := by
  dsimp only
  intro m
  cases hi : e m with
  | inl j =>
      simp [canonicalCurrentPoint, canonicalReferencePoint,
        n04CoordinatesCurrentHeightRatio, n04WholeReferenceGaugeAtlasData,
        n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi]
  | inr i =>
      have hv := n04WholeReferenceGaugeAtlasData_positive_relative_fields
        C L K e cell ψ χ h₀ τ σ Q N z m i hi
        (href i).1 (href i).2.1 (href i).2.2 (hχψ i) (hστ i) (hh₀ i)
      have hw := n04WholeCanonicalAtlasData_positive_relative_fields
        C L K e cell σ τ Q N z m i hi (href i).2.1 (href i).2.2 (hστ i)
      refine ⟨hv.1.trans hw.1.symm, ?_, hv.2.2.trans hw.2.symm⟩
      have hreference : canonicalReferencePoint C
          (n04WholeCanonicalAtlasData C L K e cell σ τ Q N) z m = σ z i := by
        funext p
        simp only [canonicalReferencePoint, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi, (href i).1, id_eq]
      exact hv.2.1.trans hreference.symm

theorem n04WholeReferenceGaugeAtlasData_global_transport
    (z : AnnularState S × ℝ) (F : PolarPoint → PolarPoint) (q : PolarPoint → ℝ)
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    (hχψ : ∀ i, Function.LeftInverse (χ i) (ψ i))
    (hστ : ∀ i, Function.LeftInverse (σ z i) (τ z i))
    (hh₀ : ∀ i p, h₀ i p ≠ 0)
    (hW : WholeCanonicalTransportQualitative (D := D) C
      (n04WholeCanonicalAtlasData C L K e cell σ τ Q N) z F q) :
    WholeCanonicalTransportQualitative (D := D) C
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N) z F q := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q N
  have hrelative := n04WholeReferenceGaugeAtlasData_relative_fields_eq
    C L K e cell ψ χ h₀ τ σ Q N z href hχψ hστ hh₀
  obtain ⟨hF, hq, hmap, hperiod, hqperiod, hreflect, hqeven, hfields, hpos⟩ := hW
  refine ⟨hF, hq, hmap, hperiod, hqperiod, hreflect, hqeven, ?_, hpos⟩
  intro m p hp
  have hpW : p ∈ referencePhysicalPieceOpen S W m := hp
  have hf := hfields m p hpW
  have hcurrent : F p = canonicalCurrentPoint C V z m p :=
    hf.1.trans (congrFun (hrelative m).1 p).symm
  refine ⟨hcurrent, ?_⟩
  calc
    q p = n04CoordinatesCurrentHeightRatio C W z m p := by
      simpa only [n04CoordinatesCurrentHeightRatio, ← hf.1] using hf.2
    _ = n04CoordinatesCurrentHeightRatio C V z m p :=
      (congrFun (hrelative m).2.2 p).symm
    _ = V.height (C.referenceState, 0) m p / V.height z m (F p) := by
      rw [n04CoordinatesCurrentHeightRatio, ← hcurrent]

end ContinuousFlexibility.Analysis
