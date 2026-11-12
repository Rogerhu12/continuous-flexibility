import ContinuousFlexibility.Analysis.N06LeftColumnSources
import ContinuousFlexibility.Analysis.N06ReferenceChartNuSource

/-!
# The true left-column difference as a small reference-chart source

The physical difference uses the original cutoff S.chiLeft and the
actual corrected coefficients. Its uniform angular jet estimate and
common compact support produce a source in the same selected V.level.
The constant is chosen before the state. The representative identity
uses the reference chart explicitly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

private theorem n06_family_radius_mono {Z : Type*}
    (lo hi : Z → ℝ) (Ad₁ Ad₂ : Z → Prop) (Jets : Z → ℝ → Prop)
    (hle : ∀ z, lo z ≤ hi z)
    (h : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → lo z ≤ 1 → Jets z (Q * hi z)) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → hi z ≤ 1 → Jets z (Q * hi z) := by
  obtain ⟨Q, hQ, hbound⟩ := h
  exact ⟨Q, hQ, fun z hz₁ hz₂ hsmall => hbound z hz₁ hz₂ ((hle z).trans hsmall)⟩

private def N06LeftColumnHighRadiusBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ) (b : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (max base (b + 1 + loss)) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ j, j ≤ b → ∀ p ∈ annularOpen D,
      |mixedDerivative 0 j (n06LeftColumnDifference D S L z) p| ≤
        Q * (stateGrading S (max base (b + 1 + loss)) (z.1 - C.referenceState) + |z.2|)

private theorem n06_leftColumnDifference_highRadius_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06LeftColumnHighRadiusBound D S C L base loss ε b Q := by
  exact n06_family_radius_mono (Z := AnnularState S × ℝ)
    (fun z => stateGrading S base (z.1 - C.referenceState) + |z.2|)
    (fun z => stateGrading S (max base (b + 1 + loss)) (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z δ => ∀ j, j ≤ b → ∀ p ∈ annularOpen D,
      |mixedDerivative 0 j (n06LeftColumnDifference D S L z) p| ≤ δ)
    (fun z => add_le_add
      (solve_stateGrading_monotone S (le_max_left _ _) (z.1 - C.referenceState))
      (le_refl |z.2|))
    (n06_leftColumnDifference_finiteAngular_bound hT hS h01 h03 b)

def N06ReferenceChartLeftDifferenceBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (V : VolumeModelData S K)
    (base loss : ℕ) (ε γ t : ℝ) (b : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (max base (b + 1 + loss)) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06LeftColumnDifference D S L z)) ∧
      ‖F‖ ≤ Q *
        (stateGrading S (max base (b + 1 + loss)) (z.1 - C.referenceState) + |z.2|)

/-- The actual physical left-column difference has a linearly small
source in every fixed reference-chart level of the selected volume model.
No normalization-region support assumption is used. -/
theorem n06Volume_exists_referenceChart_leftDifference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (γ t : ℝ) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      N06ReferenceChartLeftDifferenceBound D S C L K V base loss ε γ t b Q := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.2
  obtain ⟨J, hJ, hJD, hzero⟩ := n06_leftColumnDifferences_commonSupport hS h01 h03
  have hsource := n06Volume_controlled_reference_source_norm
    (D := D) (T := T) (S := S) (C := C) (K := K) (V := V)
    hT hV h hcoordinates γ t b hJ hJD
  have hjets := n06_leftColumnDifference_highRadius_bound hT hS h01 h03 b
  exact n06_source_family_norm_bound
    (X := AnnularState S × ℝ) (A := PolarPoint → ℝ) (Y := V.level γ t b)
    (fun f => ContDiff ℝ ∞ f)
    (fun f => Function.Periodic f (0, Real.pi))
    (fun f => ∀ p : PolarPoint, f (p.1, -p.2) = f p)
    (fun f => ∀ r, r ∉ J → ∀ θ, f (r, θ) = 0)
    (fun δ f => ∀ j, j ≤ b → ∀ p ∈ annularOpen D,
      |mixedDerivative 0 j f p| ≤ δ)
    (fun f F => ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m f)
    (n06LeftColumnDifference D S L)
    (fun z => stateGrading S (max base (b + 1 + loss))
      (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z => add_nonneg
      (apply_nonneg (stateGrading S (max base (b + 1 + loss))) (z.1 - C.referenceState))
      (abs_nonneg z.2))
    (fun z hz hs => by
      have hregular := n06_leftColumnDifference_regular hT hS h01 h03 hz hs
      exact ⟨hregular.1, hregular.2.1, hregular.2.2, hzero z⟩)
    hjets hsource

end ContinuousFlexibility.Statements
