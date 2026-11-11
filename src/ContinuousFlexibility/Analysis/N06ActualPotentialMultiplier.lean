import ContinuousFlexibility.Analysis.N06PotentialMultiplier
import ContinuousFlexibility.Analysis.N06CanonicalPotentialRegularity

/-!
# The actual potential difference on the selected N05 source space

The qualitative requirements of the multiplier construction are derived
from the original N01--N04 contracts for the actual current and reference
potentials. Only their quantitative angular jet difference estimate is
left as an input. The multiplier acts on the same original source level
and uses the height of the same original inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- One constant works for every state and every supplied displacement
bound. No smoothness, periodicity or reflection assumption on the actual
potential is added to the original nonlinear construction. -/
theorem n06N05_actualPotentialDifference_multiplier
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (A : ℝ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 i
          (fun q => K.potential z m q - K.potential (C.referenceState, 0) m q) p| ≤
          δ * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (K.cell m)) ^ A) →
      ∃ P : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖P‖ ≤ Q * δ ∧
        ∀ F m, (V.forget (3 / 4 : ℝ) 0 b (P F) m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m] fun p =>
            (K.potential z m p - K.potential (C.referenceState, 0) m p) *
              (B.inverse F).val.1.1 m p := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  obtain ⟨Q, hQ, hmult⟩ := n06N05_potentialMultiplier h01.1.1 hT h.2 A
  refine ⟨Q, hQ, ?_⟩
  intro z hz hs δ hδ hsmall
  apply hmult δ hδ
    (fun m p => K.potential z m p - K.potential (C.referenceState, 0) m p)
  · intro m
    exact (n06_canonicalPotential_contDiffOn hT hS h01 h03 h04 hz hs m).sub
      (n06_canonicalPotential_contDiffOn hT hS h01 h03 h04 href hsector m)
  · intro m p hp
    rw [n06_canonicalPotential_periodicOn hT hS h03 h04 hz hs m hp,
      n06_canonicalPotential_periodicOn hT hS h03 h04 href hsector m hp]
  · intro m p hp
    rw [n06_canonicalPotential_reflectionOn hT hS h03 h04 hz hs m hp,
      n06_canonicalPotential_reflectionOn hT hS h03 h04 href hsector m hp]
  · exact hsmall

end ContinuousFlexibility.Statements
