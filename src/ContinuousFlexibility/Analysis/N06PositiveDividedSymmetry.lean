module

public import ContinuousFlexibility.Analysis.N06PositiveCanonicalSymmetry

/-!
# Symmetries of the actual positive cubic quotients

The original interior factorization determines the quotients uniquely.
Consequently the proved current/reference principal symmetries give the
period and even/odd/even reflection of these actual divided coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_positive_dividedCoefficients_periodicOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    (hreg : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    (href : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).c (canonicalOpen S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (K.dividedDifference z m).a (p + (0, Real.pi)) = (K.dividedDifference z m).a p ∧
      (K.dividedDifference z m).b (p + (0, Real.pi)) = (K.dividedDifference z m).b p ∧
      (K.dividedDifference z m).c (p + (0, Real.pi)) = (K.dividedDifference z m).c p := by
  have hp' : p + (0, Real.pi) ∈ canonicalOpen S K m :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  have hcur := n06_positive_canonical_coefficients_periodicOn hT hS h01 h03 h04
    hz hs m hm hreg hp
  have hzero := n06_positive_canonical_coefficients_periodicOn hT hS h01 h03 h04
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m hm href hp
  have hQ := canonicalDividedDifference_eq_quotient (n06_N04_qualitative_parts h04).2 hz hs m hm hp
  have hQ' := canonicalDividedDifference_eq_quotient (n06_N04_qualitative_parts h04).2 hz hs m hm hp'
  simp only [Prod.fst_add, add_zero] at hQ'
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ'.1, hQ.1, hcur.1, hzero.1]
  · rw [hQ'.2.1, hQ.2.1, hcur.2.1, hzero.2.1]
  · rw [hQ'.2.2, hQ.2.2, hcur.2.2, hzero.2.2]

theorem n06_positive_dividedCoefficients_reflectionOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    (hreg : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    (href : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).c (canonicalOpen S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (K.dividedDifference z m).a (p.1, Real.pi - p.2) = (K.dividedDifference z m).a p ∧
      (K.dividedDifference z m).b (p.1, Real.pi - p.2) = -(K.dividedDifference z m).b p ∧
      (K.dividedDifference z m).c (p.1, Real.pi - p.2) = (K.dividedDifference z m).c p := by
  have hp' : (p.1, Real.pi - p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hcur := n06_positive_canonical_coefficients_reflectionOn hT hS h01 h03 h04
    hz hs m hm hreg hp
  have hzero := n06_positive_canonical_coefficients_reflectionOn hT hS h01 h03 h04
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m hm href hp
  have hQ := canonicalDividedDifference_eq_quotient (n06_N04_qualitative_parts h04).2 hz hs m hm hp
  have hQ' := canonicalDividedDifference_eq_quotient (n06_N04_qualitative_parts h04).2 hz hs m hm hp'
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ'.1, hQ.1, hcur.1, hzero.1]
  · rw [hQ'.2.1, hQ.2.1, hcur.2.1, hzero.2.1]
    ring
  · rw [hQ'.2.2, hQ.2.2, hcur.2.2, hzero.2.2]

end ContinuousFlexibility.Statements
