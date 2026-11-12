import ContinuousFlexibility.Analysis.N07aRelativeCanonicalPairing
import ContinuousFlexibility.Analysis.N07aCanonicalDifference

/-!
# The actual relative operator on a negative piece

The principal coefficients coincide as genuine germs. The local relative
source is therefore exactly the actual potential and scalar-column
differences in the original canonical L² space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

theorem n07a_canonical_negative_divergence_eq
    (h04 : N04Properties D T S C L K base loss ε)
    {z z₀ : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
    (m : ℕ) (hm : K.positive m = false) (u : PolarPoint → ℝ) :
    EqOn (divergenceOperator (K.coefficients z m) u)
      (divergenceOperator (K.coefficients z₀ m) u) (canonicalOpen S K m) := by
  have hn := h04.2.1.2.2.2.1
  intro p hp
  have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  apply n07a_divergenceOperator_eq_of_germs
  · filter_upwards [hnear] with q hq
    exact (hn z hz hs m hm q hq).1.trans (hn z₀ hz₀ hs₀ m hm q hq).1.symm
  · filter_upwards [hnear] with q hq
    exact (hn z hz hs m hm q hq).2.1.trans (hn z₀ hz₀ hs₀ m hm q hq).2.1.symm
  · filter_upwards [hnear] with q hq
    exact (hn z hz hs m hm q hq).2.2.trans (hn z₀ hz₀ hs₀ m hm q hq).2.2.symm

theorem n07a_relativeCanonical_negative
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m)
    (hneg : K.positive m = false) :
    V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m =
      n07aRelativeCanonicalLower href hcur z hz m hm (B.inverse F).val.1 := by
  apply n07aAngularWeak_unique m hm (k := 0)
    (f := V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m)
  · intro W hW
    simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
  · intro W hW
    have h := n07a_relativeCanonical_pairing hab hS hT h01 h02 h03 h04 href hcur
      h05 h06 z hz F m hm hW
    have hdiv := n07a_canonical_negative_divergence_eq h04
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z)
      (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m hneg W
    have he : (fun p => (B.inverse F).val.1.1 m p *
        (divergenceOperator (K.coefficients (liftSectorParameter S C z) m) W p -
          divergenceOperator (K.coefficients (C.referenceState, 0) m) W p))
        =ᵐ[canonicalMeasure S K m] fun _ => (0 : ℝ) := by
      filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
      rw [hdiv hp, sub_self, mul_zero]
    have hIntegralZero : (∫ p, (B.inverse F).val.1.1 m p *
        (divergenceOperator (K.coefficients (liftSectorParameter S C z) m) W p -
          divergenceOperator (K.coefficients (C.referenceState, 0) m) W p)
          ∂canonicalMeasure S K m) = 0 :=
      (integral_congr_ae he).trans (integral_zero _ _)
    have hzero := congrArg (fun x : ℝ => x +
      ∫ p, n07aRelativeCanonicalLower href hcur z hz m hm (B.inverse F).val.1 p * W p
        ∂canonicalMeasure S K m) hIntegralZero
    have hpair := h.trans (hzero.trans (zero_add _))
    simpa only [pow_zero, one_mul, spaces_mixedDerivative_zero] using hpair.symm

end ContinuousFlexibility.Analysis
