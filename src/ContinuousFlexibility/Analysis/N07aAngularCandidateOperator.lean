import ContinuousFlexibility.Analysis.N07aAngularCandidateGreen
import ContinuousFlexibility.Analysis.N07aCurrentCanonicalEquation
import ContinuousFlexibility.Analysis.N07aBaseInverse

/-!
# The original homogeneous candidate has zero actual N06 image

The smooth candidate and the existing N06 graph element have identical
canonical coordinates. Their actual compact distribution equations have
the same potential and scalar terms. Subtraction identifies the prescribed
source coordinate with zero, without a new weak-solution certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B} {ε : ℝ}

private theorem n07a_candidate_pairing_sub_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ell : E →L[ℝ] ℝ) (x y a b c d : E)
    (h : ell (x - a - b - c - d) = ell (y - a - b - c - d)) :
    ell x = ell y := by
  simpa only [map_sub, sub_left_inj] using h

theorem n07a_heightPair_canonical_zero_representation
    {z : AnnularState S × ℝ} {u : HeightPair S} {U : CanonicalUnknown S K}
    (haL : U.2.1 = u.2)
    (hU : ∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m ((S.height (3 / 4 : ℝ)).decode u.1)) :
    HasCanonicalRepresentation D S C K z U 0 (heightPairField S u) (fun _ => 0) := by
  constructor
  · intro m
    have he : (fun p => heightPairField S u p - U.2.1 * S.chiLeft p.1) =
        (S.height (3 / 4 : ℝ)).decode u.1 := by
      funext p
      rw [haL]
      exact add_sub_cancel_right _ _
    rw [he]
    exact hU m
  · intro m
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := canonicalMeasure S K m)] with p hp
    simpa only [Pi.zero_apply, canonicalSource, mul_zero, zero_div] using hp

theorem n07a_candidate_zero_distribution
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) (μ : ℝ) (U : CanonicalUnknown S K)
    (haL : U.2.1 = u.2) (hμ : U.2.2.1 = μ) (hAux : U.2.2.2 = 0)
    (hU : ∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u.1))
    (heq : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u) p + μ * nuColumnField D S C (liftSectorParameter S C z) p = 0)
    (m : ℕ) (hm : K.left m < K.right m) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (liftSectorParameter S C z) m)
      (U.1 m) (n07aCurrentCanonicalRhs href hcur z hz m hm U 0) := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  have hheight := (hS.1 (3 / 4 : ℝ)).2.2.2.1 u.1
  have hη : ContDiffOn ℝ ∞ (heightPairField S u) (annularOpen D) :=
    hheight.1.add (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)).contDiffOn
  have hηπ : Function.Periodic (heightPairField S u) (0, Real.pi) := by
    intro p
    simp only [heightPairField, hheight.2.2.1 p, Prod.fst_add, add_zero]
  have hrep := n07a_heightPair_canonical_zero_representation (D := D) (C := C) haL hU
  intro W hW
  apply n07a_canonical_distribution_test_pairing hab h04 hz' hs hS.2.2.1.1
    hrep hηπ (fun _ => rfl)
    (n07aCurrentOpenCoefficient href hcur z hz m hm 0)
    (n07aCurrentOpenCoefficient href hcur z hz m hm 1)
    (n07aCurrentOpenCoefficient href hcur z hz m hm 2)
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aCurrentOpenCoefficient href hcur z hz m hm 4))
    (n07aCurrentScalarOpenCoefficient href hcur z hz m hm)
    rfl rfl rfl rfl (fun _ => rfl) hW
  simpa only [hμ, hAux, zero_mul, mul_zero, add_zero, intervalIntegral.integral_zero,
    radialAngularMean] using
    n07a_candidate_homogeneous_pulledTest_pairing hab hS hT h01 h03 h04
      hz' hs hη hηπ heq hW

theorem n07a_candidate_operator_eq_zero
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) (μ : ℝ) (d : B.Space)
    (haL : d.val.1.2.1 = u.2) (hμ : d.val.1.2.2.1 = μ) (hAux : d.val.1.2.2.2 = 0)
    (hU : ∀ m, (d.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u.1))
    (heq : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u) p + μ * nuColumnField D S C (liftSectorParameter S C z) p = 0) :
    P.operator (liftSectorParameter S C z) d = 0 := by
  apply hV.2.2.1 (3 / 4 : ℝ) 0 b
  rw [map_zero]
  funext m
  apply n07a_canonical_test_separation (h04.1.referenceBounds m).2.1
  intro W hW
  have hc := n07a_currentOperator_distribution hab hS h01.2.2.1 h04 href hcur h06
    z hz m (h04.1.referenceBounds m).2.1 d W hW
  have hzero := n07a_candidate_zero_distribution hab hS hT h01 h03 h04 href hcur
    z hz u μ d.val.1 haL hμ hAux hU heq m (h04.1.referenceBounds m).2.1 W hW
  let ell : CanonicalL2 S K m →L[ℝ] ℝ :=
    n07aCanonicalTestPairing W (n07a_canonicalTest_memLp hW)
  let F : CanonicalSequence S K :=
    V.forget (3 / 4 : ℝ) 0 b (P.operator (liftSectorParameter S C z) d)
  have hpair : ell (n07aCurrentCanonicalRhs href hcur z hz m
      (h04.1.referenceBounds m).2.1 d.val.1 F) =
      ell (n07aCurrentCanonicalRhs href hcur z hz m
        (h04.1.referenceBounds m).2.1 d.val.1 0) :=
    (n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW) _).trans
      ((hc.symm.trans hzero).trans
        (n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW) _).symm)
  have hbase : ell (F m) = ell (0 : CanonicalL2 S K m) :=
    n07a_candidate_pairing_sub_four ell (F m) 0 _ _ _ _ hpair
  exact (n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW) _).symm.trans
    (hbase.trans (n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW) _))

end ContinuousFlexibility.Analysis
