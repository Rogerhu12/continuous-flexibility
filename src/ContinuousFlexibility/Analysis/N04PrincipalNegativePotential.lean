import ContinuousFlexibility.Analysis.N04PrincipalNegativeJets
import ContinuousFlexibility.Analysis.N04RealizationPotentialIdentity
import ContinuousFlexibility.Analysis.N07aCanonicalDifference
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
import ContinuousFlexibility.Analysis.N07aLocalPullbackEquation

/-!
# The negative potential in the canonical unit variable

The negative principal field is fixed.  Testing the physical action on
the constant function therefore expresses the potential using only the
pulled height, its reciprocal, and two spatial derivatives.  The affine
length factor is retained explicitly, so both negative halves use one
formula without a change of representation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

/-- The negative normal-form identity only needs the operator part of the
atlas; the quantitative N04 clauses are not hypotheses. -/
theorem n04PrincipalNegative_divergence_formula
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {v : PolarPoint → ℝ} (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m)) :
    EqOn (divergenceOperator (K.coefficients z m) v)
      (fun p => mixedDerivative 2 0 v p - p.1 * mixedDerivative 0 2 v p)
      (canonicalOpen S K m) := by
  let A : SymmetricCoefficients := ⟨fun _ => 1, fun _ => 0, fun q => -q.1⟩
  have hopen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hvr : ContDiffOn ℝ ∞ (radialPartial v) (canonicalOpen S K m) :=
    (hv.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  have hvt : ContDiffOn ℝ ∞ (angularPartial v) (canonicalOpen S K m) :=
    (hv.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  intro p hp
  have hnear := hopen.mem_nhds hp
  have hsame : divergenceOperator (K.coefficients z m) v p = divergenceOperator A v p := by
    apply n07a_divergenceOperator_eq_of_germs
    · filter_upwards [hnear] with q hq
      exact (hB.2.2.2.1 z hz hs m hm q hq).1
    · filter_upwards [hnear] with q hq
      exact (hB.2.2.2.1 z hz hs m hm q hq).2.1
    · filter_upwards [hnear] with q hq
      exact (hB.2.2.2.1 z hz hs m hm q hq).2.2
  have hrr := (radialPartial_eq_mixedDerivative_on hopen hvr hp).trans
    (mixedDerivative_radialPartial hopen hv 1 0 hp)
  have htt := (angularPartial_eq_mixedDerivative_on hopen hvt hp).trans
    (mixedDerivative_angularPartial hopen hv 0 1 hp)
  have hneg : angularPartial (fun q : PolarPoint => -q.1) p = 0 := by
    simp [angularPartial, fderiv_fun_neg, fderiv_fst]
  rw [hsame]
  change radialPartial (fun q => 1 * radialPartial v q + 0 * angularPartial v q) p +
    angularPartial (fun q => 0 * radialPartial v q + -q.1 * angularPartial v q) p = _
  simp only [one_mul, zero_mul, add_zero, zero_add]
  change radialPartial (radialPartial v) p +
    angularPartial (fun q : PolarPoint => -q.1 * angularPartial v q) p =
      mixedDerivative 2 0 v p - p.1 * mixedDerivative 0 2 v p
  rw [angularPartial_mul (f := fun q : PolarPoint => -q.1) differentiableAt_fst.neg
    ((hvt.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)), hneg, hrr, htt]
  ring

/-- Reciprocal pulled height is spatially smooth on its actual canonical
piece, directly from the qualitative inverse-chart and height data. -/
theorem n04PrincipalNegative_reciprocal_pulledHeight_smooth
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun q => (K.height z m (K.inverseChart z m q))⁻¹)
      (canonicalOpen S K m) := by
  have hc := hA.charts z hz hs m
  exact (hc.2.2.2.2.2.2.1.comp hc.2.2.2.2.2.1 hc.2.1).inv
    (fun q hq => (hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)).1.ne')

/-- Exact unit-strip expression for the actual negative potential.  The
only two nonconstant inputs are the pulled height and its reciprocal. -/
theorem n04PrincipalNegative_potential_unit_formula
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    let H : PolarPoint → ℝ := fun p =>
      K.height z m (K.inverseChart z m (canonicalUnitPoint K m p))
    atom D T S C L K z m .potential q =
      -H q * ((K.right m - K.left m)⁻¹ ^ 2 *
        mixedDerivative 2 0 (fun p => (H p)⁻¹) q -
          (canonicalUnitPoint K m q).1 * mixedDerivative 0 2 (fun p => (H p)⁻¹) q) := by
  let H : PolarPoint → ℝ := fun p =>
    K.height z m (K.inverseChart z m (canonicalUnitPoint K m p))
  let v : PolarPoint → ℝ := fun p => (K.height z m (K.inverseChart z m p))⁻¹
  have hqK := n04PrincipalNegative_unitPoint_mem K m (hA.referenceBounds m).2.1 hq
  have hv := n04PrincipalNegative_reciprocal_pulledHeight_smooth hA hz hs m
  have hdiv := n04PrincipalNegative_divergence_formula hB hz hs m hm hv hqK
  have hpot := n04Realization_canonicalPotential_eq_reciprocalHeight_divergence
    hA hB hz hs m hqK
  have hlen : K.right m - K.left m ≠ 0 :=
    (sub_pos.mpr (hA.referenceBounds m).2.1).ne'
  have he2 : mixedDerivative 2 0 (fun p => (H p)⁻¹) q =
      (K.right m - K.left m) ^ 2 * mixedDerivative 2 0 v (canonicalUnitPoint K m q) :=
    n07a_mixedDerivative_radialAffine v (K.left m) (K.right m - K.left m) 2 0 q
  have he0 : mixedDerivative 0 2 (fun p => (H p)⁻¹) q =
      mixedDerivative 0 2 v (canonicalUnitPoint K m q) := by
    have hh := n07a_mixedDerivative_radialAffine v
      (K.left m) (K.right m - K.left m) 0 2 q
    rw [pow_zero, one_mul] at hh
    exact hh
  have hrad : mixedDerivative 2 0 v (canonicalUnitPoint K m q) =
      (K.right m - K.left m)⁻¹ ^ 2 * mixedDerivative 2 0 (fun p => (H p)⁻¹) q := by
    rw [he2, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hlen, one_pow, one_mul]
  change K.potential z m (canonicalUnitPoint K m q) = _
  rw [hpot, hm]
  simp only [Bool.false_eq_true, ite_false, neg_mul, one_mul]
  rw [hdiv]
  change -(H q * (mixedDerivative 2 0 v (canonicalUnitPoint K m q) -
    (canonicalUnitPoint K m q).1 * mixedDerivative 0 2 v (canonicalUnitPoint K m q))) = _
  rw [hrad, ← he0]

/-- The reference inverse-height atom already bounds the reciprocal
pulled height, at the same stored material sample.  The inverse point is
in the reference physical piece, so no comparison between cells is used.
This bound is valid for both kinds of pieces. -/
theorem n04PrincipalNegative_reference_pulledHeight_inverse_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    (href : ReferenceJets D T S C L K)
    (hzref : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState) :
    ∃ B : ℝ, 0 < B ∧ ∀ m q, q ∈ unitStrip →
      |(K.height (C.referenceState, 0) m
        (K.inverseChart (C.referenceState, 0) m (canonicalUnitPoint K m q)))⁻¹| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B := by
  have hbound := href.2 0
  refine ⟨hbound.choose, hbound.choose_spec.1, ?_⟩
  intro m q hq
  let x : PolarPoint := K.inverseChart (C.referenceState, 0) m (canonicalUnitPoint K m q)
  have hx : x ∈ referencePhysicalPieceOpen S K m := by
    rw [← hA.referenceDomain m]
    exact (hA.charts (C.referenceState, 0) hzref hsref m).2.1
      (n04PrincipalNegative_unitPoint_mem K m (hA.referenceBounds m).2.1 hq)
  have hlen : 0 < K.physicalRight m - K.physicalLeft m :=
    sub_pos.mpr (hA.referenceBounds m).1
  let p : PolarPoint :=
    ((x.1 - K.physicalLeft m) / (K.physicalRight m - K.physicalLeft m), x.2)
  have hp : p ∈ unitStrip := by
    refine ⟨⟨div_pos (sub_pos.mpr hx.1.1) hlen, ?_⟩, mem_univ _⟩
    exact (div_lt_one hlen).mpr (sub_lt_sub_right hx.1.2 _)
  have hpoint : physicalUnitPoint K m p = x := by
    apply Prod.ext
    · change K.physicalLeft m + (K.physicalRight m - K.physicalLeft m) *
        ((x.1 - K.physicalLeft m) / (K.physicalRight m - K.physicalLeft m)) = x.1
      field_simp [hlen.ne']
      ring
    · rfl
  have hv := hbound.choose_spec.2 m .heightInverse p hp 0 0 le_rfl
  rw [spaces_mixedDerivative_zero] at hv
  change |(K.height (C.referenceState, 0) m (physicalUnitPoint K m p))⁻¹| ≤ _ at hv
  rw [hpoint] at hv
  exact hv

end ContinuousFlexibility.Analysis
