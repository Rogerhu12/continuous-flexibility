import ContinuousFlexibility.Analysis.N06LeftColumnHalfPairing
import ContinuousFlexibility.Analysis.N06EvenHalfTests
import ContinuousFlexibility.Analysis.N06CurrentTestAveraging
import ContinuousFlexibility.Analysis.N06CurrentOperatorLinearity
import ContinuousFlexibility.Analysis.N06PhysicalHeightAffinePairing

/-!
# The genuine left-column pairing for every original physical test

Two actual integrable angular halves first give the source mean of the
half-period average. N04's source identity commutes this average with the
actual operator on the a.e. physical cover. Reflection averaging then
uses the recovered piecewise operator linearity, N03's exact parity, and
integrability proved from the original canonical L2 transforms. The
compact even test pairing therefore proves the full original identity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

private theorem n06_sourceMean_congr_radial_ae
    {D : ReferenceData} (hab : D.a ≤ D.b) {f g : PolarPoint → ℝ}
    (h : ∀ᵐ r ∂volume.restrict (radialCore D),
      angularMean (fun θ => f (r, θ)) = angularMean (fun θ => g (r, θ))) :
    physicalSourceIntegral D f = physicalSourceIntegral D g := by
  have hrad : (volume : Measure ℝ).restrict (radialCore D) =
      volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  unfold physicalSourceIntegral
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  rw [hrad] at h
  exact integral_congr_ae h

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The literal left-cutoff pairing with the actual operator is
integrable on either angular half. The original graph geometry supplies
finiteness on the original compact test support. -/
theorem n06_chiLeft_operator_twoHalf_integrable
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    IntegrableOn (fun p : PolarPoint => S.chiLeft p.1 *
      divergenceOperator (L.coefficients z) φ p)
        (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    IntegrableOn (fun p : PolarPoint => S.chiLeft p.1 *
      divergenceOperator (L.coefficients z) φ (p + (0, Real.pi)))
        (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hφ.2.2
  have hfinite := n06_currentPieces_finite_on_compact h01.1.1 h01.2.2.2.1
    hcoords h04 hz hs hJ hJD
  have hLzero : ∀ r, r ∉ J → ∀ θ,
      divergenceOperator (L.coefficients z) φ (r, θ) = 0 :=
    fun r hr θ => n06_divergenceOperator_zero_off_radial_support
      (L.coefficients z) hJ.isClosed hzero hr θ
  refine ⟨n06_chiLeft_half_pairing_integrable hS h04 hz hs hfinite
    (fun m => n06_current_operatorTest_memLp hT hS h01 h03 h04 hz hs m hφ) hLzero, ?_⟩
  apply n06_chiLeft_half_pairing_integrable hS h04 hz hs hfinite
  · intro m
    simpa only [Nat.cast_one, one_mul] using
      n06_current_shifted_operatorTest_memLp hT hS h01 h03 h04 hz hs m 1 hφ
  · intro r hr θ
    simpa only [Prod.mk_add_mk, add_zero] using hLzero r hr (θ + Real.pi)

/-- Half-period averaging is applied to the actual full-period operator
pairing before any reflection symmetry of the test is imposed. -/
theorem n06_chiLeft_full_pairing_eq_half_average
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => S.chiLeft r *
      divergenceOperator (L.coefficients z) φ (r, θ))) =
      physicalSourceIntegral D (fun p => S.chiLeft p.1 *
        divergenceOperator (L.coefficients z) (n06_radialTestAverage φ) p) := by
  have hab := h01.1.1.choose_spec.1.2.1.le
  have hI := n06_chiLeft_operator_twoHalf_integrable hT hS h01 h03 h04 hcoords hz hs hφ
  have hperiod : Function.Periodic (fun p : PolarPoint => S.chiLeft p.1)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero]
  have havg := n06_fullPhysical_pairing_of_two_halves hab hperiod hI.1 hI.2
  have hmean : (∫ r in D.a..D.b, radialAngularMean (fun θ => S.chiLeft r *
      divergenceOperator (L.coefficients z) φ (r, θ))) =
      physicalSourceIntegral D (fun p => S.chiLeft p.1 *
        n06_radialTestAverage (divergenceOperator (L.coefficients z) φ) p) :=
    havg.2.trans (n06_angularMean_halfIntegral hab havg.1).symm
  refine hmean.trans (n06_sourceMean_congr_radial_ae hab ?_)
  filter_upwards [n06_current_divergence_average_radial_ae hT hS h01 h03 h04 hz hs hφ]
    with r hr
  apply n06_angularMean_congr_ae
  filter_upwards [hr] with θ hθ
  rw [hθ]

/-- The actual operator pairing of a half-period test is unchanged by
its even projection. The angular integrability follows from N04 and the
original finite atlas, and the operator identities hold on its a.e. cover. -/
theorem n06_chiLeft_half_pairing_evenPart
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : ∀ m, K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hπ : Function.Periodic φ (0, Real.pi)) :
    physicalSourceIntegral D (fun p => S.chiLeft p.1 *
      divergenceOperator (L.coefficients z) φ p) =
      physicalSourceIntegral D (fun p => S.chiLeft p.1 *
        divergenceOperator (L.coefficients z) (n06EvenPart φ) p) := by
  have hI := (n06_chiLeft_operator_twoHalf_integrable
    hT hS h01 h03 h04 hcoords hz hs hφ).1
  have hmeasure : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) =
      (volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    change ((volume : Measure ℝ).prod volume).restrict _ = _
    rw [← Measure.prod_restrict]
  rw [IntegrableOn, hmeasure] at hI
  have hreflect : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ᵐ θ ∂volume,
      divergenceOperator (L.coefficients z) (n06EvenPart φ) (r, θ) =
        (divergenceOperator (L.coefficients z) φ (r, θ) +
          divergenceOperator (L.coefficients z) φ (r, -θ)) / 2 :=
    n06_physicalPieces_radial_ae h04 hz hs (fun m _ hp =>
      n06_current_divergence_reflectionAverage_on_piece h03 h04 hz hs (hpositive m) hφ.1 hp)
  apply n06_sourceMean_congr_radial_ae h01.1.1.choose_spec.1.2.1.le
  filter_upwards [hI.prod_right_ae,
    n06_current_divergence_periodic_radial_ae hT hS h01 h03 h04 hz hs hφ hπ,
    hreflect] with r hint hperiod heven
  have hint' : IntervalIntegrable (fun θ => S.chiLeft r *
      divergenceOperator (L.coefficients z) φ (r, θ)) volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr hint
  have hperiod' : (fun θ => S.chiLeft r *
      divergenceOperator (L.coefficients z) φ (r, θ + Real.pi)) =ᵐ[volume]
        (fun θ => S.chiLeft r * divergenceOperator (L.coefficients z) φ (r, θ)) := by
    filter_upwards [hperiod] with θ hθ
    exact congrArg (fun t : ℝ => S.chiLeft r * t) hθ
  symm
  calc
    _ = angularMean (fun θ => (S.chiLeft r * divergenceOperator (L.coefficients z) φ (r, θ) +
        S.chiLeft r * divergenceOperator (L.coefficients z) φ (r, -θ)) / 2) := by
      apply n06_angularMean_congr_ae
      filter_upwards [heven] with θ hθ
      rw [hθ]
      ring
    _ = _ := n06_angularMean_reflectionAverage_ae hperiod' hint'

/-- The exact full-period physical left-column identity for every
original RadialTest. Positive canonical regularity is the qualitative
fact already derived on the retained Through05 neighborhood. -/
theorem n06_currentLeftColumn_full_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : ∀ m, K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => S.chiLeft r *
      divergenceOperator (L.coefficients z) φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06CurrentLeftColumn S L z (r, θ) * φ (r, θ)) := by
  let ψ := n06_radialTestAverage φ
  have hψ : RadialTest D ψ := n06_radialTestAverage_test hφ
  have hψπ : Function.Periodic ψ (0, Real.pi) := n06_radialTestAverage_periodic hφ.2.1
  have hcol := n06_currentLeftColumn_contDiff hT hS h01 h03 hz hs
  have hcolπ := n06_currentLeftColumn_periodic hS h03 hz hs
  have hcole := n06_currentLeftColumn_even hT hS h01 h03 hz hs
  have hRHS : (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06CurrentLeftColumn S L z (r, θ) * φ (r, θ))) =
      physicalSourceIntegral D (fun p => n06CurrentLeftColumn S L z p * ψ p) := by
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [physicalSourceIntegral]
    exact n06_radialAngularMean_pairing_of_continuous
      (u := fun θ => n06CurrentLeftColumn S L z (r, θ)) (φ := fun θ => φ (r, θ))
      (fun θ => by simpa only [Prod.mk_add_mk, add_zero] using hcolπ (r, θ))
      (hcol.continuous.comp (continuous_const.prodMk continuous_id))
      (hφ.1.continuous.comp (continuous_const.prodMk continuous_id))
  calc
    _ = physicalSourceIntegral D (fun p => S.chiLeft p.1 *
        divergenceOperator (L.coefficients z) ψ p) :=
      n06_chiLeft_full_pairing_eq_half_average hT hS h01 h03 h04 hcoords hz hs hφ
    _ = physicalSourceIntegral D (fun p => S.chiLeft p.1 *
        divergenceOperator (L.coefficients z) (n06EvenPart ψ) p) :=
      n06_chiLeft_half_pairing_evenPart hT hS h01 h03 h04 hcoords hz hs hpositive hψ hψπ
    _ = physicalSourceIntegral D (fun p => n06CurrentLeftColumn S L z p * n06EvenPart ψ p) :=
      n06_currentLeftColumn_half_pairing hT hS h01 h03 hz hs (n06EvenPart_contDiff hψ.1)
        (n06EvenPart_even ψ) (n06EvenPart_periodic hψπ) (n06EvenPart_support hψ.2.2)
    _ = physicalSourceIntegral D (fun p => n06CurrentLeftColumn S L z p * ψ p) :=
      n06_sourceIntegral_evenPart_pairing D hcol.continuous hψ.1.continuous
        hcolπ hψπ (fun r θ => hcole (r, θ))
    _ = _ := hRHS.symm

end ContinuousFlexibility.Statements
