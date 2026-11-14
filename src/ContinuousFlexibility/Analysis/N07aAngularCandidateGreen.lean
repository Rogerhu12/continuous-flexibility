module

public import ContinuousFlexibility.Analysis.N07aAngularClassicalEquation
public import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals
public import ContinuousFlexibility.Analysis.N07aAngularNuRegularity
public import ContinuousFlexibility.Analysis.N07aLeadingRegularity
public import ContinuousFlexibility.Analysis.N07aPeriodicRadialPairing
public import ContinuousFlexibility.Analysis.N07aPhysicalTestSupport

/-!
# A genuine smooth physical candidate satisfies the required compact pairings

The same corrected coefficients are smooth and periodic on the open
annulus by the actual N01/N03 construction. Interior Green pairing applies
to every pulled canonical test. The full physical mean is converted only
after the compact products have been proved integrable.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_physical_pi_pairing_eq_canonical
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : Integrable f (canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0))
    (hp : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      Real.pi⁻¹ * ∫ p, f p ∂canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0 := by
  have hfi : Integrable f ((volume.restrict (Ioo D.a D.b)).prod angleMeasure) := by
    simpa only [n07aCanonicalMeasure_eq_prod, n07aRadialIntervalData] using hf
  have hperiod : ∀ᵐ r ∂volume.restrict (Ioo D.a D.b),
      Function.Periodic (fun θ => f (r, θ)) Real.pi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hp (r, θ) ⟨hr, mem_univ _⟩
  simpa only [n07aCanonicalMeasure_eq_prod, n07aRadialIntervalData] using
    n07a_periodic_radial_mean_eq_half hab hfi hperiod

theorem n07a_physical_smooth_homogeneous_pairing
    (hab : D.a ≤ D.b) (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ A.b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ A.c (annularOpen D))
    (hap : ∀ p ∈ annularOpen D, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ annularOpen D, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ annularOpen D, A.c (p + (0, Real.pi)) = A.c p)
    {η ν φ : PolarPoint → ℝ} {μ : ℝ}
    (hη : ContDiffOn ℝ ∞ η (annularOpen D))
    (hηπ : Function.Periodic η (0, Real.pi))
    (hν : ContDiffOn ℝ ∞ ν (annularOpen D))
    (hνπ : Function.Periodic ν (0, Real.pi))
    (hφ : CanonicalTest S (n07aRadialIntervalData K D.a D.b) 0 φ)
    (heq : ∀ p ∈ annularOpen D, divergenceOperator A η p + μ * ν p = 0) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      η (r, θ) * divergenceOperator A φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => ν (r, θ) * φ (r, θ))) = 0 := by
  let J := n07aRadialIntervalData K D.a D.b
  have hφdiv : CanonicalTest S J 0 (divergenceOperator A φ) :=
    n07a_canonicalTest_divergence (S := S) (K := J) (m := 0)
      A ha hb hc hap hbp hcp hφ
  have hiη : Integrable (fun p => η p * divergenceOperator A φ p)
      (canonicalMeasure S J 0) :=
    n07a_canonicalOpen_integrable_mul_test hη (fun p _ => hηπ p) hφdiv
  have hiν : Integrable (fun p => ν p * φ p) (canonicalMeasure S J 0) :=
    n07a_canonicalOpen_integrable_mul_test hν (fun p _ => hνπ p) hφ
  have hmeanη := n07a_physical_pi_pairing_eq_canonical hab hiη
    (fun p _ => congrArg₂ (· * ·) (hηπ p) (hφdiv.2.1 p))
  have hmeanν := n07a_physical_pi_pairing_eq_canonical hab hiν
    (fun p _ => congrArg₂ (· * ·) (hνπ p) (hφ.2.1 p))
  have hgreen := n07a_canonicalOpen_green (S := S) (K := J) (m := 0)
    A ha hb hc hap hbp hcp hη (fun p _ => hηπ p) hφ
  have hae : (fun p => divergenceOperator A η p * φ p) =ᵐ[canonicalMeasure S J 0]
      fun p => -(μ * (ν p * φ p)) := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := J) (m := 0)] with p hp
    have h := heq p hp
    have hmul := congrArg (· * φ p) h
    nlinarith only [hmul]
  have hint : (∫ p, divergenceOperator A η p * φ p ∂canonicalMeasure S J 0) =
      -(μ * ∫ p, ν p * φ p ∂canonicalMeasure S J 0) := by
    rw [integral_congr_ae hae, integral_neg, integral_const_mul]
  rw [hmeanη, hmeanν, hgreen, hint]
  ring

theorem n07a_candidate_homogeneous_pulledTest_pairing
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {η : PolarPoint → ℝ} {μ : ℝ}
    (hη : ContDiffOn ℝ ∞ η (annularOpen D))
    (hηπ : Function.Periodic η (0, Real.pi))
    (heq : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients z) η p + μ * nuColumnField D S C z p = 0)
    {m : ℕ} {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
      divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W) (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * n07aPhysicalTestPullback S K z m W (r, θ))) = 0 := by
  have hspace := h03.2.2.2.2.2.2.2.2 z hz hs
  have ha := n07a_correctedLeadingCoefficient_contDiffOn hS hT h01 h03 hz hs
  have hap : ∀ p ∈ annularOpen D,
      (L.coefficients z).a (p + (0, Real.pi)) = (L.coefficients z).a p := by
    intro p _
    rw [h03.1 z hz hs, h03.1 z hz hs]
    exact (n07a_originalCoefficients_periodic hS z).1 p
  obtain ⟨hφ, hφπ, _⟩ := n07aPhysicalTestPullback_test h04 hz hs hW
  have hφcan : CanonicalTest S (n07aRadialIntervalData K D.a D.b) 0
      (n07aPhysicalTestPullback S K z m W) := ⟨hφ.1, hφπ, hφ.2.2⟩
  exact n07a_physical_smooth_homogeneous_pairing hab (L.coefficients z)
    ha hspace.1 hspace.2.1 hap (fun p hp => (hspace.2.2 p hp).1)
    (fun p hp => (hspace.2.2 p hp).2) hη hηπ
    (n07a_nuColumnField_contDiffOn hS hT h01 hz hs)
    (n07a_nuColumnField_periodic hS z) hφcan heq

end ContinuousFlexibility.Analysis
