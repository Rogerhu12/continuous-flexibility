import ContinuousFlexibility.Analysis.N06PrimitivePositiveModeEnergy
import ContinuousFlexibility.Analysis.N06PrincipalJetAlgebra
import ContinuousFlexibility.Analysis.N06PositiveCanonicalSymmetry
import ContinuousFlexibility.Analysis.N06NegativeForcingParity
import ContinuousFlexibility.Analysis.N07aCanonicalRadialReflection
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Reflection of the actual principal perturbation

The signs of the actual current and reference coefficients follow from
N03 and the genuine N04 density.  Reflection is transferred through the
compact weak equation, so no pointwise regularity of an inverse height
or a chosen weak derivative is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n06_openDivergence_reflectionOn
    (a beta c : N07aCanonicalOpenCoefficient S K m)
    (ha : ∀ p ∈ canonicalOpen S K m, a.value (p.1, Real.pi - p.2) = a.value p)
    (hb : ∀ p ∈ canonicalOpen S K m, beta.value (p.1, Real.pi - p.2) = -beta.value p)
    (hc : ∀ p ∈ canonicalOpen S K m, c.value (p.1, Real.pi - p.2) = c.value p)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    EqOn (divergenceOperator ⟨a.value, beta.value, c.value⟩
        (fun p => φ (p.1, Real.pi - p.2)))
      (fun p => divergenceOperator ⟨a.value, beta.value, c.value⟩ φ
        (p.1, Real.pi - p.2)) (canonicalOpen S K m) := by
  let ψ : PolarPoint → ℝ := fun p => φ (p.1, Real.pi - p.2)
  have hψ : CanonicalTest S K m ψ := n07a_canonicalTest_reflected hφ
  let fr : PolarPoint → ℝ := fun q =>
    a.value q * mixedDerivative 1 0 φ q + beta.value q * mixedDerivative 0 1 φ q
  let ft : PolarPoint → ℝ := fun q =>
    beta.value q * mixedDerivative 1 0 φ q + c.value q * mixedDerivative 0 1 φ q
  intro p hp
  have hpR : (p.1, Real.pi - p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hfr : (fun q => a.value q * mixedDerivative 1 0 ψ q +
      beta.value q * mixedDerivative 0 1 ψ q) =ᶠ[𝓝 p]
        fun q => fr (q.1, Real.pi - q.2) := by
    filter_upwards [hn] with q hq
    simp only [ψ, fr, spaces_mixedDerivative_reflection, pow_zero, pow_one,
      one_mul, neg_one_mul, ha q hq, hb q hq]
    ring
  have hft : (fun q => beta.value q * mixedDerivative 1 0 ψ q +
      c.value q * mixedDerivative 0 1 ψ q) =ᶠ[𝓝 p]
        fun q => (-1 : ℝ) * ft (q.1, Real.pi - q.2) := by
    filter_upwards [hn] with q hq
    simp only [ψ, ft, spaces_mixedDerivative_reflection, pow_zero, pow_one,
      one_mul, neg_one_mul, hb q hq, hc q hq]
    ring
  change divergenceOperator ⟨a.value, beta.value, c.value⟩ ψ p =
    divergenceOperator ⟨a.value, beta.value, c.value⟩ φ (p.1, Real.pi - p.2)
  rw [n07a_open_divergence_mixed ⟨a.value, beta.value, c.value⟩
    a.smooth beta.smooth c.smooth hψ.1.contDiffOn hp,
    n07a_open_divergence_mixed ⟨a.value, beta.value, c.value⟩
    a.smooth beta.smooth c.smooth hφ.1.contDiffOn hpR]
  change mixedDerivative 1 0 _ p + mixedDerivative 0 1 _ p =
    mixedDerivative 1 0 fr (p.1, Real.pi - p.2) +
      mixedDerivative 0 1 ft (p.1, Real.pi - p.2)
  rw [n07a_mixedDerivative_eventuallyEq hfr 1 0,
    n07a_mixedDerivative_eventuallyEq hft 0 1,
    spaces_mixedDerivative_const_mul]
  simp only [spaces_mixedDerivative_reflection, pow_zero, pow_one,
    one_mul, neg_one_mul, neg_neg]

theorem n06_openDistribution_reflection
    (a beta c : N07aCanonicalOpenCoefficient S K m)
    (ha : ∀ p ∈ canonicalOpen S K m, a.value (p.1, Real.pi - p.2) = a.value p)
    (hb : ∀ p ∈ canonicalOpen S K m, beta.value (p.1, Real.pi - p.2) = -beta.value p)
    (hc : ∀ p ∈ canonicalOpen S K m, c.value (p.1, Real.pi - p.2) = c.value p)
    {u g : CanonicalL2 S K m} (hu : n07aAngularReflection m u = u)
    (heq : N07aCanonicalDistributionEquation S K m
      ⟨a.value, beta.value, c.value⟩ u g) :
    n07aAngularReflection m g = g := by
  apply n06_canonicalL2_test_ext
  intro φ hφ
  have hdiv : MemLp (divergenceOperator ⟨a.value, beta.value, c.value⟩ φ) 2
      (canonicalMeasure S K m) :=
    n07a_canonicalTest_memLp (n07a_canonicalTest_divergence
      ⟨a.value, beta.value, c.value⟩ a.smooth beta.smooth c.smooth
      a.periodic beta.periodic c.periodic hφ)
  calc
    (∫ p, n07aAngularReflection m g p * φ p ∂canonicalMeasure S K m) =
        ∫ p, g p * φ (p.1, Real.pi - p.2) ∂canonicalMeasure S K m :=
      n07aCanonicalReflection_pairing g φ (n07a_canonicalTest_memLp hφ)
    _ = ∫ p, u p * divergenceOperator ⟨a.value, beta.value, c.value⟩
        (fun q => φ (q.1, Real.pi - q.2)) p ∂canonicalMeasure S K m :=
      (heq _ (n07a_canonicalTest_reflected hφ)).symm
    _ = ∫ p, u p * divergenceOperator ⟨a.value, beta.value, c.value⟩ φ
        (p.1, Real.pi - p.2) ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
      rw [n06_openDivergence_reflectionOn a beta c ha hb hc hφ hp]
    _ = ∫ p, n07aAngularReflection m u p *
        divergenceOperator ⟨a.value, beta.value, c.value⟩ φ p
        ∂canonicalMeasure S K m :=
      (n07aCanonicalReflection_pairing u _ hdiv).symm
    _ = ∫ p, u p * divergenceOperator ⟨a.value, beta.value, c.value⟩ φ p
        ∂canonicalMeasure S K m := by rw [hu]
    _ = ∫ p, g p * φ p ∂canonicalMeasure S K m := heq φ hφ

variable {D : ReferenceData} {T : MaterialData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {V : VolumeModelData S K}
  {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

theorem n06_primitivePrincipal_difference_reflection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.positive m = true) (hlen : K.left m < K.right m)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    let a := (n07aCurrentOpenCoefficient href hcur z hz m hlen 0).sub
      (n07aReferenceOpenCoefficient href m hlen 0)
    let beta := (n07aCurrentOpenCoefficient href hcur z hz m hlen 1).sub
      (n07aReferenceOpenCoefficient href m hlen 1)
    let c := (n07aCurrentOpenCoefficient href hcur z hz m hlen 2).sub
      (n07aReferenceOpenCoefficient href m hlen 2)
    a.value (p.1, Real.pi - p.2) = a.value p ∧
      beta.value (p.1, Real.pi - p.2) = -beta.value p ∧
      c.value (p.1, Real.pi - p.2) = c.value p := by
  have hreg : ContDiffOn ℝ ∞ (K.coefficients (liftSectorParameter S C z) m).a
      (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (liftSectorParameter S C z) m).b
        (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (liftSectorParameter S C z) m).c
        (canonicalOpen S K m) :=
    ⟨(n07aCurrentOpenCoefficient href hcur z hz m hlen 0).smooth,
      (n07aCurrentOpenCoefficient href hcur z hz m hlen 1).smooth,
      (n07aCurrentOpenCoefficient href hcur z hz m hlen 2).smooth⟩
  have hreg₀ : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).a
      (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).b
        (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).c
        (canonicalOpen S K m) :=
    ⟨(n07aReferenceOpenCoefficient href m hlen 0).smooth,
      (n07aReferenceOpenCoefficient href m hlen 1).smooth,
      (n07aReferenceOpenCoefficient href m hlen 2).smooth⟩
  have hz' := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl
  have hs' := h01.2.2.1.liftSectorParameter_sector z
  have hs := n06_positive_canonical_coefficients_reflectionOn
    hT hS h01 h03 h04 hz' hs' m hm hreg hp
  have hs₀ := n06_positive_canonical_coefficients_reflectionOn
    hT hS h01 h03 h04 (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m hm hreg₀ hp
  change (K.coefficients (liftSectorParameter S C z) m).a (p.1, Real.pi - p.2) -
      (K.coefficients (C.referenceState, 0) m).a (p.1, Real.pi - p.2) = _ ∧
    (K.coefficients (liftSectorParameter S C z) m).b (p.1, Real.pi - p.2) -
      (K.coefficients (C.referenceState, 0) m).b (p.1, Real.pi - p.2) = _ ∧
    (K.coefficients (liftSectorParameter S C z) m).c (p.1, Real.pi - p.2) -
      (K.coefficients (C.referenceState, 0) m).c (p.1, Real.pi - p.2) = _
  rw [hs.1, hs.2.1, hs.2.2, hs₀.1, hs₀.2.1, hs₀.2.2]
  exact ⟨rfl, by ring, rfl⟩

theorem n06_primitiveReferenceInverse_reflection
    (h05 : N05Properties D T S C K V b B)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    n07aAngularReflection m (n07aReferenceInverseField (B := B) F m) =
      n07aReferenceInverseField (B := B) F m := by
  apply Lp.ext
  exact (n07aAngularReflection_ae m _).trans
    (n06N05_height_reflection h05 (B.inverse F) m)

theorem n06_primitivePrincipalJet_reflection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ)
    (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (J : N06PrimitivePositiveJets (n07aReferenceInverseField (B := B) F m)) :
    n07aAngularReflection m (n07aRelativePrincipalJet href hcur z hz m hlen
      J.radial J.angular J.secondRadial J.radialAngular J.angularAngular) =
        n07aRelativePrincipalJet href hcur z hz m hlen
          J.radial J.angular J.secondRadial J.radialAngular J.angularAngular := by
  apply n06_openDistribution_reflection
    ((n07aCurrentOpenCoefficient href hcur z hz m hlen 0).sub
      (n07aReferenceOpenCoefficient href m hlen 0))
    ((n07aCurrentOpenCoefficient href hcur z hz m hlen 1).sub
      (n07aReferenceOpenCoefficient href m hlen 1))
    ((n07aCurrentOpenCoefficient href hcur z hz m hlen 2).sub
      (n07aReferenceOpenCoefficient href m hlen 2))
    (fun p hp => (n06_primitivePrincipal_difference_reflection
      hT hS h01 h03 h04 href hcur z hz m hm hlen hp).1)
    (fun p hp => (n06_primitivePrincipal_difference_reflection
      hT hS h01 h03 h04 href hcur z hz m hm hlen hp).2.1)
    (fun p hp => (n06_primitivePrincipal_difference_reflection
      hT hS h01 h03 h04 href hcur z hz m hm hlen hp).2.2)
    (n06_primitiveReferenceInverse_reflection h05 F m)
  exact n07aOpenDivergence_distribution _ _ _ J.radial_weak J.angular_weak
    J.secondRadial_weak J.radialAngular_weak J.angularAngular_weak

end ContinuousFlexibility.Analysis
