import ContinuousFlexibility.Analysis.N07aCanonicalRadialOperator

/-!
# The actual radial weak mode equation

Fubini is applied only after compact-test integrability is established.
The resulting radial functions are the real cosine coefficients of the
given canonical L² representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S} {m : ℕ}

theorem n07a_reference_canonical_mode_equation
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (hP : CanonicalGeometry.ReferencePrincipal T S C K)
    (hm : K.left m < K.right m) {u G : CanonicalL2 S K m}
    (heq : N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G)
    (n : ℕ) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (K.left m) (K.right m) →
      (∫ r, n07aHalfRadialCoefficient u n r *
        deriv (fun t => (K.coefficients (C.referenceState, 0) m).a (t, 0) * deriv φ t) r) =
      ∫ r, ((2 * (n : ℝ)) ^ 2 * (K.coefficients (C.referenceState, 0) m).c (r, 0) *
        n07aHalfRadialCoefficient u n r + n07aHalfRadialCoefficient G n r) * φ r := by
  intro φ hφ hc hs
  let a := fun r => (K.coefficients (C.referenceState, 0) m).a (r, 0)
  let c := fun r => (K.coefficients (C.referenceState, 0) m).c (r, 0)
  let j : ℝ := 2 * (n : ℝ)
  let flux := fun r => deriv (fun t => a t * deriv φ t) r
  let testOp := fun r => flux r - j ^ 2 * c r * φ r
  let W := fun p : PolarPoint => φ p.1 * referenceAngularBasis n p.2
  let A := K.coefficients (C.referenceState, 0) m
  have hW : CanonicalTest S K m W := n07a_canonical_basis_test hφ hc hs n
  let ca := n07aReferenceOpenCoefficient hJ m hm 0
  let cb := n07aReferenceOpenCoefficient hJ m hm 1
  let cc := n07aReferenceOpenCoefficient hJ m hm 2
  have hdiv := n07a_canonicalTest_divergence A ca.smooth cb.smooth cc.smooth
    ca.periodic cb.periodic cc.periodic hW
  have hiD : Integrable (fun p => u p * divergenceOperator A W p) (canonicalMeasure S K m) :=
    (Lp.memLp u).integrable_mul (n07a_canonicalTest_memLp hdiv)
  have hD : (fun p => u p * divergenceOperator A W p) =ᵐ[canonicalMeasure S K m]
      fun p => u p * (testOp p.1 * referenceAngularBasis n p.2) := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    exact congrArg (u p * ·) (n07a_reference_divergence_basis hJ hP hm hφ n hp)
  have hiT := hiD.congr hD
  have hiC : Integrable (fun p => u p * ((c p.1 * φ p.1) * referenceAngularBasis n p.2))
      (canonicalMeasure S K m) := by
    have hi : Integrable (fun p => u p * (cc.value p * W p)) (canonicalMeasure S K m) :=
      (Lp.memLp u).integrable_mul
        (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hW cc.smooth cc.periodic))
    apply hi.congr
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    change u p * (A.c p * (φ p.1 * referenceAngularBasis n p.2)) = _
    rw [(hP.1 m p hp).2.2.2.1]
    ring
  have hiFlux : Integrable (fun p => u p * (flux p.1 * referenceAngularBasis n p.2))
      (canonicalMeasure S K m) := by
    apply (hiT.add (hiC.const_mul (j ^ 2))).congr
    exact Eventually.of_forall fun p => by
      simp only [Pi.add_apply]
      dsimp only [testOp]
      ring
  have hiRflux := n07a_canonical_basis_radial_integrable u n flux hiFlux
  have hiRc := n07a_canonical_basis_radial_integrable u n (fun r => c r * φ r) hiC
  have hiG : Integrable (fun p => G p * W p) (canonicalMeasure S K m) :=
    (Lp.memLp G).integrable_mul (n07a_canonicalTest_memLp hW)
  have hiRg := n07a_canonical_basis_radial_integrable G n φ hiG
  have h := heq W hW
  rw [integral_congr_ae hD, n07a_canonical_basis_pairing_integrable u n testOp hiT,
    n07a_canonical_basis_pairing G n hφ hc hs] at h
  have hscalar := mul_left_cancel₀ Real.pi_ne_zero h
  have hsplit : (fun r => n07aHalfRadialCoefficient u n r * testOp r) =
      fun r => n07aHalfRadialCoefficient u n r * flux r -
        j ^ 2 * (n07aHalfRadialCoefficient u n r * (c r * φ r)) := by
    funext r
    dsimp only [testOp]
    ring
  rw [hsplit, integral_sub hiRflux (hiRc.const_mul (j ^ 2)), integral_const_mul] at hscalar
  have hfluxSupport : tsupport flux ⊆ Ioo (K.left m) (K.right m) :=
    tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hs))
  have hleft : (∫ r in Ioo (K.left m) (K.right m), n07aHalfRadialCoefficient u n r * flux r) =
      ∫ r, n07aHalfRadialCoefficient u n r * flux r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hr (hfluxSupport hh)), mul_zero]
  have hright : (∫ r in Ioo (K.left m) (K.right m),
      (j ^ 2 * c r * n07aHalfRadialCoefficient u n r + n07aHalfRadialCoefficient G n r) * φ r) =
      ∫ r, (j ^ 2 * c r * n07aHalfRadialCoefficient u n r + n07aHalfRadialCoefficient G n r) * φ r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hr (hs hh)), mul_zero]
  change (∫ r, n07aHalfRadialCoefficient u n r * flux r) =
    ∫ r, (j ^ 2 * c r * n07aHalfRadialCoefficient u n r + n07aHalfRadialCoefficient G n r) * φ r
  rw [← hleft, ← hright]
  have he : (fun r => (j ^ 2 * c r * n07aHalfRadialCoefficient u n r +
      n07aHalfRadialCoefficient G n r) * φ r) =
      fun r => j ^ 2 * (n07aHalfRadialCoefficient u n r * (c r * φ r)) +
        n07aHalfRadialCoefficient G n r * φ r := by funext r; ring
  rw [he, integral_add (hiRc.const_mul (j ^ 2)) hiRg, integral_const_mul]
  linarith only [hscalar]

end ContinuousFlexibility.Analysis
