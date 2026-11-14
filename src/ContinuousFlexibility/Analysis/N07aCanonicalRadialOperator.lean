module

public import ContinuousFlexibility.Analysis.N07aCanonicalTestDivergence
public import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients
public import ContinuousFlexibility.Analysis.N07aCanonicalRadialCoefficients
public import ContinuousFlexibility.Analysis.N07aCanonicalDifference
public import ContinuousFlexibility.Radial.ReferenceCosineJacobi

/-!
# The genuine reference divergence on separated cosine tests

Only the angular variable is expanded. Radial coefficients remain actual
functions on the open interval, and no periodic radial extension is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonical_basis_row_integral
    (u : PolarPoint → ℝ) (n : ℕ) (φ : ℝ → ℝ) (r : ℝ) :
    (∫ θ, u (r, θ) * (φ r * referenceAngularBasis n θ) ∂angleMeasure) =
      Real.pi * (n07aHalfRadialCoefficient u n r * φ r) := by
  have he : (fun θ => u (r, θ) * (φ r * referenceAngularBasis n θ)) =
      fun θ => (u (r, θ) * referenceAngularBasis n θ) * φ r := by funext θ; ring
  rw [he, integral_mul_const]
  unfold n07aHalfRadialCoefficient angleMeasure
  field_simp [Real.pi_ne_zero]

theorem n07a_canonical_basis_radial_integrable
    (u : CanonicalL2 S K m) (n : ℕ) (φ : ℝ → ℝ)
    (hi : Integrable (fun p => u p * (φ p.1 * referenceAngularBasis n p.2))
      (canonicalMeasure S K m)) :
    Integrable (fun r => n07aHalfRadialCoefficient u n r * φ r)
      (volume.restrict (Ioo (K.left m) (K.right m))) := by
  let f : PolarPoint → ℝ := u
  change Integrable (fun p => f p * (φ p.1 * referenceAngularBasis n p.2))
    (canonicalMeasure S K m) at hi
  change Integrable (fun r => n07aHalfRadialCoefficient f n r * φ r) _
  rw [n07aCanonicalMeasure_eq_prod] at hi
  have h := hi.integral_prod_left.const_mul Real.pi⁻¹
  apply h.congr
  exact Eventually.of_forall fun r => by
    dsimp only
    rw [n07a_canonical_basis_row_integral]
    field_simp [Real.pi_ne_zero]

theorem n07a_canonical_basis_pairing_integrable
    (u : CanonicalL2 S K m) (n : ℕ) (φ : ℝ → ℝ)
    (hi : Integrable (fun p => u p * (φ p.1 * referenceAngularBasis n p.2))
      (canonicalMeasure S K m)) :
    (∫ p, u p * (φ p.1 * referenceAngularBasis n p.2) ∂canonicalMeasure S K m) =
      Real.pi * ∫ r in Ioo (K.left m) (K.right m), n07aHalfRadialCoefficient u n r * φ r := by
  let f : PolarPoint → ℝ := u
  change Integrable (fun p => f p * (φ p.1 * referenceAngularBasis n p.2))
    (canonicalMeasure S K m) at hi
  change (∫ p, f p * (φ p.1 * referenceAngularBasis n p.2) ∂canonicalMeasure S K m) =
    Real.pi * ∫ r in Ioo (K.left m) (K.right m), n07aHalfRadialCoefficient f n r * φ r
  rw [n07aCanonicalMeasure_eq_prod] at hi ⊢
  rw [integral_prod _ hi, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    dsimp only
    have he : (fun θ => f (r, θ) * (φ r * referenceAngularBasis n θ)) =
        fun θ => (f (r, θ) * referenceAngularBasis n θ) * φ r := by funext θ; ring
    rw [he, integral_mul_const]
    unfold n07aHalfRadialCoefficient
    change _ = Real.pi * ((Real.pi⁻¹ *
      ∫ θ in Ioc (0 : ℝ) Real.pi, f (r, θ) * referenceAngularBasis n θ) * φ r)
    unfold angleMeasure
    field_simp [Real.pi_ne_zero]

theorem n07a_radial_divergence_basis (a c : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Ioo (K.left m) (K.right m)))
    (hc : ContDiffOn ℝ ∞ c (Ioo (K.left m) (K.right m)))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    divergenceOperator ⟨(fun q => a q.1), (fun _ => 0), (fun q => c q.1)⟩
      (fun q => φ q.1 * referenceAngularBasis n q.2) p =
      (deriv (fun r => a r * deriv φ r) p.1 -
        (2 * (n : ℝ)) ^ 2 * c p.1 * φ p.1) * referenceAngularBasis n p.2 := by
  have hW : ContDiff ℝ ∞ (fun q : PolarPoint => φ q.1 * referenceAngularBasis n q.2) :=
    (hφ.comp contDiff_fst).mul ((contDiff_referenceAngularBasis n).comp contDiff_snd)
  have hr : radialPartial (fun q => φ q.1 * referenceAngularBasis n q.2) =
      fun q => deriv φ q.1 * referenceAngularBasis n q.2 := by
    rw [n07a_radialPartial_eq_mixed hW]
    exact funext (n07a_canonical_basis_radial hφ n)
  have ht : angularPartial (fun q => φ q.1 * referenceAngularBasis n q.2) =
      fun q => φ q.1 * deriv (referenceAngularBasis n) q.2 := by
    rw [n07a_angularPartial_eq_mixed hW]
    funext q
    simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one, deriv_const_mul_field]
  have ha' := (ha.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).differentiableAt (by simp)
  have hc' := (hc.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).differentiableAt (by simp)
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hn' := (contDiff_infty_iff_deriv.mp (contDiff_referenceAngularBasis n)).2
  have hfr : DifferentiableAt ℝ
      (fun q : PolarPoint => (a q.1 * deriv φ q.1) * referenceAngularBasis n q.2) p :=
    ((ha'.comp p differentiableAt_fst).mul ((hφ'.comp contDiff_fst).differentiable (by simp) p)).mul
      (((contDiff_referenceAngularBasis n).comp contDiff_snd).differentiable (by simp) p)
  have hft : DifferentiableAt ℝ
      (fun q : PolarPoint => (c q.1 * φ q.1) * deriv (referenceAngularBasis n) q.2) p :=
    ((hc'.comp p differentiableAt_fst).mul ((hφ.comp contDiff_fst).differentiable (by simp) p)).mul
      ((hn'.comp contDiff_snd).differentiable (by simp) p)
  simp only [divergenceOperator, hr, ht, zero_mul, add_zero, zero_add]
  simp_rw [← mul_assoc]
  rw [← (hasDerivAt_radialSlice hfr).deriv, ← (hasDerivAt_angularSlice hft).deriv]
  simp only [deriv_mul_const_field, deriv_const_mul_field, deriv_deriv_referenceAngularBasis,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

variable {D : ReferenceData} {T : MaterialData} {C : NonlinearGeometryData S}
  {L : ReturnCorrectionData S}

theorem n07a_reference_divergence_basis
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (hP : CanonicalGeometry.ReferencePrincipal T S C K)
    (hm : K.left m < K.right m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) :
    EqOn (divergenceOperator (K.coefficients (C.referenceState, 0) m)
      (fun q => φ q.1 * referenceAngularBasis n q.2))
      (fun p => (deriv (fun r => (K.coefficients (C.referenceState, 0) m).a (r, 0) * deriv φ r) p.1 -
        (2 * (n : ℝ)) ^ 2 * (K.coefficients (C.referenceState, 0) m).c (p.1, 0) * φ p.1) *
          referenceAngularBasis n p.2) (canonicalOpen S K m) := by
  let a := fun r => (K.coefficients (C.referenceState, 0) m).a (r, 0)
  let c := fun r => (K.coefficients (C.referenceState, 0) m).c (r, 0)
  have hmap : MapsTo (fun r : ℝ => (r, (0 : ℝ)))
      (Ioo (K.left m) (K.right m)) (canonicalOpen S K m) := fun _ hr => ⟨hr, mem_univ _⟩
  have ha : ContDiffOn ℝ ∞ a (Ioo (K.left m) (K.right m)) :=
    (n07aReferenceOpenCoefficient hJ m hm 0).smooth.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn hmap
  have hc : ContDiffOn ℝ ∞ c (Ioo (K.left m) (K.right m)) :=
    (n07aReferenceOpenCoefficient hJ m hm 2).smooth.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn hmap
  intro p hp
  have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have he : divergenceOperator (K.coefficients (C.referenceState, 0) m)
      (fun q => φ q.1 * referenceAngularBasis n q.2) p =
      divergenceOperator ⟨(fun q => a q.1), (fun _ => 0), (fun q => c q.1)⟩
        (fun q => φ q.1 * referenceAngularBasis n q.2) p := by
    apply n07a_divergenceOperator_eq_of_germs
    · filter_upwards [hnear] with q hq
      exact (hP.1 m q hq).2.2.1
    · filter_upwards [hnear] with q hq
      exact (hP.1 m q hq).2.1
    · filter_upwards [hnear] with q hq
      exact (hP.1 m q hq).2.2.2.1
  exact he.trans (n07a_radial_divergence_basis a c ha hc hφ n hp)

end ContinuousFlexibility.Analysis
