import ContinuousFlexibility.Statements.ScalarWeighted
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual weak scalar graph on the physical annulus

The integration by parts formula below uses the physical measure `dr dθ`.
The angular boundary cancels by periodicity and compact radial tests vanish
at both radial endpoints. No endpoint condition is imposed on the height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

private theorem weightedGraph_continuous_radialPartial {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (radialPartial f) :=
  continuous_iff_continuousAt.mpr fun p =>
    (contDiffAt_radialPartial hf.contDiffAt (m := 0) (by simp)).continuousAt

private theorem weightedGraph_continuous_angularPartial {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (angularPartial f) :=
  continuous_iff_continuousAt.mpr fun p =>
    (contDiffAt_angularPartial hf.contDiffAt (m := 0) (by simp)).continuousAt

theorem scalarAnnularIntegral_add (D : ReferenceData) {f g : PolarPoint → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    scalarAnnularIntegral D (fun p => f p + g p) =
      scalarAnnularIntegral D f + scalarAnnularIntegral D g := by
  have hfi : Continuous (fun r => ∫ θ in (0 : ℝ)..Real.pi, f (r, θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => f (r, θ)) hf 0 Real.pi
  have hgi : Continuous (fun r => ∫ θ in (0 : ℝ)..Real.pi, g (r, θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => g (r, θ)) hg 0 Real.pi
  have he (r : ℝ) : (∫ θ in (0 : ℝ)..Real.pi, f (r, θ) + g (r, θ)) =
      (∫ θ in (0 : ℝ)..Real.pi, f (r, θ)) + (∫ θ in (0 : ℝ)..Real.pi, g (r, θ)) :=
    intervalIntegral.integral_add
      ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 Real.pi)
      ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 Real.pi)
  unfold scalarAnnularIntegral
  simp_rw [he]
  exact intervalIntegral.integral_add (hfi.intervalIntegrable D.a D.b)
    (hgi.intervalIntegrable D.a D.b)

theorem scalarAnnularIntegral_sub (D : ReferenceData) {f g : PolarPoint → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    scalarAnnularIntegral D (fun p => f p - g p) =
      scalarAnnularIntegral D f - scalarAnnularIntegral D g := by
  simpa only [sub_eq_add_neg, scalarAnnularIntegral, Pi.neg_apply,
    intervalIntegral.integral_neg] using
    scalarAnnularIntegral_add D hf hg.neg

theorem IsPhysicalScalarTest.zero_endpoints {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hφ : IsPhysicalScalarTest D φ) (θ : ℝ) : φ (D.a, θ) = 0 ∧ φ (D.b, θ) = 0 := by
  obtain ⟨K, _, hK, hz⟩ := hφ.2.2
  exact ⟨hz D.a (fun ha => (lt_irrefl D.a) (hK ha).1) θ,
    hz D.b (fun hb => (lt_irrefl D.b) (hK hb).2) θ⟩

/-- Physical integration by parts for smooth fluxes and a compact radial
periodic test. Only the angular flux needs the seam condition. -/
theorem scalarAnnularIntegral_divergence_mul_test
    (D : ReferenceData) {R Θ φ : PolarPoint → ℝ}
    (hR : ContDiff ℝ ∞ R) (hΘ : ContDiff ℝ ∞ Θ)
    (hΘp : Function.Periodic Θ (0, Real.pi)) (hφ : IsPhysicalScalarTest D φ) :
    scalarAnnularIntegral D (fun p => (radialPartial R p + angularPartial Θ p) * φ p) =
      -scalarAnnularIntegral D (fun p => R p * radialPartial φ p + Θ p * angularPartial φ p) := by
  let α : PlaneOneForm := ⟨fun p => -(φ p * Θ p), fun p => φ p * R p⟩
  have hαr : ContDiff ℝ ∞ α.radial := (hφ.1.mul hΘ).neg
  have hαθ : ContDiff ℝ ∞ α.angular := hφ.1.mul hR
  have hi := integral_exteriorCoefficient_eq_zero
    (a := D.a) (b := D.b) (c := 0) (d := Real.pi)
    (fun p _ => hαr.contDiffAt.of_le (by simp))
    (fun p _ => hαθ.contDiffAt.of_le (by simp))
    (by
      intro r _
      have hφp := hφ.2.1 (r, 0)
      have hΘp' := hΘp (r, 0)
      change -(φ (r, Real.pi) * Θ (r, Real.pi)) = -(φ (r, 0) * Θ (r, 0))
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using congrArg₂ (fun v w : ℝ => -(v * w)) hφp hΘp')
    (by
      intro θ _
      change φ (D.b, θ) * R (D.b, θ) = φ (D.a, θ) * R (D.a, θ)
      rw [(hφ.zero_endpoints θ).1, (hφ.zero_endpoints θ).2, zero_mul, zero_mul])
  have hid (p : PolarPoint) : exteriorCoefficient α p =
      (radialPartial R p + angularPartial Θ p) * φ p +
        (R p * radialPartial φ p + Θ p * angularPartial φ p) := by
    have hneg : angularPartial (fun q => -(φ q * Θ q)) p =
        -angularPartial (fun q => φ q * Θ q) p := by
      simp only [angularPartial, fderiv_fun_neg, neg_apply]
    change radialPartial (fun q => φ q * R q) p -
      angularPartial (fun q => -(φ q * Θ q)) p = _
    rw [hneg, radialPartial_mul (hφ.1.differentiable (by simp) p)
      (hR.differentiable (by simp) p),
      angularPartial_mul (hφ.1.differentiable (by simp) p)
        (hΘ.differentiable (by simp) p)]
    ring
  have hsum : scalarAnnularIntegral D (fun p =>
      (radialPartial R p + angularPartial Θ p) * φ p +
        (R p * radialPartial φ p + Θ p * angularPartial φ p)) = 0 := by
    simpa only [scalarAnnularIntegral, hid] using hi
  rw [scalarAnnularIntegral_add D
    (f := fun p => (radialPartial R p + angularPartial Θ p) * φ p)
    (g := fun p => R p * radialPartial φ p + Θ p * angularPartial φ p)
    (((weightedGraph_continuous_radialPartial hR).add
      (weightedGraph_continuous_angularPartial hΘ)).mul hφ.1.continuous)
    ((hR.continuous.mul (weightedGraph_continuous_radialPartial hφ.1)).add
      (hΘ.continuous.mul (weightedGraph_continuous_angularPartial hφ.1)))] at hsum
  linarith only [hsum]

/-- The pointwise corrected operator satisfies the literal defining weak
equation as soon as its three actual coefficient fields are smooth. -/
theorem scalarStateOperator_weak_equation
    (D : ReferenceData) (S : PhysicalSpacesData) (x : ScalarWeightedState S)
    (u : ScalarCommonHeight S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x))
    (hC : ContDiff ℝ ∞ (scalarStateCorrectedC D S x))
    (hu : ContDiff ℝ ∞ (scalarCommonHeightDecode S u))
    (hBp : Function.Periodic (scalarStateB D S x) (0, Real.pi))
    (hCp : Function.Periodic (scalarStateCorrectedC D S x) (0, Real.pi))
    (hup : Function.Periodic (scalarCommonHeightDecode S u) (0, Real.pi))
    {φ : PolarPoint → ℝ} (hφ : IsPhysicalScalarTest D φ) :
    scalarAnnularIntegral D (fun p => scalarStateOperator D S x u p * φ p) =
      -scalarAnnularIntegral D (fun p =>
        symmetricNormalFlux (scalarStateA D S x) (scalarStateB D S x)
          (scalarCommonHeightDecode S u) p * radialPartial φ p +
        symmetricAngularFlux (scalarStateB D S x) (scalarStateCorrectedC D S x)
          (scalarCommonHeightDecode S u) p * angularPartial φ p) := by
  have hR : ContDiff ℝ ∞ (symmetricNormalFlux (scalarStateA D S x)
      (scalarStateB D S x) (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p =>
      contDiffAt_symmetricNormalFlux hA.contDiffAt hB.contDiffAt hu.contDiffAt
  have hΘ : ContDiff ℝ ∞ (symmetricAngularFlux (scalarStateB D S x)
      (scalarStateCorrectedC D S x) (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p =>
      contDiffAt_symmetricAngularFlux hB.contDiffAt hC.contDiffAt hu.contDiffAt
  have hΘp : Function.Periodic (symmetricAngularFlux (scalarStateB D S x)
      (scalarStateCorrectedC D S x) (scalarCommonHeightDecode S u)) (0, Real.pi) := by
    intro p
    simp only [symmetricAngularFlux, hBp p, hCp p,
      periodic_radialPartial hup p, periodic_angularPartial hup p]
  exact scalarAnnularIntegral_divergence_mul_test D hR hΘ hΘp hφ

theorem mem_physicalScalarWeakGraph_of_decode_operator
    (D : ReferenceData) (S : PhysicalSpacesData) (x : ScalarWeightedState S)
    (u : ScalarCommonHeight S) (f : ScalarHeightSpace S)
    (hA : ContDiff ℝ ∞ (scalarStateA D S x))
    (hB : ContDiff ℝ ∞ (scalarStateB D S x))
    (hC : ContDiff ℝ ∞ (scalarStateCorrectedC D S x))
    (hu : ContDiff ℝ ∞ (scalarCommonHeightDecode S u))
    (hBp : Function.Periodic (scalarStateB D S x) (0, Real.pi))
    (hCp : Function.Periodic (scalarStateCorrectedC D S x) (0, Real.pi))
    (hup : Function.Periodic (scalarCommonHeightDecode S u) (0, Real.pi))
    (hf : ∀ p, (S.height scalarBeta).decode f p = scalarStateOperator D S x u p) :
    (u, f) ∈ PhysicalScalarWeakGraph D S x := by
  intro φ hφ
  simp_rw [hf]
  exact scalarStateOperator_weak_equation D S x u hA hB hC hu hBp hCp hup hφ

end ContinuousFlexibility.Statements
