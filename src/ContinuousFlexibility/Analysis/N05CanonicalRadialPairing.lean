module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05CanonicalRadialTestDerivative
public import ContinuousFlexibility.Analysis.N05CanonicalAngularPairing
public import ContinuousFlexibility.Scalar.Conservation
public import ContinuousFlexibility.Scalar.WeightedPartialIdentities

/-!
# The genuine canonical first radial weak derivative

The transported radial test converts the physical weak normal identity
into the literal canonical test pairing. All four physical products are
integrable L² pairings; the logarithmic-height correction is eliminated
pointwise before integration, so no separate coefficient integrability is
assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped ContDiff Topology

theorem n05CanonicalTest_radial {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    CanonicalTest S K m (radialPartial φ) := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun p =>
    contDiffAt_radialPartial hφ.1.contDiffAt (by simp)), periodic_radialPartial hφ.2.1, ?_⟩
  obtain ⟨J, hJ, hJI, hzero⟩ := hφ.2.2
  refine ⟨J, hJ, hJI, fun r hr θ => ?_⟩
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 (r, θ), q.1 ∉ J :=
    (hJ.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hr
  have he : φ =ᶠ[𝓝 (r, θ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnear] with q hq
    exact hzero q.1 hq q.2
  calc
    _ = radialPartial (fun _ : PolarPoint => (0 : ℝ)) (r, θ) :=
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (he.fderiv_eq (𝕜 := ℝ))
    _ = 0 := radialPartial_const 0

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
theorem n05CanonicalRadialTestTransport_radial_zero_of_outside (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) {p : PolarPoint}
    (hp : p ∉ referencePhysicalPieceOpen S K m) :
    radialPartial (n05CanonicalRadialTestTransport S C K m φ) p = 0 := by
  obtain ⟨J, hJ, hJI, hzero⟩ :=
    n05CanonicalRadialTestTransport_compact_support h hcoordinates m hφ
  have hpJ : p.1 ∉ J := fun hj => hp ⟨hJI hj, mem_univ _⟩
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ J :=
    (hJ.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpJ
  have he : n05CanonicalRadialTestTransport S C K m φ =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnear] with q hq
    exact hzero q.1 hq q.2
  calc
    _ = radialPartial (fun _ : PolarPoint => (0 : ℝ)) p :=
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (he.fderiv_eq (𝕜 := ℝ))
    _ = 0 := radialPartial_const 0

include h hcoordinates in
/-- The field `g` is the actual radial correction on this real piece.
Its canonical height represents the literal first weak radial derivative.
The formula is local; global weights can construct `g` independently. -/
theorem n05_weakCanonicalRadialDerivative_of_physical (hab : D.a ≤ D.b) (m : ℕ)
    {u ur g : PolarPoint → ℝ}
    (hup : Function.Periodic u (0, Real.pi)) (hgp : Function.Periodic g (0, Real.pi))
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hur : MemLp ur 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hweak : WeakNormalDerivative D u ur)
    (hformula : ∀ p ∈ referencePhysicalPieceOpen S K m,
      g p = (ur p - u p * (radialPartial (K.height (C.referenceState, 0) m) p /
        K.height (C.referenceState, 0) m p)) / planeJacobian (K.chart (C.referenceState, 0) m) p)
    {f d : CanonicalL2 S K m}
    (hf : (f : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m u)
    (hd : (d : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m g) :
    ∀ φ, CanonicalTest S K m φ →
      (∫ p, d p * φ p ∂canonicalMeasure S K m) =
        -(∫ p, f p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) := by
  intro φ hφ
  let τ := n05CanonicalAngularTransport S C K m φ
  let τr := n05CanonicalAngularTransport S C K m (radialPartial φ)
  let ψ := n05CanonicalRadialTestTransport S C K m φ
  have hφr := n05CanonicalTest_radial hφ
  have hτ := n05CanonicalAngularTransport_test h hcoordinates m hφ
  have hτr := n05CanonicalAngularTransport_test h hcoordinates m hφr
  have hψ := n05CanonicalRadialTestTransport_test h hcoordinates m hφ
  have hτLp : MemLp τ 2 (radialPhysicalMeasure D) := r11b_continuous_memLp hτ.1.continuous
  have hτrLp : MemLp τr 2 (radialPhysicalMeasure D) := r11b_continuous_memLp hτr.1.continuous
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) := r11b_continuous_memLp hψ.1.continuous
  have hψrSmooth : ContDiff ℝ ∞ (radialPartial ψ) :=
    contDiff_iff_contDiffAt.mpr (fun p => contDiffAt_radialPartial hψ.1.contDiffAt (by simp))
  have hψrLp : MemLp (radialPartial ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψrSmooth.continuous
  have hpoint (p : PolarPoint) :
      g p * τ p + u p * τr p = ur p * ψ p + u p * radialPartial ψ p := by
    by_cases hp : p ∈ referencePhysicalPieceOpen S K m
    · have hval : ψ p = τ p / planeJacobian (K.chart (C.referenceState, 0) m) p := by
        change n05CanonicalAngularTransport S C K m φ p /
          deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1 = _
        rw [n05_reference_planeJacobian_radial h hcoordinates m hp]
      have hder : radialPartial ψ p = τr p -
          (radialPartial (K.height (C.referenceState, 0) m) p /
            K.height (C.referenceState, 0) m p) * ψ p :=
        n05CanonicalRadialTestTransport_radial h hcoordinates m hφ.1 hp
      rw [hformula p hp, hder, hval]
      simp only [div_eq_mul_inv]
      ring
    · have hr : p.1 ∉ Ioo (K.physicalLeft m) (K.physicalRight m) :=
        fun hr => hp ⟨hr, mem_univ _⟩
      have hz (q : PolarPoint → ℝ) : n05CanonicalAngularTransport S C K m q p = 0 := by
        simp only [n05CanonicalAngularTransport, if_neg hr]
      have hψ0 : ψ p = 0 := by
        change n05CanonicalAngularTransport S C K m φ p /
          deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1 = 0
        rw [hz φ, zero_div]
      have hdψ0 : radialPartial ψ p = 0 :=
        n05CanonicalRadialTestTransport_radial_zero_of_outside h hcoordinates m hφ hp
      rw [show τ p = 0 from hz φ, show τr p = 0 from hz (radialPartial φ), hψ0, hdψ0]
      ring
  have he : (∫ p, g p * τ p + u p * τr p ∂radialPhysicalMeasure D) =
      ∫ p, ur p * ψ p + u p * radialPartial ψ p ∂radialPhysicalMeasure D :=
    integral_congr_ae (Eventually.of_forall hpoint)
  have hgτInt : Integrable (fun p => g p * τ p) (radialPhysicalMeasure D) :=
    hg.integrable_mul hτLp
  have huτrInt : Integrable (fun p => u p * τr p) (radialPhysicalMeasure D) :=
    hu.integrable_mul hτrLp
  have hurψInt : Integrable (fun p => ur p * ψ p) (radialPhysicalMeasure D) :=
    hur.integrable_mul hψLp
  have huψrInt : Integrable (fun p => u p * radialPartial ψ p) (radialPhysicalMeasure D) :=
    hu.integrable_mul hψrLp
  rw [integral_add hgτInt huτrInt, integral_add hurψInt huψrInt] at he
  have hw := hweak ψ hψ
  rw [r11b_integral_angularMean_mul_eq hab hu hψrLp,
    r11b_integral_angularMean_mul_eq hab hur hψLp] at hw
  have hfull : (∫ p, u p * radialPartial ψ p ∂radialPhysicalMeasure D) =
      -(∫ p, ur p * ψ p ∂radialPhysicalMeasure D) := by
    apply mul_left_cancel₀ (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
    simpa only [mul_neg] using hw
  have hpaired : (∫ p, g p * τ p ∂radialPhysicalMeasure D) =
      -(∫ p, u p * τr p ∂radialPhysicalMeasure D) := by linarith only [he, hfull]
  have hrad : mixedDerivative 1 0 φ = radialPartial φ :=
    funext fun p => (radialPartial_eq_mixedDerivative_on isOpen_univ hφ.1.contDiffOn (mem_univ p)).symm
  have hdφ : (fun p => d p * φ p) =ᵐ[canonicalMeasure S K m]
      (fun p => canonicalHeight S K (C.referenceState, 0) m g p * φ p) :=
    hd.mul (show φ =ᵐ[canonicalMeasure S K m] φ from EventuallyEq.rfl)
  have hfφ : (fun p => f p * radialPartial φ p) =ᵐ[canonicalMeasure S K m]
      (fun p => canonicalHeight S K (C.referenceState, 0) m u p * radialPartial φ p) :=
    hf.mul (show radialPartial φ =ᵐ[canonicalMeasure S K m] radialPartial φ from EventuallyEq.rfl)
  rw [hrad, integral_congr_ae hdφ, integral_congr_ae hfφ,
    n05_canonicalHeight_angular_test_pairing hab h hcoordinates m hgp hg hφ,
    n05_canonicalHeight_angular_test_pairing hab h hcoordinates m hup hu hφr,
    r11b_integral_angularMean_mul_eq hab hg hτLp,
    r11b_integral_angularMean_mul_eq hab hu hτrLp, hpaired]
  ring

end ContinuousFlexibility.Statements
