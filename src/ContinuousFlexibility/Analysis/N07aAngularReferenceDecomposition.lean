import ContinuousFlexibility.Analysis.N07aAngularReferenceSource
import ContinuousFlexibility.Analysis.N07aAngularReferenceFlux
import ContinuousFlexibility.Analysis.N07aPhysicalPieceBound
import ContinuousFlexibility.Radial.ReferenceCosineJacobi
import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# Actual radial and angular parts of the reference source

The interface set is null by the original canonical cover. On every open
piece the measurable reference source is the actual right flux derivative
plus the true angular second derivative. The latter has zero circle mean.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

def n07aReferenceNormalSource {S : PhysicalSpacesData} (D : ReferenceData)
    (K : CanonicalData S) (v : PolarPoint → ℝ) : PolarPoint → ℝ :=
  (n07aReferencePieceInterior K).indicator (fun p =>
    deriv D.w p.1 * radialPartial v p + D.w p.1 * radialPartial (radialPartial v) p)

theorem n07aReferenceNormalSource_measurable {D : ReferenceData}
    {S : PhysicalSpacesData} (K : CanonicalData S) (hw : Measurable D.w)
    (v : PolarPoint → ℝ) : Measurable (n07aReferenceNormalSource D K v) := by
  exact ((((measurable_deriv D.w).comp measurable_fst).mul
    (measurable_fderiv_apply_const ℝ v (1, 0))).add
      ((hw.comp measurable_fst).mul
        (measurable_fderiv_apply_const ℝ (radialPartial v) (1, 0)))).indicator
    (n07aReferencePieceInterior_isOpen K).measurableSet

theorem n07a_referencePieceInterior_ae
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) :=
  n07a_physicalPieceInterior_ae h04

theorem n07a_angularSlice_second_eq {v : PolarPoint → ℝ} {p : PolarPoint}
    (hv : ContDiffAt ℝ ∞ v p) :
    deriv (deriv (fun θ => v (p.1, θ))) p.2 = angularPartial (angularPartial v) p := by
  have hv1 : ContDiffAt ℝ 1 v p := hv.of_le (by simp)
  have hd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ v q :=
    (hv1.eventually (by simp)).mono fun _ hq => hq.differentiableAt one_ne_zero
  have he : (fun θ => deriv (fun t => v (p.1, t)) θ) =ᶠ[𝓝 p.2]
      (fun θ => angularPartial v (p.1, θ)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hd] with θ hθ
    exact (hasDerivAt_angularSlice hθ).deriv
  have hd₂ := hasDerivAt_angularSlice
    ((contDiffAt_angularPartial hv (m := 1) (by simp)).differentiableAt one_ne_zero)
  exact (hd₂.congr_of_eventuallyEq he).deriv

theorem n07a_periodic_circle_second_mean_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) :
    radialAngularMean (deriv (deriv f)) = 0 := by
  have h := reference_integral_periodic_mul_second_deriv
    (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ))) hf
    (fun _ => rfl) hp
  have hz : (∫ θ in (0 : ℝ)..2 * Real.pi, deriv (deriv f) θ) = 0 := by
    simpa only [one_mul, deriv_const', deriv_const, zero_mul,
      intervalIntegral.integral_zero] using h
  rw [radialAngularMean, hz, mul_zero]

variable {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07a_referenceNormalSource_ae_right
    (hw : Differentiable ℝ D.w) {v : PolarPoint → ℝ}
    (hv : ∀ m, ContDiffOn ℝ ∞ v (physicalPieceOpen S K m))
    (hcover : ∀ᵐ r ∂volume.restrict (radialCore D),
      ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) (θ : ℝ) :
    (fun r => n07aReferenceNormalSource D K v (r, θ)) =ᵐ[volume.restrict (radialCore D)]
      fun r => n07aReferenceRightFluxDerivative D v (r, θ) := by
  filter_upwards [hcover] with r hr
  obtain ⟨m, hm⟩ := hr
  have hp : (r, θ) ∈ physicalPieceOpen S K m := ⟨hm, mem_univ _⟩
  have hmem : (r, θ) ∈ n07aReferencePieceInterior K := mem_iUnion.mpr ⟨m, hp⟩
  rw [n07aReferenceNormalSource, indicator_of_mem hmem]
  exact (n07a_referenceRightFluxDerivative_eq (hw r)
    ((hv m).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp))).symm

theorem n07a_referenceSource_mean_eq_normal_on_piece
    {v : PolarPoint → ℝ}
    {m : ℕ} (hv : ContDiffOn ℝ ∞ v (physicalPieceOpen S K m))
    (hvp : Function.Periodic v (0, Real.pi))
    {r : ℝ} (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    radialAngularMean (fun θ => n07aReferenceInteriorDifferential D K v (r, θ)) =
      radialAngularMean (fun θ => n07aReferenceNormalSource D K v (r, θ)) := by
  have hat (θ : ℝ) : ContDiffAt ℝ ∞ v (r, θ) :=
    hv.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)
  have hf : ContDiff ℝ ∞ (fun θ => v (r, θ)) := by
    rw [contDiff_iff_contDiffAt]
    intro θ
    exact (hat θ).comp θ (contDiffAt_const.prodMk contDiffAt_id)
  have hfp : Function.Periodic (fun θ => v (r, θ)) (2 * Real.pi) := by
    intro θ
    have h₁ := hvp (r, θ)
    have h₂ := hvp (r, θ + Real.pi)
    simp only [Prod.mk_add_mk, add_zero] at h₁ h₂
    convert h₂.trans h₁ using 1 <;> congr 1 <;> ring
  have hθ : (fun θ => angularPartial (angularPartial v) (r, θ)) =
      deriv (deriv (fun θ => v (r, θ))) :=
    funext fun θ => (n07a_angularSlice_second_eq (hat θ)).symm
  have hmean := n07a_periodic_circle_second_mean_zero hf hfp
  have hr₁ : Continuous (fun θ => radialPartial v (r, θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hc := (contDiffAt_radialPartial (hat θ) (m := 0) (by simp)).continuousAt
    exact hc.comp (continuous_const.prodMk continuous_id).continuousAt
  have hr₂ : Continuous (fun θ => radialPartial (radialPartial v) (r, θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hc := (contDiffAt_radialPartial
      (contDiffAt_radialPartial (hat θ) (m := 1) (by simp)) (m := 0) (by simp)).continuousAt
    exact hc.comp (continuous_const.prodMk continuous_id).continuousAt
  have hN : Continuous (fun θ => deriv D.w r * radialPartial v (r, θ) +
      D.w r * radialPartial (radialPartial v) (r, θ)) :=
    (continuous_const.mul hr₁).add (continuous_const.mul hr₂)
  have hθint : IntervalIntegrable (deriv (deriv (fun θ => v (r, θ))))
      volume 0 (2 * Real.pi) := ((contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp hf).2).2.continuous).intervalIntegrable 0 (2 * Real.pi)
  have hfull : (fun θ => n07aReferenceInteriorDifferential D K v (r, θ)) =
      fun θ => (deriv D.w r * radialPartial v (r, θ) +
        D.w r * radialPartial (radialPartial v) (r, θ)) +
        (deriv D.w r / r) * deriv (deriv (fun θ => v (r, θ))) θ := by
    funext θ
    rw [n07aReferenceInteriorDifferential_on_piece v (m := m) ⟨hr, mem_univ _⟩]
    simp only [n07aReferenceDifferential, ← hθ]
  have hnormal : (fun θ => n07aReferenceNormalSource D K v (r, θ)) =
      fun θ => deriv D.w r * radialPartial v (r, θ) +
        D.w r * radialPartial (radialPartial v) (r, θ) := by
    funext θ
    have hmem : (r, θ) ∈ n07aReferencePieceInterior K :=
      mem_iUnion.mpr ⟨m, ⟨hr, mem_univ _⟩⟩
    exact indicator_of_mem hmem _
  rw [hfull, hnormal, radialAngularMean, radialAngularMean,
    intervalIntegral.integral_add (hN.intervalIntegrable _ _)
      (hθint.const_mul (deriv D.w r / r)), intervalIntegral.integral_const_mul, mul_add]
  have hzero : (2 * Real.pi)⁻¹ * ((deriv D.w r / r) *
      ∫ θ in (0 : ℝ)..2 * Real.pi, deriv (deriv (fun θ => v (r, θ))) θ) = 0 := by
    calc
      _ = (deriv D.w r / r) * radialAngularMean
          (deriv (deriv (fun θ => v (r, θ)))) := by unfold radialAngularMean; ring
      _ = 0 := by rw [hmean, mul_zero]
  rw [hzero, add_zero]

end ContinuousFlexibility.Analysis
