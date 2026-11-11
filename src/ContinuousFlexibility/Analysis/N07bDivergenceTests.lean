import ContinuousFlexibility.Analysis.N07bHalfPeriodSeparation
import ContinuousFlexibility.Analysis.PhysicalTransmissionOperator

/-!
# Locality of the actual divergence operator on compact tests

The symmetric divergence expression depends only on the germ of its test
function. Its support therefore stays inside the test's support. Coefficients
smooth on the physical open domain suffice: compact tests make the resulting
divergence globally smooth without extending those coefficients.

The final identity transfers the full-period weak divergence pairing to the
ordinary compact planar test. It uses local physical integrability, rather
than imposing any regularity on the unencoded half-period of a representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- Local equality of test functions gives local equality of their actual
divergence expressions, even for arbitrary coefficient functions. -/
theorem n07b_divergenceOperator_eventuallyEq (L : SymmetricCoefficients)
    {u v : PolarPoint → ℝ} {p : PolarPoint} (h : u =ᶠ[𝓝 p] v) :
    divergenceOperator L u =ᶠ[𝓝 p] divergenceOperator L v := by
  let Nu := fun q => L.a q * radialPartial u q + L.b q * angularPartial u q
  let Nv := fun q => L.a q * radialPartial v q + L.b q * angularPartial v q
  let Tu := fun q => L.b q * radialPartial u q + L.c q * angularPartial u q
  let Tv := fun q => L.b q * radialPartial v q + L.c q * angularPartial v q
  have hN : Nu =ᶠ[𝓝 p] Nv := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
    change L.a q * (fderiv ℝ u q) (1, 0) + L.b q * (fderiv ℝ u q) (0, 1) =
      L.a q * (fderiv ℝ v q) (1, 0) + L.b q * (fderiv ℝ v q) (0, 1)
    rw [hq]
  have hT : Tu =ᶠ[𝓝 p] Tv := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
    change L.b q * (fderiv ℝ u q) (1, 0) + L.c q * (fderiv ℝ u q) (0, 1) =
      L.b q * (fderiv ℝ v q) (1, 0) + L.c q * (fderiv ℝ v q) (0, 1)
    rw [hq]
  filter_upwards [hN.fderiv (𝕜 := ℝ), hT.fderiv (𝕜 := ℝ)] with q hn ht
  change (fderiv ℝ Nu q) (1, 0) + (fderiv ℝ Tu q) (0, 1) =
    (fderiv ℝ Nv q) (1, 0) + (fderiv ℝ Tv q) (0, 1)
  rw [hn, ht]

theorem n07b_divergenceOperator_zero (L : SymmetricCoefficients) :
    divergenceOperator L (fun _ => 0) = (fun _ => 0) := by
  funext p
  simp [divergenceOperator, radialPartial, angularPartial]

/-- Differentiation does not enlarge the closed support of a test. -/
theorem n07b_tsupport_divergenceOperator_subset (L : SymmetricCoefficients)
    (φ : PolarPoint → ℝ) : tsupport (divergenceOperator L φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hnot
  have hz : φ =ᶠ[𝓝 p] (fun _ => 0) :=
    ((isClosed_tsupport φ).isOpen_compl.mem_nhds hnot).mono
      (fun q hq => image_eq_zero_of_notMem_tsupport hq)
  have hd := (n07b_divergenceOperator_eventuallyEq L hz).self_of_nhds
  rw [n07b_divergenceOperator_zero] at hd
  exact hp hd

/-- Smooth coefficients on an open neighborhood of the test support are
enough for global smoothness of its divergence. -/
theorem n07b_contDiff_divergence_compact_test {A : Set PolarPoint}
    (hA : IsOpen A) {L : SymmetricCoefficients}
    (ha : ContDiffOn ℝ ∞ L.a A) (hb : ContDiffOn ℝ ∞ L.b A)
    (hc : ContDiffOn ℝ ∞ L.c A) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ A) :
    ContDiff ℝ ∞ (divergenceOperator L φ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ A
  · have ha' := (ha p hp).contDiffAt (hA.mem_nhds hp)
    have hb' := (hb p hp).contDiffAt (hA.mem_nhds hp)
    have hc' := (hc p hp).contDiffAt (hA.mem_nhds hp)
    exact (contDiffAt_radialPartial
      (contDiffAt_symmetricNormalFlux ha' hb' hφ.contDiffAt) (by simp)).add
      (contDiffAt_angularPartial
        (contDiffAt_symmetricAngularFlux hb' hc' hφ.contDiffAt) (by simp))
  · have hnot : p ∉ tsupport (divergenceOperator L φ) :=
      fun h => hp (hs (n07b_tsupport_divergenceOperator_subset L φ h))
    have hz : divergenceOperator L φ =ᶠ[𝓝 p] (fun _ => 0) :=
      ((isClosed_tsupport (divergenceOperator L φ)).isOpen_compl.mem_nhds hnot).mono
        (fun q hq => image_eq_zero_of_notMem_tsupport hq)
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- Inside the open full integration period, periodizing a half-period test
does not change the germ seen by the divergence operator. -/
theorem n07b_fullPeriodTest_divergence_eqOn (L : SymmetricCoefficients)
    {φ : PolarPoint → ℝ}
    (hs : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) :
    EqOn (divergenceOperator L (n07bFullPeriodTest φ)) (divergenceOperator L φ)
      ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) (2 * Real.pi)) := by
  intro p hp
  have he : n07bFullPeriodTest φ =ᶠ[𝓝 p] φ :=
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp).mono (fun q hq =>
      n07bFullPeriodTest_eqOn hs ⟨hq.1, ⟨hq.2.1, hq.2.2.le⟩⟩)
  exact (n07b_divergenceOperator_eventuallyEq L he).self_of_nhds

/-- The weak full-period divergence pairing equals the compact planar
distribution pairing, with the same normalization factor. -/
theorem n07b_halfPeriod_divergence_pairing {D : ReferenceData}
    (hab : D.a ≤ D.b) {A : Set PolarPoint} (hopen : IsOpen A)
    (hA : A ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi)
    {L : SymmetricCoefficients}
    (ha : ContDiffOn ℝ ∞ L.a A) (hb : ContDiffOn ℝ ∞ L.b A)
    (hc : ContDiffOn ℝ ∞ L.c A)
    {u φ : PolarPoint → ℝ} (hu : LocallyIntegrableOn u A volume)
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ A) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L (n07bFullPeriodTest φ) (r, θ))) =
      (2 * Real.pi)⁻¹ * ∫ p, u p * divergenceOperator L φ p := by
  have hds : tsupport (divergenceOperator L φ) ⊆ A :=
    (n07b_tsupport_divergenceOperator_subset L φ).trans hs
  have hdc : HasCompactSupport (divergenceOperator L φ) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _)
      (n07b_tsupport_divergenceOperator_subset L φ)
  have hdd := n07b_contDiff_divergence_compact_test hopen ha hb hc hφ hs
  have hi := n07b_integrable_mul_compact_test hu hdd.continuous hdc hds
  have hsupport : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi :=
    fun p hp => ⟨mem_univ _, (hA (hs hp)).2⟩
  have hmeasure : radialPhysicalMeasure D =
      volume.restrict (radialCore D ×ˢ Ioo (0 : ℝ) (2 * Real.pi)) :=
    Measure.restrict_congr_set
      (Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Ioc.symm)
  have hmem : ∀ᵐ p ∂radialPhysicalMeasure D,
      p ∈ radialCore D ×ˢ Ioo (0 : ℝ) (2 * Real.pi) := by
    rw [hmeasure]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have he :
      (fun p => u p * divergenceOperator L (n07bFullPeriodTest φ) p)
        =ᵐ[radialPhysicalMeasure D] (fun p => u p * divergenceOperator L φ p) := by
    filter_upwards [hmem] with p hp
    change u p * divergenceOperator L (n07bFullPeriodTest φ) p =
      u p * divergenceOperator L φ p
    rw [n07b_fullPeriodTest_divergence_eqOn L hsupport ⟨mem_univ _, hp.2⟩]
  have hip : Integrable (fun p => u p * divergenceOperator L (n07bFullPeriodTest φ) p)
      (radialPhysicalMeasure D) := hi.integrableOn.congr he.symm
  rw [Radial.r11b_integral_angularMean_eq hab hip, integral_congr_ae he]
  congr 1
  change (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi),
    u p * divergenceOperator L φ p) = ∫ p, u p * divergenceOperator L φ p
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hd0 : divergenceOperator L φ p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => by
      have hpin := hA (hds h)
      exact hp ⟨hpin.1, ⟨hpin.2.1,
        hpin.2.2.le.trans (by linarith [Real.pi_pos])⟩⟩)
  change u p * divergenceOperator L φ p = 0
  rw [hd0, mul_zero]

end ContinuousFlexibility.Analysis
