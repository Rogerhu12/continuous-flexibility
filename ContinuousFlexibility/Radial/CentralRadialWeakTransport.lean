import ContinuousFlexibility.Radial.CentralRadialClosedGraph

/-!
# Actual radial compact tests and distribution transport

Radial tests are globally smooth and compactly supported strictly inside
the positive half-line. The forward test map is genuinely extended by
zero outside that half-line. Both source pairings use the proved ordinary
and spectral Jacobians, with the normalization factor twelve retained.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency false

/-- The compact radial test is extended by zero, rather than using the
arbitrary off-range values of the inverse radius. -/
def centralRadialCompactTest (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  if 0 < r then centralRadialHeight φ r else 0

def centralRadialTestPullback (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  centralDensityRoot x * v (centralRadius x)

theorem centralRadialCompactTest_pullback (φ : ℝ → ℝ) (x : ℝ) :
    centralRadialCompactTest φ (centralRadius x) = φ x / centralDensityRoot x := by
  rw [centralRadialCompactTest, ite_eq_left (centralRadius_pos x), centralRadialHeight_pullback]

private theorem radial_test_support_subset (φ : ℝ → ℝ) :
    Function.support (centralRadialCompactTest φ) ⊆ centralRadius '' tsupport φ := by
  intro r hr
  change centralRadialCompactTest φ r ≠ 0 at hr
  have hp : 0 < r := by
    by_contra hn
    exact hr (by simp only [centralRadialCompactTest, ite_eq_right hn])
  have hφ : φ (centralModelCoordinate r) ≠ 0 := by
    intro hz
    exact hr (by simp only [centralRadialCompactTest, ite_eq_left hp, centralRadialHeight, hz, zero_div])
  exact ⟨centralModelCoordinate r, subset_tsupport φ hφ, centralRadius_modelCoordinate hp⟩

theorem centralRadialCompactTest_tsupport_subset {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    tsupport (centralRadialCompactTest φ) ⊆ centralRadius '' tsupport φ :=
  closure_minimal (radial_test_support_subset φ) (hc.image contDiff_centralRadius.continuous).isClosed

theorem centralRadialCompactTest_hasCompactSupport {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (centralRadialCompactTest φ) :=
  (hc.image contDiff_centralRadius.continuous).of_isClosed_subset
    (isClosed_tsupport _) (centralRadialCompactTest_tsupport_subset hc)

theorem centralRadialCompactTest_tsupport_positive {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    tsupport (centralRadialCompactTest φ) ⊆ Ioi 0 := by
  intro r hr
  obtain ⟨x, _, rfl⟩ := centralRadialCompactTest_tsupport_subset hc hr
  exact centralRadius_pos x

theorem centralRadialCompactTest_eventuallyEq (φ : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    centralRadialCompactTest φ =ᶠ[𝓝 r] centralRadialHeight φ := by
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact ite_eq_left ht

theorem contDiff_centralRadialCompactTest {φ : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (centralRadialCompactTest φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : 0 < r
  · have hh := contDiffAt_centralRadialHeight hs (centralModelCoordinate r)
    rw [centralRadius_modelCoordinate hr] at hh
    exact hh.congr_of_eventuallyEq (centralRadialCompactTest_eventuallyEq φ hr)
  · have hn : r ∉ tsupport (centralRadialCompactTest φ) :=
      fun h => hr (centralRadialCompactTest_tsupport_positive hc h)
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) r).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

private theorem continuousOn_centralModelCoordinate_positive :
    ContinuousOn centralModelCoordinate (Ioi 0) := by
  intro r hr
  have hh := contDiffAt_centralModelCoordinate (centralModelCoordinate r)
  rw [centralRadius_modelCoordinate hr] at hh
  exact hh.continuousAt.continuousWithinAt

theorem contDiff_centralRadialTestPullback {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (centralRadialTestPullback v) :=
  contDiff_centralDensityRoot.mul (hs.comp contDiff_centralRadius)

theorem centralRadialTestPullback_hasCompactSupport {v : ℝ → ℝ}
    (hc : HasCompactSupport v) (hp : tsupport v ⊆ Ioi 0) :
    HasCompactSupport (centralRadialTestPullback v) := by
  have hK : IsCompact (centralModelCoordinate '' tsupport v) :=
    hc.image_of_continuousOn (continuousOn_centralModelCoordinate_positive.mono hp)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro x hx
  have hv : v (centralRadius x) ≠ 0 := by
    intro hz
    exact hx (by simp only [centralRadialTestPullback, hz, mul_zero])
  exact ⟨centralRadius x, subset_tsupport v hv, centralModelCoordinate_radius x⟩

theorem centralRadialTestPullback_compactTest (φ : ℝ → ℝ) :
    centralRadialTestPullback (centralRadialCompactTest φ) = φ := by
  funext x
  rw [centralRadialTestPullback, centralRadialCompactTest_pullback]
  field_simp [(centralDensityRoot_pos x).ne']

theorem centralRadialCompactTest_testPullback {v : ℝ → ℝ}
    (hp : tsupport v ⊆ Ioi 0) :
    centralRadialCompactTest (centralRadialTestPullback v) = v := by
  funext r
  by_cases hr : 0 < r
  · rw [centralRadialCompactTest, ite_eq_left hr, centralRadialHeight,
      centralRadialTestPullback, centralRadius_modelCoordinate hr]
    exact mul_div_cancel_left₀ _ (centralDensityRoot_pos (centralModelCoordinate r)).ne'
  · rw [centralRadialCompactTest, ite_eq_right hr]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hr (hp h))).symm

private theorem radialJacobi_congr_eventually {a : ℝ} {w u v : ℝ → ℝ} {r : ℝ}
    (h : u =ᶠ[𝓝 r] v) : radialJacobi a w u r = radialJacobi a w v r := by
  have hf : (fun t => w t * deriv u t) =ᶠ[𝓝 r] (fun t => w t * deriv v t) := by
    filter_upwards [h.deriv] with t ht
    rw [ht]
  unfold radialJacobi
  rw [hf.deriv_eq, h.eq_of_nhds]

theorem radialJacobi_centralRadialCompactTest {φ : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ φ) (j c x : ℝ) :
    radialJacobi (j ^ 2) (centralRadialProfile c) (centralRadialCompactTest φ) (centralRadius x) =
      -(c * centralDensityRoot x / deriv centralRadius x) *
        liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x := by
  rw [radialJacobi_congr_eventually
    (centralRadialCompactTest_eventuallyEq φ (centralRadius_pos x))]
  exact radialJacobi_centralRadialHeight hs j c x

private theorem radial_transport_inner_integral (u v : HermiteL2) :
    ⟪u, v⟫_ℝ = ∫ x : ℝ, u x * v x := by
  rw [L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The ordinary `dr` weak pairing uses `c/sqrt(12*c)`, not the
spectral density. Its integrability follows from two genuine L2 factors. -/
theorem centralRadial_dr_test_pairing {c : ℝ} (hc : 0 < c) (j : ℝ)
    (u : CentralRadialHilbert c) {φ : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    IntegrableOn (fun r => u r *
      (-radialJacobi (j ^ 2) (centralRadialProfile c) (centralRadialCompactTest φ) r)) (Ioi 0) ∧
    (∫ r in Ioi 0, u r *
      (-radialJacobi (j ^ 2) (centralRadialProfile c) (centralRadialCompactTest φ) r)) =
      (c / sqrt (12 * c)) *
        ⟪centralRadialInverseWeight (centralRadialHilbertEquiv hc u),
          (compactSmooth_centralImage_memLp hs hφc j).toLp
            (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)⟫_ℝ := by
  let h : HermiteL2 := centralRadialHilbertEquiv hc u
  let Hφ : HermiteL2 := (compactSmooth_centralImage_memLp hs hφc j).toLp
    (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)
  let g : ℝ → ℝ := fun r => u r *
    (-radialJacobi (j ^ 2) (centralRadialProfile c) (centralRadialCompactTest φ) r)
  have ht : sqrt (12 * c) ≠ 0 := (sqrt_pos.mpr (mul_pos (by norm_num) hc)).ne'
  have hprod : Integrable (fun x => centralRadialInverseWeight h x * Hφ x) :=
    (Lp.memLp (centralRadialInverseWeight h)).integrable_mul (Lp.memLp Hφ)
  have hae : (fun x => deriv centralRadius x * g (centralRadius x)) =ᵐ[volume]
      (fun x => (c / sqrt (12 * c)) * (centralRadialInverseWeight h x * Hφ x)) := by
    filter_upwards [centralRadialHilbertEquiv_ae hc u, centralRadialInverseWeight_ae h,
      (compactSmooth_centralImage_memLp hs hφc j).coeFn_toLp] with x hu hq hH
    change h x = centralRadialAmplitude c x * u (centralRadius x) at hu
    change Hφ x = liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x at hH
    change deriv centralRadius x *
      (u (centralRadius x) * (-radialJacobi (j ^ 2) (centralRadialProfile c)
        (centralRadialCompactTest φ) (centralRadius x))) = _
    rw [radialJacobi_centralRadialCompactTest hs, hq, hu, hH]
    unfold centralRadialAmplitude
    field_simp [ht, (deriv_centralRadius_pos x).ne', (centralRadiusLogDerivative_pos x).ne']
  have hg : IntegrableOn g (Ioi 0) :=
    (centralRadius_integrable_iff g).mpr
      ((hprod.const_mul (c / sqrt (12 * c))).congr hae.symm)
  refine ⟨hg, ?_⟩
  change (∫ r in Ioi 0, g r) = (c / sqrt (12 * c)) * ⟪centralRadialInverseWeight h, Hφ⟫_ℝ
  rw [centralRadius_integral_change, integral_congr_ae hae, integral_const_mul,
    ← radial_transport_inner_integral]

/-- The source is arbitrary in the radial Hilbert space. Only the
compact test is multiplied by `nu`; no `nu*F ∈ L2` premise is imposed. -/
theorem centralRadial_spectral_test_pairing {c : ℝ} (hc : 0 < c)
    (F : CentralRadialHilbert c) {φ : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun r => F r * centralRadialCompactTest φ r) (centralRadialSpectralMeasure c) ∧
    (∫ r, F r * centralRadialCompactTest φ r ∂centralRadialSpectralMeasure c) =
      sqrt (12 * c) * ⟪centralRadialHilbertEquiv hc F, centralRadialTestWeight φ hs hφc⟫_ℝ := by
  let f : HermiteL2 := centralRadialHilbertEquiv hc F
  let vφ : HermiteL2 := centralRadialTestWeight φ hs hφc
  let g : ℝ → ℝ := fun r => F r * centralRadialCompactTest φ r
  have hsq : sqrt (12 * c) ^ 2 = 12 * c := sq_sqrt (mul_pos (by norm_num) hc).le
  have hprod : Integrable (fun x => f x * vφ x) := (Lp.memLp f).integrable_mul (Lp.memLp vφ)
  have hae : (fun x => centralRadialPullbackDensity c x * g (centralRadius x)) =ᵐ[volume]
      (fun x => sqrt (12 * c) * (f x * vφ x)) := by
    filter_upwards [centralRadialHilbertEquiv_ae hc F, centralRadialTestWeight_ae φ hs hφc]
      with x hF hv
    change f x = centralRadialAmplitude c x * F (centralRadius x) at hF
    change vφ x = centralRadiusLogDerivative x * φ x at hv
    change centralRadialPullbackDensity c x *
      (F (centralRadius x) * centralRadialCompactTest φ (centralRadius x)) = _
    rw [centralRadialCompactTest_pullback, hF, hv]
    have hD : centralRadialPullbackDensity c x =
        sqrt (12 * c) ^ 2 * (centralDensityRoot x * centralRadiusLogDerivative x) ^ 2 := by
      rw [hsq]
      rfl
    rw [hD]
    unfold centralRadialAmplitude
    field_simp [(centralDensityRoot_pos x).ne']
  have hg : Integrable g (centralRadialSpectralMeasure c) :=
    (centralRadialSpectral_integrable_iff hc g).mpr ((hprod.const_mul _).congr hae.symm)
  refine ⟨hg, ?_⟩
  change (∫ r, g r ∂centralRadialSpectralMeasure c) = sqrt (12 * c) * ⟪f, vφ⟫_ℝ
  rw [centralRadialSpectral_integral_change hc, integral_congr_ae hae,
    integral_const_mul, ← radial_transport_inner_integral]

/-- Every physical compact test has both actual pairings integrable,
for arbitrary solution and source vectors in the radial Hilbert space. -/
theorem centralRadial_distribution_test_integrable {c : ℝ} (hc : 0 < c)
    (j : ℝ) (u F : CentralRadialHilbert c) {v : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvp : tsupport v ⊆ Ioi 0) :
    IntegrableOn (fun r => u r * (-radialJacobi (j ^ 2) (centralRadialProfile c) v r)) (Ioi 0) ∧
      Integrable (fun r => F r * v r) (centralRadialSpectralMeasure c) := by
  let φ := centralRadialTestPullback v
  have hφs : ContDiff ℝ ∞ φ := contDiff_centralRadialTestPullback hs
  have hφc : HasCompactSupport φ := centralRadialTestPullback_hasCompactSupport hvc hvp
  have hL := (centralRadial_dr_test_pairing hc j u hφs hφc).1
  have hR := (centralRadial_spectral_test_pairing hc F hφs hφc).1
  have heq : centralRadialCompactTest φ = v := centralRadialCompactTest_testPullback hvp
  rw [heq] at hL hR
  exact ⟨hL, hR⟩

/-- The actual weak equation in ordinary radial coordinates. All its
tests have compact support strictly inside the positive radial range. -/
def CentralRadialDistributionEquation (c j : ℝ) (u F : CentralRadialHilbert c) : Prop :=
  ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v → tsupport v ⊆ Ioi 0 →
    (∫ r in Ioi 0, u r * (-radialJacobi (j ^ 2) (centralRadialProfile c) v r)) =
      ∫ r, F r * v r ∂centralRadialSpectralMeasure c

private theorem radial_pairing_normalization {c t A B : ℝ}
    (hc : c ≠ 0) (ht : t ≠ 0) (hsq : t ^ 2 = 12 * c) :
    (c / t) * A = t * B ↔ A = 12 * B := by
  have hscale : (c / t) * 12 = t := by
    field_simp [ht]
    nlinarith only [hsq]
  constructor
  · intro h
    apply mul_left_cancel₀ (div_ne_zero hc ht)
    calc
      (c / t) * A = t * B := h
      _ = (c / t) * (12 * B) := by rw [← mul_assoc, hscale]
  · intro h
    rw [h, ← mul_assoc, hscale]

/-- The physical distribution equation and the normalized compact weak
graph describe exactly the same pairs under the actual Hilbert transform. -/
theorem centralRadialDistributionEquation_iff_normalized {c : ℝ} (hc : 0 < c)
    (j : ℝ) (u F : CentralRadialHilbert c) :
    CentralRadialDistributionEquation c j u F ↔
      CentralRadialCompactWeakEquation j (centralRadialHilbertEquiv hc u)
        (centralRadialHilbertEquiv hc F) := by
  have ht : sqrt (12 * c) ≠ 0 := (sqrt_pos.mpr (mul_pos (by norm_num) hc)).ne'
  have hsq : sqrt (12 * c) ^ 2 = 12 * c := sq_sqrt (mul_pos (by norm_num) hc).le
  constructor
  · intro h φ hs hφc
    have hL := centralRadial_dr_test_pairing hc j u hs hφc
    have hR := centralRadial_spectral_test_pairing hc F hs hφc
    have hh := h (centralRadialCompactTest φ) (contDiff_centralRadialCompactTest hs hφc)
      (centralRadialCompactTest_hasCompactSupport hφc) (centralRadialCompactTest_tsupport_positive hφc)
    rw [hL.2, hR.2] at hh
    exact (radial_pairing_normalization hc.ne' ht hsq).mp hh
  · intro h v hs hvc hvp
    let φ := centralRadialTestPullback v
    have hφs : ContDiff ℝ ∞ φ := contDiff_centralRadialTestPullback hs
    have hφc : HasCompactSupport φ := centralRadialTestPullback_hasCompactSupport hvc hvp
    have hL := centralRadial_dr_test_pairing hc j u hφs hφc
    have hR := centralRadial_spectral_test_pairing hc F hφs hφc
    have hh := (radial_pairing_normalization hc.ne' ht hsq).mpr (h φ hφs hφc)
    rw [← hL.2, ← hR.2] at hh
    have heq : centralRadialCompactTest φ = v := centralRadialCompactTest_testPullback hvp
    rwa [heq] at hh

theorem centralRadialDistributionEquation_iff_graph {c : ℝ} (hc : 0 < c)
    (j : ℝ) (u F : CentralRadialHilbert c) :
    CentralRadialDistributionEquation c j u F ↔
      (centralRadialHilbertEquiv hc u, centralRadialHilbertEquiv hc F) ∈ centralRadialClosedGraph j :=
  (centralRadialDistributionEquation_iff_normalized hc j u F).trans
    (mem_centralRadialClosedGraph j _ _).symm

end ContinuousFlexibility.Radial
