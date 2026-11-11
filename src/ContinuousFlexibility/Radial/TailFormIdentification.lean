import ContinuousFlexibility.Radial.TailTestPairing
import ContinuousFlexibility.Radial.TailFormCore
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The distributional description of the tail form

Compact topological support is essential here: tests stay in a region where
the density and its inverse are bounded. The weak derivative identities are
closed in the actual weighted energy norm, and the form pairing extends from
the defining smooth core by continuity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem tailFormLift_weakDerivative {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) {u d : DeepTailL2 T}
    (hud : (u, d) ∈ TailFormLift T endCut) : TailWeakDerivative T endCut u d := by
  intro ψ hψ hcψ hsψ
  have hsub : Ioo T.entrance endCut ⊆ Ioo T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_le hcut⟩
  have hs : tsupport ψ ⊆ Ioo T.entrance T.endpoint := hsψ.trans hsub
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hds : tsupport (deriv ψ) ⊆ Ioo T.entrance T.endpoint :=
    tsupport_deriv_subset.trans hs
  let L : DeepTailL2 T →L[ℝ] ℝ :=
    tailTestPairing T (deriv ψ) (tail_div_test_memLp hp hpos hdψ hcψ.deriv hds)
  let R : DeepTailL2 T →L[ℝ] ℝ :=
    tailTestPairing T ψ (tail_div_test_memLp hp hpos hψ hcψ hs)
  have hclosed : IsClosed {z : DeepTailL2 T × DeepTailL2 T | L z.1 = -R z.2} :=
    isClosed_eq (L.continuous.comp continuous_fst) (R.continuous.comp continuous_snd).neg
  have hcore : TailEnergyCore T endCut ⊆
      {z : DeepTailL2 T × DeepTailL2 T | L z.1 = -R z.2} := by
    intro z hz
    obtain ⟨φ, hφ, hcφ, _, hu, hd⟩ := hz
    change L z.1 = -R z.2
    dsimp only [L, R]
    rw [tailTestPairing_apply hp hpos hds, tailTestPairing_apply hp hpos hs,
      tail_unweighted_pairing_congr hp hpos ((subset_tsupport _).trans hds) hu,
      tail_unweighted_pairing_congr hp hpos ((subset_tsupport _).trans hs) hd]
    have hdφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
      (fun x _ => (hψ.differentiable (by simp) x).hasDerivAt)
      ((hφ.continuous.mul hdψ.continuous).integrable_of_hasCompactSupport hcφ.mul_right)
      ((hdφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
      ((hφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcφ.mul_right)
  have hresult := (closure_minimal hcore hclosed) hud
  change L u = -R d at hresult
  dsimp only [L, R] at hresult
  rwa [tailTestPairing_apply hp hpos hds, tailTestPairing_apply hp hpos hs] at hresult

/-- Integration by parts against the genuine compact test `p ψ′` identifies
the weighted differential expression with the derivative pairing. -/
theorem tailFormLift_green_test {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) {u d : DeepTailL2 T}
    (hud : (u, d) ∈ TailFormLift T endCut) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ Ioo T.entrance endCut) :
    (∫ x, u x * (-(T.p x)⁻¹ * deriv (fun y => T.p y * deriv ψ y) x)
      ∂deepTailMeasure T) = ∫ x, d x * deriv ψ x ∂deepTailMeasure T := by
  have hsub : Ioo T.entrance endCut ⊆ Ioo T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_le hcut⟩
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  let ζ : ℝ → ℝ := fun x => T.p x * deriv ψ x
  have hζ : ContDiff ℝ ∞ ζ :=
    tail_contDiff_mul_test hp hdψ (tsupport_deriv_subset.trans (hsψ.trans hsub))
  have hcζ : HasCompactSupport ζ := hcψ.deriv.mul_left
  have hsζ : tsupport ζ ⊆ Ioo T.entrance endCut :=
    tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hsψ)
  have hw := tailFormLift_weakDerivative hp hpos hcut hud ζ hζ hcζ hsζ
  have hdsζ : Function.support (deriv ζ) ⊆ Ioo T.entrance T.endpoint :=
    support_deriv_subset.trans (hsζ.trans hsub)
  calc
    (∫ x, u x * (-(T.p x)⁻¹ * deriv ζ x) ∂deepTailMeasure T) =
        -(∫ x, u x * (deriv ζ x / T.p x) ∂deepTailMeasure T) := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = -(∫ x, u x * deriv ζ x) := by
      rw [tail_integral_div_test hp hpos hdsζ]
    _ = ∫ x, d x * ζ x := by rw [hw, neg_neg]
    _ = ∫ x, d x * deriv ψ x ∂deepTailMeasure T :=
      (tail_integral_mul_test hp hpos
        (support_deriv_subset.trans (hsψ.trans hsub)) d).symm

theorem tailFriedrichsGraph_distribution {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) {u f : DeepTailL2 T}
    (h : TailFriedrichsGraph T endCut u f) : TailDistributionGraph T endCut u f := by
  obtain ⟨d, hd, hform⟩ := h
  intro ψ hψ hcψ hsψ
  have hs : tsupport ψ ⊆ Ioo T.entrance T.endpoint :=
    fun x hx => ⟨(hsψ hx).1, (hsψ hx).2.trans_le hcut⟩
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hm := tail_test_memLp hp hpos hψ hcψ hs
  have hdm := tail_test_memLp hp hpos hdψ hcψ.deriv (tsupport_deriv_subset.trans hs)
  have hcore : (hm.toLp ψ, hdm.toLp (deriv ψ)) ∈ TailEnergyCore T endCut :=
    ⟨ψ, hψ, hcψ, hsψ, MemLp.coeFn_toLp hm, MemLp.coeFn_toLp hdm⟩
  have hf := hform (hm.toLp ψ, hdm.toLp (deriv ψ)) (subset_closure hcore)
  rw [tail_inner_right_of_ae _ _ (MemLp.coeFn_toLp hm),
    tail_inner_right_of_ae _ _ (MemLp.coeFn_toLp hdm)] at hf
  exact hf.trans (tailFormLift_green_test hp hpos hcut hd hψ hcψ hsψ).symm

/-- The distributional equation extends from the defining smooth core to all
form tests because both sides are continuous on the energy product. -/
theorem tailFriedrichsGraph_of_distribution {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) {u d f : DeepTailL2 T}
    (hud : (u, d) ∈ TailFormLift T endCut)
    (hw : TailDistributionGraph T endCut u f) : TailFriedrichsGraph T endCut u f := by
  refine ⟨d, hud, ?_⟩
  have hc : IsClosed {z : DeepTailL2 T × DeepTailL2 T |
      ⟪f, z.1⟫_ℝ = ⟪d, z.2⟫_ℝ} :=
    isClosed_eq ((innerSL ℝ f).continuous.comp continuous_fst)
      ((innerSL ℝ d).continuous.comp continuous_snd)
  have hcore : TailEnergyCore T endCut ⊆
      {z : DeepTailL2 T × DeepTailL2 T | ⟪f, z.1⟫_ℝ = ⟪d, z.2⟫_ℝ} := by
    intro z hz
    obtain ⟨ψ, hψ, hcψ, hsψ, hzu, hzd⟩ := hz
    change ⟪f, z.1⟫_ℝ = ⟪d, z.2⟫_ℝ
    rw [tail_inner_right_of_ae _ _ hzu, tail_inner_right_of_ae _ _ hzd]
    exact (hw ψ hψ hcψ hsψ).trans
      (tailFormLift_green_test hp hpos hcut hud hψ hcψ hsψ)
  exact fun z hz => (closure_minimal hcore hc) hz

theorem tailFriedrichsGraph_iff_distribution {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) (u f : DeepTailL2 T) :
    TailFriedrichsGraph T endCut u f ↔
      (∃ d, (u, d) ∈ TailFormLift T endCut) ∧ TailDistributionGraph T endCut u f := by
  constructor
  · intro h
    exact ⟨⟨h.choose, h.choose_spec.1⟩, tailFriedrichsGraph_distribution hp hpos hcut h⟩
  · rintro ⟨⟨d, hd⟩, hw⟩
    exact tailFriedrichsGraph_of_distribution hp hpos hcut hd hw

/-- Closed energy lifts have a unique derivative, including for a truncated
tail considered inside the full ambient weighted space. -/
theorem tailFormLift_zero_derivative {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) {d : DeepTailL2 T}
    (hd : (0, d) ∈ TailFormLift T endCut) : d = 0 := by
  have hsub : Ioo T.entrance endCut ⊆ Ioo T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_le hcut⟩
  have hw := tailFormLift_weakDerivative hp hpos hcut hd
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo T.entrance endCut → d x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((tail_locallyIntegrableOn hp hpos d).mono_set hsub)
    intro ψ hψ hcψ hsψ
    have hds : tsupport (deriv ψ) ⊆ Ioo T.entrance T.endpoint :=
      tsupport_deriv_subset.trans (hsψ.trans hsub)
    have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
    have hm := tail_div_test_memLp hp hpos hdψ hcψ.deriv hds
    have hzero : (∫ x, (0 : DeepTailL2 T) x * deriv ψ x) = 0 := by
      rw [← tailTestPairing_apply hp hpos hds hm]
      exact map_zero _
    have hh := hw ψ hψ hcψ hsψ
    rw [hzero] at hh
    have hpair : (∫ x, d x * ψ x) = 0 := neg_eq_zero.mp hh.symm
    simpa only [smul_eq_mul, mul_comm] using hpair
  have hac : deepTailMeasure T ≪ volume :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioo T.entrance T.endpoint))
      (fun x => ENNReal.ofReal (T.p x))).trans Measure.absolutelyContinuous_restrict
  have hzμ : ∀ᵐ x ∂deepTailMeasure T, x ∈ Ioo T.entrance endCut → d x = 0 :=
    hac.ae_le hz
  have hout := (tailFormLift_ae_zero_outside hd).2
  apply Lp.ext
  filter_upwards [hzμ, hout, Lp.coeFn_zero ℝ 2 (deepTailMeasure T)] with x hi ho hzero
  rw [hzero]
  by_cases hx : x ∈ Ioo T.entrance endCut
  · exact hi hx
  · exact ho hx

/-- The Friedrichs form agrees with the actual local differential equation
for every smooth positive density. Deep-tail size estimates are not needed
for this identification. -/
theorem tailFormIdentification {T : DeepTailData} {endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hcut : endCut ≤ T.endpoint) : TailFormIdentification T endCut :=
  ⟨fun _ _ h => tailFormLift_weakDerivative hp hpos hcut h,
    fun _ h => tailFormLift_zero_derivative hp hpos hcut h,
    tailFriedrichsGraph_iff_distribution hp hpos hcut⟩

end ContinuousFlexibility.Radial
