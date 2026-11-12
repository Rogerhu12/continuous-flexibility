import ContinuousFlexibility.Analysis.SpacesMollifierL1
import ContinuousFlexibility.Analysis.SpacesLpOverlap

/-!
# Actual planar L² estimates for normalized convolution

Translation is continuous in the squared L² distance. A nonnegative
kernel of mass one satisfies a squared-error estimate, proved from the
nonnegative weighted variance and Fubini. The proof also establishes
square integrability of the convolution residual.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function MeasureTheory
open scoped Topology Convolution ENNReal

theorem n05_continuous_integral_sq_translation_sub
    {f : SpacesPlane → ℝ} (hf : MemLp f 2 volume) :
    Continuous (fun y : SpacesPlane => ∫ x, (f (x - y) - f x) ^ 2) := by
  let u := hf.toLp f
  let g (y : SpacesPlane) : C(SpacesPlane, SpacesPlane) :=
    ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g
      (continuous_snd.sub continuous_fst)
  have hgm (y : SpacesPlane) : MeasurePreserving (g y) volume volume :=
    measurePreserving_sub_right volume y
  let τ (y : SpacesPlane) := Lp.compMeasurePreserving (g y) (hgm y) u
  have hτ : Continuous τ :=
    continuous_const.compMeasurePreservingLp hg hgm (by simp : (2 : ENNReal) ≠ ∞)
  have he (y : SpacesPlane) :
      ‖τ y - u‖ ^ 2 = ∫ x, (f (x - y) - f x) ^ 2 := by
    rw [spacesLpReal_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (τ y) u, Lp.coeFn_compMeasurePreserving u (hgm y),
      MemLp.coeFn_toLp hf, (hgm y).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hf)]
      with x hs ht hx hxy
    rw [hs]
    simp only [Pi.sub_apply]
    rw [ht]
    change (u (x - y) - u x) ^ 2 = (f (x - y) - f x) ^ 2
    change u (x - y) = f (x - y) at hxy
    rw [hx, hxy]
  have hcont : Continuous (fun y : SpacesPlane => ‖τ y - u‖ ^ 2) :=
    (hτ.sub (continuous_const (y := u))).norm.pow 2
  simpa only [he] using hcont

/-- The scalar probability-weighted square inequality, without a change
of measure. It follows by integrating the nonnegative variance. -/
theorem n05_weighted_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {κ r : α → ℝ} (hκ : Integrable κ μ)
    (hr : Integrable (fun x => κ x * r x) μ)
    (hr₂ : Integrable (fun x => κ x * r x ^ 2) μ)
    (hnon : ∀ x, 0 ≤ κ x) (hmass : ∫ x, κ x ∂μ = 1) :
    (∫ x, κ x * r x ∂μ) ^ 2 ≤ ∫ x, κ x * r x ^ 2 ∂μ := by
  let a : ℝ := ∫ x, κ x * r x ∂μ
  have he :
      (∫ x, κ x * (r x - a) ^ 2 ∂μ) =
        (∫ x, κ x * r x ^ 2 ∂μ) -
          (2 * a) * (∫ x, κ x * r x ∂μ) + a ^ 2 * (∫ x, κ x ∂μ) := by
    calc
      (∫ x, κ x * (r x - a) ^ 2 ∂μ) =
          ∫ x, κ x * r x ^ 2 - (2 * a) * (κ x * r x) + a ^ 2 * κ x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by
        have hlinear : Integrable (fun x => (2 * a) * (κ x * r x)) μ :=
          hr.const_mul (2 * a)
        have hsub : Integrable
            (fun x => κ x * r x ^ 2 - (2 * a) * (κ x * r x)) μ :=
          hr₂.sub hlinear
        rw [integral_add hsub (hκ.const_mul (a ^ 2)),
          integral_sub hr₂ hlinear, integral_const_mul, integral_const_mul]
  have hn : 0 ≤ ∫ x, κ x * (r x - a) ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hnon x) (sq_nonneg _))
  rw [he, hmass] at hn
  dsimp only [a] at hn
  nlinarith

theorem n05_integrable_convolution_sq_residual_integrand
    {f κ : SpacesPlane → ℝ} (hf : MemLp f 2 volume) (hκ : Integrable κ volume)
    (hnon : ∀ y, 0 ≤ κ y) :
    Integrable (fun p : SpacesPlane × SpacesPlane =>
      κ p.2 * (f (p.1 - p.2) - f p.1) ^ 2) (volume.prod volume) := by
  have h₁ : Integrable (fun p : SpacesPlane × SpacesPlane =>
      κ p.2 * f (p.1 - p.2) ^ 2) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      hκ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf.integrable_sq
  have h₂ : Integrable (fun p : SpacesPlane × SpacesPlane =>
      κ p.2 * f p.1 ^ 2) (volume.prod volume) := by
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
      (hκ.mul_prod hf.integrable_sq).swap
  have hsub : AEStronglyMeasurable
      (fun p : SpacesPlane × SpacesPlane => f (p.1 - p.2)) (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  have hmeas : AEStronglyMeasurable
      (fun p : SpacesPlane × SpacesPlane => κ p.2 * (f (p.1 - p.2) - f p.1) ^ 2)
      (volume.prod volume) :=
    hκ.aestronglyMeasurable.comp_snd.mul
      ((hsub.sub hf.aestronglyMeasurable.comp_fst).pow 2)
  apply ((h₁.add h₂).const_mul 2).mono' hmeas
  filter_upwards [] with p
  simp only [Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hnon p.2) (sq_nonneg _))]
  calc
    κ p.2 * (f (p.1 - p.2) - f p.1) ^ 2 ≤
        κ p.2 * (2 * f (p.1 - p.2) ^ 2 + 2 * f p.1 ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (hnon p.2)
      nlinarith [sq_nonneg (f (p.1 - p.2) + f p.1)]
    _ = 2 * (κ p.2 * f (p.1 - p.2) ^ 2 + κ p.2 * f p.1 ^ 2) := by ring

theorem n05_convolution_sq_residual_ae_le
    {f κ : SpacesPlane → ℝ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (hκ : Integrable κ volume) (hnon : ∀ y, 0 ≤ κ y) (hmass : ∫ y, κ y = 1) :
    ∀ᵐ x ∂volume,
      ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2 ≤
        ∫ y, κ y * (f (x - y) - f x) ^ 2 := by
  have hQ := n05_integrable_convolution_sq_residual_integrand hf₂ hκ hnon
  filter_upwards [hκ.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hf₁,
    hQ.prod_right_ae] with x hx hQx
  have hr : Integrable (fun y => κ y * (f (x - y) - f x)) volume := by
    simp only [mul_sub]
    exact hx.sub (hκ.mul_const (f x))
  have he :
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x =
        ∫ y, κ y * (f (x - y) - f x) := by
    rw [show (∫ y, κ y * (f (x - y) - f x)) =
        (∫ y, κ y * f (x - y)) - ∫ y, κ y * f x by
      simp only [mul_sub]
      exact integral_sub hx (hκ.mul_const (f x))]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
      integral_mul_const, hmass, one_mul]
  rw [he]
  exact n05_weighted_integral_sq_le hκ hr hQx hnon hmass

theorem n05_memLp_convolution_sub
    {f κ : SpacesPlane → ℝ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (hκ : Integrable κ volume) (hnon : ∀ y, 0 ≤ κ y) (hmass : ∫ y, κ y = 1) :
    MemLp (fun x => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume := by
  have hmeas := ((hκ.integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hf₁).sub hf₁).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  apply (n05_integrable_convolution_sq_residual_integrand hf₂ hκ hnon).integral_prod_left.mono'
    (hmeas.pow 2)
  filter_upwards [n05_convolution_sq_residual_ae_le hf₁ hf₂ hκ hnon hmass] with x hx
  change ‖((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (sq_nonneg ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x))]
  exact hx

theorem n05_integral_sq_convolution_sub_le
    {f κ : SpacesPlane → ℝ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (hκ : Integrable κ volume) (hnon : ∀ y, 0 ≤ κ y) (hmass : ∫ y, κ y = 1) {ε : ℝ}
    (hsmall : ∀ y ∈ support κ, (∫ x, (f (x - y) - f x) ^ 2) ≤ ε) :
    (∫ x, ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2) ≤ ε := by
  let Q (p : SpacesPlane × SpacesPlane) := κ p.2 * (f (p.1 - p.2) - f p.1) ^ 2
  have hQ : Integrable Q (volume.prod volume) :=
    n05_integrable_convolution_sq_residual_integrand hf₂ hκ hnon
  calc
    (∫ x, ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) ^ 2) ≤
        ∫ x, ∫ y, Q (x, y) :=
      integral_mono_ae (n05_memLp_convolution_sub hf₁ hf₂ hκ hnon hmass).integrable_sq
        hQ.integral_prod_left (n05_convolution_sq_residual_ae_le hf₁ hf₂ hκ hnon hmass)
    _ = ∫ y, κ y * ∫ x, (f (x - y) - f x) ^ 2 := by
      rw [integral_integral_swap (by
        simpa only [Function.uncurry_def, Prod.eta] using hQ)]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [Q, integral_const_mul]
    _ ≤ ∫ y, κ y * ε := by
      have hi : Integrable
          (fun y : SpacesPlane => κ y * ∫ x, (f (x - y) - f x) ^ 2) volume := by
        simpa only [Q, integral_const_mul] using hQ.integral_prod_right
      apply integral_mono hi (hκ.mul_const ε)
      intro y
      by_cases hy : y ∈ support κ
      · exact mul_le_mul_of_nonneg_left (hsmall y hy) (hnon y)
      · simp only [notMem_support.mp hy, zero_mul, le_refl]
    _ = ε := by rw [integral_mul_const, hmass, one_mul]

end ContinuousFlexibility.Analysis
