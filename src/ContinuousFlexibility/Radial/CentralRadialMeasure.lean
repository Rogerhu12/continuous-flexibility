module

public import ContinuousFlexibility.Radial.CentralRadiusMetric
public import ContinuousFlexibility.Radial.CentralRadiusGrowth
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual central radial measure and full-line change of variables

The measure is defined by the physical density `12 w / r²` on positive radii.
Its identification with a pushforward is a theorem. Ordinary `dr` source
pairings keep their different Jacobian. No closed radial operator or choice
of a radial orthogonal reduced inverse is asserted here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual radius is an order isomorphism onto the positive half-line. -/
def centralRadiusOrderIso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfRightInverse
    (fun x => (⟨centralRadius x, centralRadius_pos x⟩ : Ioi (0 : ℝ)))
    (fun _ _ h => strictMono_centralRadius h)
    (fun r => centralModelCoordinate r)
    (fun r => Subtype.ext (centralRadius_modelCoordinate r.property))

theorem measurableEmbedding_centralRadius : MeasurableEmbedding centralRadius :=
  (MeasurableEmbedding.subtype_coe measurableSet_Ioi).comp
    centralRadiusOrderIso.toHomeomorph.toMeasurableEquiv.measurableEmbedding

theorem centralRadius_lintegral_change (g : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi 0, g r =
      ∫⁻ x, ENNReal.ofReal (deriv centralRadius x) * g (centralRadius x) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    strictMono_centralRadius.injective.injOn g
  simpa only [image_univ, range_centralRadius, Measure.restrict_univ,
    abs_of_pos (deriv_centralRadius_pos _)] using h

theorem centralRadius_integrable_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      Integrable (fun x => deriv centralRadius x * g (centralRadius x)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    strictMono_centralRadius.injective.injOn g
  simpa only [image_univ, range_centralRadius, IntegrableOn, Measure.restrict_univ,
    abs_of_pos (deriv_centralRadius_pos _), smul_eq_mul] using h

theorem centralRadius_integral_change (g : ℝ → ℝ) :
    ∫ r in Ioi 0, g r =
      ∫ x, deriv centralRadius x * g (centralRadius x) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    strictMono_centralRadius.injective.injOn g
  simpa only [image_univ, range_centralRadius, Measure.restrict_univ,
    abs_of_pos (deriv_centralRadius_pos _), smul_eq_mul] using h

def centralRadialVarpi (c r : ℝ) : ℝ :=
  12 * centralRadialProfile c r / r ^ 2

def centralRadialSpectralMeasure (c : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun r => ENNReal.ofReal (centralRadialVarpi c r))

/-- The real full-line density before taking its square root. -/
def centralRadialPullbackDensity (c x : ℝ) : ℝ :=
  12 * c * (centralDensityRoot x * centralRadiusLogDerivative x) ^ 2

theorem centralRadialVarpi_pos {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    0 < centralRadialVarpi c r :=
  div_pos (mul_pos (by norm_num) (centralRadialProfile_pos hc hr)) (sq_pos_of_pos hr)

theorem continuousOn_centralRadialVarpi (c : ℝ) :
    ContinuousOn (centralRadialVarpi c) (Ioi 0) := by
  exact (continuousOn_const.mul (contDiffOn_centralRadialProfile c).continuousOn).div
    (continuousOn_id.pow 2) (fun r hr => pow_ne_zero 2 (ne_of_gt hr))

theorem centralRadialVarpi_aemeasurable (c : ℝ) :
    AEMeasurable (fun r => ENNReal.ofReal (centralRadialVarpi c r))
      (volume.restrict (Ioi 0)) :=
  (continuousOn_centralRadialVarpi c).aemeasurable measurableSet_Ioi |>.ennreal_ofReal

theorem continuous_centralRadialPullbackDensity (c : ℝ) :
    Continuous (centralRadialPullbackDensity c) :=
  continuous_const.mul
    ((contDiff_centralDensityRoot.continuous.mul
      contDiff_centralRadiusLogDerivative.continuous).pow 2)

theorem centralRadialPullbackDensity_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < centralRadialPullbackDensity c x :=
  mul_pos (mul_pos (by norm_num) hc)
    (sq_pos_of_pos (mul_pos (centralDensityRoot_pos x) (centralRadiusLogDerivative_pos x)))

theorem centralRadialVarpi_pullback_density (c x : ℝ) :
    deriv centralRadius x * centralRadialVarpi c (centralRadius x) =
      centralRadialPullbackDensity c x := by
  unfold centralRadialVarpi centralRadialPullbackDensity centralRadiusLogDerivative
  rw [centralRadialProfile_pullback]
  field_simp [(centralRadius_pos x).ne']

theorem centralRadialSpectralMeasure_map (c : ℝ) :
    Measure.map centralRadius
      (volume.withDensity (fun x => ENNReal.ofReal (centralRadialPullbackDensity c x))) =
      centralRadialSpectralMeasure c := by
  ext s hs
  have hpre := contDiff_centralRadius.continuous.measurable hs
  rw [Measure.map_apply contDiff_centralRadius.continuous.measurable hs,
    withDensity_apply _ hpre]
  calc
    _ = ∫⁻ x, (centralRadius ⁻¹' s).indicator
        (fun x => ENNReal.ofReal (centralRadialPullbackDensity c x)) x :=
      (lintegral_indicator hpre _).symm
    _ = ∫⁻ x, ENNReal.ofReal (deriv centralRadius x) *
        s.indicator (fun r => ENNReal.ofReal (centralRadialVarpi c r))
          (centralRadius x) := by
      apply lintegral_congr
      intro x
      by_cases hx : centralRadius x ∈ s
      · simp only [mem_preimage, hx, indicator_of_mem]
        rw [← ENNReal.ofReal_mul (deriv_centralRadius_pos x).le,
          centralRadialVarpi_pullback_density]
      · simp [hx]
    _ = ∫⁻ r in Ioi 0,
        s.indicator (fun r => ENNReal.ofReal (centralRadialVarpi c r)) r :=
      (centralRadius_lintegral_change _).symm
    _ = centralRadialSpectralMeasure c s := by
      rw [lintegral_indicator hs, centralRadialSpectralMeasure,
        withDensity_apply _ hs]

theorem centralRadialSpectral_integrable_iff {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) :
    Integrable g (centralRadialSpectralMeasure c) ↔
      Integrable (fun x => centralRadialPullbackDensity c x * g (centralRadius x)) := by
  rw [← centralRadialSpectralMeasure_map,
    measurableEmbedding_centralRadius.integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (continuous_centralRadialPullbackDensity c).measurable.ennreal_ofReal
      (by simp)]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (centralRadialPullbackDensity_pos hc _).le,
    smul_eq_mul]

theorem centralRadialSpectral_integral_change {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) :
    ∫ r, g r ∂centralRadialSpectralMeasure c =
      ∫ x, centralRadialPullbackDensity c x * g (centralRadius x) := by
  rw [← centralRadialSpectralMeasure_map, measurableEmbedding_centralRadius.integral_map,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_centralRadialPullbackDensity c).measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (centralRadialPullbackDensity_pos hc _).le,
    smul_eq_mul]

/-- The ordinary forcing pairing keeps the Jacobian `R'/s`. -/
theorem centralRadial_source_pairing_integral (u ψ f : ℝ → ℝ)
    (hu : ∀ x, u (centralRadius x) = ψ x / centralDensityRoot x) :
    ∫ r in Ioi 0, u r * f r =
      ∫ x, ψ x * (deriv centralRadius x / centralDensityRoot x * f (centralRadius x)) := by
  rw [centralRadius_integral_change]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by dsimp only; rw [hu]; ring)

theorem centralRadial_source_pairing_integrable_iff (u ψ f : ℝ → ℝ)
    (hu : ∀ x, u (centralRadius x) = ψ x / centralDensityRoot x) :
    IntegrableOn (fun r => u r * f r) (Ioi 0) ↔
      Integrable (fun x =>
        ψ x * (deriv centralRadius x / centralDensityRoot x * f (centralRadius x))) := by
  rw [centralRadius_integrable_iff]
  have heq : (fun x => deriv centralRadius x * (u (centralRadius x) * f (centralRadius x))) =
      (fun x => ψ x * (deriv centralRadius x / centralDensityRoot x * f (centralRadius x))) := by
    funext x
    rw [hu]
    ring
  rw [heq]

/-- The manuscript's actual full-domain Hilbert square-density identity. -/
theorem centralRadial_height_sq_integral {c : ℝ} (hc : 0 < c) (u ψ : ℝ → ℝ)
    (hu : ∀ x, u (centralRadius x) = ψ x / centralDensityRoot x) :
    ∫ r, u r ^ 2 ∂centralRadialSpectralMeasure c =
      12 * c * ∫ x, (centralRadiusLogDerivative x * ψ x) ^ 2 := by
  rw [centralRadialSpectral_integral_change hc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [hu]
  unfold centralRadialPullbackDensity
  field_simp [(centralDensityRoot_pos x).ne']

theorem centralRadial_height_sq_integrable_iff {c : ℝ} (hc : 0 < c) (u ψ : ℝ → ℝ)
    (hu : ∀ x, u (centralRadius x) = ψ x / centralDensityRoot x) :
    Integrable (fun r => u r ^ 2) (centralRadialSpectralMeasure c) ↔
      Integrable (fun x => (centralRadiusLogDerivative x * ψ x) ^ 2) := by
  rw [centralRadialSpectral_integrable_iff hc]
  have heq : (fun x => centralRadialPullbackDensity c x * u (centralRadius x) ^ 2) =
      (fun x => (12 * c) * (centralRadiusLogDerivative x * ψ x) ^ 2) := by
    funext x
    rw [hu]
    unfold centralRadialPullbackDensity
    field_simp [(centralDensityRoot_pos x).ne']
  rw [heq, integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) hc.ne'))]

/-- The spectral source pairing, kept separate from the ordinary `dr` source. -/
theorem centralRadial_spectral_pairing_integral {c : ℝ} (hc : 0 < c) (u ψ F : ℝ → ℝ)
    (hu : ∀ x, u (centralRadius x) = ψ x / centralDensityRoot x) :
    ∫ r, u r * F r ∂centralRadialSpectralMeasure c =
      12 * c * ∫ x, (centralRadiusLogDerivative x * ψ x) *
        (centralDensityRoot x * centralRadiusLogDerivative x * F (centralRadius x)) := by
  rw [centralRadialSpectral_integral_change hc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [hu]
  unfold centralRadialPullbackDensity
  field_simp [(centralDensityRoot_pos x).ne']

private theorem centralRadialInterval_aecover {μ : Measure ℝ}
    (hμ : μ ≪ volume.restrict (Ioi (0 : ℝ))) :
    AECover μ atTop (fun n : ℕ =>
      Icc (centralRadius (-(n : ℝ))) (centralRadius (n : ℝ))) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => centralRadius (-(n : ℝ))) atTop (𝓝 0) :=
    tendsto_centralRadius_atBot.comp (tendsto_neg_atTop_atBot.comp hn)
  have hr : Tendsto (fun n : ℕ => centralRadius (n : ℝ)) atTop atTop :=
    tendsto_centralRadius_atTop.comp hn
  have hleft : AECover (volume.restrict (Ioi (0 : ℝ))) atTop
      (fun n : ℕ => Ici (centralRadius (-(n : ℝ)))) := aecover_Ioi_of_Ici hl
  have hright : AECover (volume.restrict (Ioi (0 : ℝ))) atTop
      (fun n : ℕ => Iic (centralRadius (n : ℝ))) := aecover_Iic hr
  have h := hleft.inter hright
  exact ⟨hμ.ae_le h.ae_eventually_mem, h.measurableSet⟩

/-- Actual finite-radius truncations exhaust the ordinary source integral. -/
theorem centralRadial_dr_truncation {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    Tendsto (fun n : ℕ =>
      ∫ r in Icc (centralRadius (-(n : ℝ))) (centralRadius (n : ℝ)), g r)
      atTop (𝓝 (∫ r in Ioi 0, g r)) := by
  have h := (centralRadialInterval_aecover (μ := volume.restrict (Ioi 0))
    Measure.AbsolutelyContinuous.rfl).integral_tendsto_of_countably_generated hg
  have heq : ∀ n : ℕ,
      (volume.restrict (Ioi (0 : ℝ))).restrict
          (Icc (centralRadius (-(n : ℝ))) (centralRadius (n : ℝ))) =
        volume.restrict (Icc (centralRadius (-(n : ℝ))) (centralRadius (n : ℝ))) := by
    intro n
    apply Measure.restrict_restrict_of_subset
    intro r hr
    exact lt_of_lt_of_le (centralRadius_pos _) hr.1
  simpa only [heq] using h

/-- The same actual finite-radius truncations exhaust the spectral integral. -/
theorem centralRadial_spectral_truncation {c : ℝ} {g : ℝ → ℝ}
    (hg : Integrable g (centralRadialSpectralMeasure c)) :
    Tendsto (fun n : ℕ =>
      ∫ r in Icc (centralRadius (-(n : ℝ))) (centralRadius (n : ℝ)),
        g r ∂centralRadialSpectralMeasure c)
      atTop (𝓝 (∫ r, g r ∂centralRadialSpectralMeasure c)) :=
  (centralRadialInterval_aecover
    (withDensity_absolutelyContinuous (volume.restrict (Ioi 0)) _)).integral_tendsto_of_countably_generated hg

end ContinuousFlexibility.Radial
