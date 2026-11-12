import ContinuousFlexibility.Analysis.CircleAngularJetLinear
import ContinuousFlexibility.Analysis.CircleEnergyDifferentiation
import ContinuousFlexibility.Analysis.ScalarDerivativeLimit

/-!
# Full circle derivatives from actual scalar second variations

The scalar Taylor remainder is applied after multiplying each angular
jet by its exact material weight. A summable energy envelope for the
second variation then gives convergence of the entire circle-valued
difference quotient in every projective norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

local instance circleTaylorDifferentiationRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

private theorem abs_weighted_slope_error (w h a b d e : ℝ) (hd : d = e) :
    |w * (h⁻¹ * (a - b) - d)| = |h⁻¹ * (w * a - w * b) - w * e| := by
  rw [hd]
  congr 1
  ring

theorem circle_hasProjectiveCurveDerivAt_of_weighted_second_jets
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (c : ℝ → S.Space) (dc : S.Space)
    (J₁ J₂ : ℝ → ℕ → ℕ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hfirst : ∀ t, |t| < δ → ∀ m b θ,
      HasDerivAt (fun u => iteratedDeriv b (S.decode (c u) m) θ) (J₁ t m b θ) t)
    (hsecond : ∀ t, |t| < δ → ∀ m b θ,
      HasDerivAt (fun u => J₁ u m b θ) (J₂ t m b θ) t)
    (hvalue : ∀ m b θ, J₁ 0 m b θ = iteratedDeriv b (S.decode dc m) θ)
    (hbound : ∀ s, ∃ E : ℕ → ℝ≥0∞, ∃ B : ℝ,
      (∑' m, E m) < ⊤ ∧ 0 ≤ B ∧
      ∀ t, |t| < δ → ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) * |J₂ t m b θ| ≤
          B * Real.sqrt (E m).toReal) :
    HasProjectiveCurveDerivAt c dc 0 := by
  refine circle_hasProjectiveCurveDerivAt_of_energy_envelope hS hM hH c dc 0 ?_
  intro s
  let E : ℕ → ℝ≥0∞ := (hbound s).choose
  let B : ℝ := (hbound s).choose_spec.choose
  have hE : (∑' m, E m) < ⊤ := (hbound s).choose_spec.choose_spec.1
  have hB : 0 ≤ B := (hbound s).choose_spec.choose_spec.2.1
  have hb : ∀ t, |t| < δ → ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) * |J₂ t m b θ| ≤
        B * Real.sqrt (E m).toReal := (hbound s).choose_spec.choose_spec.2.2
  have hlim : Tendsto (fun h : ℝ => B * |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ha : Tendsto (fun h : ℝ => |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [abs_zero, mul_zero] using
      ha.const_mul B
  refine ⟨E, (fun h : ℝ => B * |h|), hE, hlim, ?_⟩
  have hsmall : {h : ℝ | |h| < δ} ∈ 𝓝 (0 : ℝ) := by
    simpa only [Metric.ball, Real.dist_eq, sub_zero] using Metric.ball_mem_nhds (0 : ℝ) hδ
  filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with h hh hne
  have hh' : |h| < δ := hh
  have hne' : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  refine ⟨mul_nonneg hB (abs_nonneg h), ?_⟩
  intro m b k horder θ
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  let L := circleAngularJetEvaluationLinear hS b m θ
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg (hM m) k) (Real.rpow_nonneg (hH m) _)
  have hjet : ∀ t, L (c t) = iteratedDeriv b (S.decode (c t) m) θ :=
    fun t => circleAngularJetEvaluationLinear_apply hS b m θ (c t)
  have hLdc : L dc = J₁ 0 m b θ :=
    (circleAngularJetEvaluationLinear_apply hS b m θ dc).trans (hvalue m b θ).symm
  have hfirst' (t : ℝ) (ht : |t| < δ) :
      HasDerivAt (fun u => w * L (c u)) (w * J₁ t m b θ) t := by
    simpa only [hjet] using (hfirst t ht m b θ).const_mul w
  have hsecond' (t : ℝ) (ht : |t| < δ) :
      HasDerivAt (fun u => w * J₁ u m b θ) (w * J₂ t m b θ) t :=
    (hsecond t ht m b θ).const_mul w
  have hweighted (t : ℝ) (ht : |t| < δ) :
      |w * J₂ t m b θ| ≤ B * Real.sqrt (E m).toReal := by
    rw [abs_mul, abs_of_nonneg hw]
    exact hb t ht m b k horder θ
  have hTaylor := abs_slope_sub_derivative_le_of_second_derivative_bound
    hδ (mul_nonneg hB (Real.sqrt_nonneg _)) hfirst' hsecond' hweighted hh' hne'
  simp only [zero_add]
  rw [← circleAngularJetEvaluationLinear_apply hS b m θ]
  change w * |L (h⁻¹ • (c h - c 0) - dc)| ≤ (B * |h|) * Real.sqrt (E m).toReal
  calc
    w * |L (h⁻¹ • (c h - c 0) - dc)| =
        |w * (h⁻¹ * (L (c h) - L (c 0)) - L dc)| := by
      simp only [map_sub, map_smul, RingHom.id_apply, smul_eq_mul, abs_mul, abs_of_nonneg hw]
    _ = |h⁻¹ * (w * L (c h) - w * L (c 0)) - w * J₁ 0 m b θ| :=
      abs_weighted_slope_error w h (L (c h)) (L (c 0)) (L dc) (J₁ 0 m b θ) hLdc
    _ ≤ (B * Real.sqrt (E m).toReal) * |h| := hTaylor
    _ = (B * |h|) * Real.sqrt (E m).toReal := by ring

end ContinuousFlexibility.Statements
