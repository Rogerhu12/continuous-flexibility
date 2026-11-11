import ContinuousFlexibility.Analysis.IntervalFluxEnergy
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Caccioppoli estimates from the conormal energy identity

The cutoff estimate costs one power of angular frequency. Its proof uses
only the actual first derivative and the energy identity established from
the flux primitive; no classical second derivative is assumed.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

private theorem cutoff_caccioppoli_pointwise {w χ χ' u d f c K L j : ℝ}
    (hw₀ : 0 ≤ w) (hwK : w ≤ K) (hK : 0 ≤ K)
    (hχ : |χ| ≤ 1) (hχ' : |χ'| ≤ L) (hc : |c| ≤ K) :
    -((f + j ^ 2 * c * u) * (χ ^ 2 * u)) - 2 * (w * χ * χ' * u * d) ≤
      (1 / 2) * (w * χ ^ 2 * d ^ 2) + (1 / 2) * f ^ 2 +
        (1 / 2 + j ^ 2 * K + 2 * K * L ^ 2) * u ^ 2 := by
  have hχ₂ : χ ^ 2 ≤ 1 := by
    have h₁ := (abs_le.mp hχ).1
    have h₂ := (abs_le.mp hχ).2
    nlinarith [mul_nonneg (show 0 ≤ 1 - χ by linarith)
      (show 0 ≤ 1 + χ by linarith)]
  have hχ'₂ : χ' ^ 2 ≤ L ^ 2 := by
    have h₁ := (abs_le.mp hχ').1
    have h₂ := (abs_le.mp hχ').2
    nlinarith [mul_nonneg (show 0 ≤ L - χ' by linarith)
      (show 0 ≤ L + χ' by linarith)]
  have hsource₀ :
      -(f * (χ ^ 2 * u)) ≤ (1 / 2) * χ ^ 2 * f ^ 2 + (1 / 2) * χ ^ 2 * u ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg χ) (sq_nonneg (f + u))]
  have hsource : -(f * (χ ^ 2 * u)) ≤ (1 / 2) * f ^ 2 + (1 / 2) * u ^ 2 := by
    have hf := mul_le_mul_of_nonneg_right hχ₂ (sq_nonneg f)
    have hu := mul_le_mul_of_nonneg_right hχ₂ (sq_nonneg u)
    nlinarith
  have hnegc : -c ≤ K := by linarith [(abs_le.mp hc).1]
  have hpot₀ : -c * χ ^ 2 ≤ K := by
    calc
      -c * χ ^ 2 ≤ K * χ ^ 2 := mul_le_mul_of_nonneg_right hnegc (sq_nonneg χ)
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hχ₂ hK
      _ = K := mul_one K
  have hpot := mul_le_mul_of_nonneg_left hpot₀ (mul_nonneg (sq_nonneg j) (sq_nonneg u))
  have hcross₀ : -(2 * (w * χ * χ' * u * d)) ≤
      (1 / 2) * (w * χ ^ 2 * d ^ 2) + 2 * w * χ' ^ 2 * u ^ 2 := by
    nlinarith [mul_nonneg hw₀ (sq_nonneg (χ * d + 2 * χ' * u))]
  have hweight : w * χ' ^ 2 ≤ K * L ^ 2 :=
    mul_le_mul hwK hχ'₂ (sq_nonneg χ') hK
  have hcross := mul_le_mul_of_nonneg_right hweight (sq_nonneg u)
  nlinarith

private theorem cutoff_caccioppoli_absorb {A D Φ U K L j : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hΦ : 0 ≤ Φ) (hU : 0 ≤ U)
    (hA : A ≤ Φ + (1 + 2 * j ^ 2 * K + 4 * K * L ^ 2) * U)
    (hD : D ≤ K * A) :
    D ≤ 7 * K ^ 2 * L ^ 2 * (Φ + (1 + j ^ 2) * U) := by
  have hK₀ : 0 ≤ K := le_trans zero_le_one hK
  have hK₂ : K ≤ K ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hK hK₀]
  have hL₂ : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hKK : K ^ 2 ≤ K ^ 2 * L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hL₂ (sq_nonneg K)
    nlinarith
  have hKL : K ≤ K ^ 2 * L ^ 2 := hK₂.trans hKK
  have hnonneg : 0 ≤ K ^ 2 * L ^ 2 := mul_nonneg (sq_nonneg K) (sq_nonneg L)
  have hcoef : K + 2 * j ^ 2 * K ^ 2 + 4 * K ^ 2 * L ^ 2 ≤
      7 * K ^ 2 * L ^ 2 * (1 + j ^ 2) := by
    have hj := mul_le_mul_of_nonneg_left hKK (sq_nonneg j)
    have hj₀ := mul_nonneg (sq_nonneg j) hnonneg
    nlinarith
  have hΦcoef : K ≤ 7 * K ^ 2 * L ^ 2 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hA hK₀
  have h₂ := mul_le_mul_of_nonneg_right hcoef hU
  have h₃ := mul_le_mul_of_nonneg_right hΦcoef hΦ
  nlinarith

/-- The integral Caccioppoli inequality for any measure, once the conormal
energy identity and the integrability of its actual terms are available. -/
theorem cutoff_caccioppoli_of_energy_identity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {w χ χ' u d f c : α → ℝ} {K L j : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hcoef : ∀ᵐ x ∂μ, 1 / K ≤ w x ∧ w x ≤ K ∧ |χ x| ≤ 1 ∧
      |χ' x| ≤ L ∧ |c x| ≤ K)
    (hEi : Integrable (fun x => w x * χ x ^ 2 * d x ^ 2) μ)
    (hDi : Integrable (fun x => χ x ^ 2 * d x ^ 2) μ)
    (hXi : Integrable (fun x => w x * χ x * χ' x * u x * d x) μ)
    (hHi : Integrable (fun x => (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) μ)
    (hfi : Integrable (fun x => f x ^ 2) μ)
    (hui : Integrable (fun x => u x ^ 2) μ)
    (heq : (∫ x, w x * χ x ^ 2 * d x ^ 2 ∂μ) =
      -(∫ x, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x) ∂μ) -
        2 * (∫ x, w x * χ x * χ' x * u x * d x ∂μ)) :
    (∫ x, χ x ^ 2 * d x ^ 2 ∂μ) ≤
      7 * K ^ 2 * L ^ 2 * ((∫ x, f x ^ 2 ∂μ) +
        (1 + j ^ 2) * (∫ x, u x ^ 2 ∂μ)) := by
  have hK₀ : 0 ≤ K := le_trans zero_le_one hK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let S : ℝ := 1 / 2 + j ^ 2 * K + 2 * K * L ^ 2
  have hp : ∀ᵐ x ∂μ,
      -((f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) -
          2 * (w x * χ x * χ' x * u x * d x) ≤
        (1 / 2) * (w x * χ x ^ 2 * d x ^ 2) + (1 / 2) * f x ^ 2 + S * u x ^ 2 := by
    filter_upwards [hcoef] with x hx
    exact cutoff_caccioppoli_pointwise
      ((one_div_nonneg.mpr hK₀).trans hx.1) hx.2.1 hK₀
      hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
  have hmono := integral_mono_ae (hHi.neg.sub (hXi.const_mul 2))
    (((hEi.const_mul (1 / 2)).add (hfi.const_mul (1 / 2))).add (hui.const_mul S)) hp
  rw [integral_sub' hHi.neg (hXi.const_mul 2), integral_neg',
    integral_add' ((hEi.const_mul (1 / 2)).add (hfi.const_mul (1 / 2))) (hui.const_mul S),
    integral_add' (hEi.const_mul (1 / 2)) (hfi.const_mul (1 / 2))] at hmono
  simp only [integral_const_mul] at hmono
  rw [← heq] at hmono
  have hA : (∫ x, w x * χ x ^ 2 * d x ^ 2 ∂μ) ≤
      (∫ x, f x ^ 2 ∂μ) +
        (1 + 2 * j ^ 2 * K + 4 * K * L ^ 2) * (∫ x, u x ^ 2 ∂μ) := by
    dsimp only [S] at hmono
    nlinarith
  have hpD : ∀ᵐ x ∂μ, χ x ^ 2 * d x ^ 2 ≤ K * (w x * χ x ^ 2 * d x ^ 2) := by
    filter_upwards [hcoef] with x hx
    have hKw : 1 ≤ w x * K := (div_le_iff₀ hKpos).mp hx.1
    have hh := mul_le_mul_of_nonneg_right hKw (mul_nonneg (sq_nonneg (χ x)) (sq_nonneg (d x)))
    nlinarith
  have hD := integral_mono_ae hDi (hEi.const_mul K) hpD
  rw [integral_const_mul] at hD
  exact cutoff_caccioppoli_absorb hK hL
    (integral_nonneg fun x => sq_nonneg (f x))
    (integral_nonneg fun x => sq_nonneg (u x)) hA hD

/-- The actual C¹ cutoff Caccioppoli estimate. The forcing is merely L²,
and the differential equation is used through its already established
conormal primitive. -/
theorem interval_cutoff_caccioppoli {a b : ℝ} (hab : a < b)
    {u w f c χ : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (hw : ContinuousOn w (Ioo a b)) (hc : ContinuousOn c (Ioo a b))
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hu₂ : MemLp u 2 (volume.restrict (Ioo a b)))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo a b) {K L j : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hcoef : ∀ x ∈ Ioo a b, 1 / K ≤ w x ∧ w x ≤ K ∧ |χ x| ≤ 1 ∧
      |deriv χ x| ≤ L ∧ |c x| ≤ K)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b) (q : ℝ)
    (hflux : ∀ x ∈ Ioo a b, w x * deriv u x =
      intervalLocalPrimitive (fun y => f y + j ^ 2 * c y * u y) x₀ x + q) :
    (∫ x in Ioo a b, χ x ^ 2 * deriv u x ^ 2) ≤
      7 * K ^ 2 * L ^ 2 * ((∫ x in Ioo a b, f x ^ 2) +
        (1 + j ^ 2) * (∫ x in Ioo a b, u x ^ 2)) := by
  letI : IsFiniteMeasure (volume.restrict (Ioo a b) : Measure ℝ) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top⟩
  have hfi : IntegrableOn f (Ioo a b) volume := hf.integrable (by norm_num)
  have hloc : LocallyIntegrableOn
      (fun x => f x + j ^ 2 * c x * u x) (Ioo a b) volume :=
    hfi.locallyIntegrableOn.add
      (((continuousOn_const.mul hc).mul hu.continuousOn).locallyIntegrableOn measurableSet_Ioo)
  have hud : ContinuousOn (deriv u) (Ioo a b) :=
    continuousOn_deriv_of_contDiffOn_one_Ioo hu
  have hχd : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hEcore : ContinuousOn (fun x => w x * χ x * deriv u x ^ 2) (Ioo a b) :=
    (hw.mul hχ.continuous.continuousOn).mul (hud.pow 2)
  have hEi : Integrable (fun x => w x * χ x ^ 2 * deriv u x ^ 2) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hEcore.locallyIntegrableOn measurableSet_Ioo) hχ.continuous hχc hχs
    exact hi.congr (Eventually.of_forall fun x => by ring)
  have hDcore : ContinuousOn (fun x => χ x * deriv u x ^ 2) (Ioo a b) :=
    hχ.continuous.continuousOn.mul (hud.pow 2)
  have hDi : Integrable (fun x => χ x ^ 2 * deriv u x ^ 2) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hDcore.locallyIntegrableOn measurableSet_Ioo) hχ.continuous hχc hχs
    exact hi.congr (Eventually.of_forall fun x => by ring)
  have hXcore : ContinuousOn
      (fun x => w x * deriv χ x * u x * deriv u x) (Ioo a b) :=
    ((hw.mul hχd.continuousOn).mul hu.continuousOn).mul hud
  have hXi : Integrable (fun x => w x * χ x * deriv χ x * u x * deriv u x) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hXcore.locallyIntegrableOn measurableSet_Ioo) hχ.continuous hχc hχs
    exact hi.congr (Eventually.of_forall fun x => by ring)
  obtain ⟨hψ, hψc, hψs⟩ := interval_cutoff_square_mul_test hu hχ hχc hχs
  have hHi : Integrable
      (fun x => (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) :=
    integrable_mul_test_of_locallyIntegrableOn_Ioo hloc hψ.continuous hψc hψs
  have hEeq : (∫ x in Ioo a b, w x * χ x ^ 2 * deriv u x ^ 2) =
      ∫ x, w x * χ x ^ 2 * deriv u x ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχs hh))
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
  have hXeq : (∫ x in Ioo a b, w x * χ x * deriv χ x * u x * deriv u x) =
      ∫ x, w x * χ x * deriv χ x * u x * deriv u x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχs hh))
    simp only [hz, mul_zero, zero_mul]
  have hHeq : (∫ x in Ioo a b, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) =
      ∫ x, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχs hh))
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
  have heq : (∫ x in Ioo a b, w x * χ x ^ 2 * deriv u x ^ 2) =
      -(∫ x in Ioo a b, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) -
        2 * (∫ x in Ioo a b, w x * χ x * deriv χ x * u x * deriv u x) := by
    rw [hEeq, hHeq, hXeq]
    exact interval_cutoff_energy_identity hab hu hw hloc hχ hχc hχs x₀ hx₀ q hflux
  have hf₂ : Integrable (fun x => f x ^ 2) (volume.restrict (Ioo a b)) := hf.integrable_sq
  have hu₂' : Integrable (fun x => u x ^ 2) (volume.restrict (Ioo a b)) := hu₂.integrable_sq
  exact cutoff_caccioppoli_of_energy_identity (volume.restrict (Ioo a b)) hK hL
    ((ae_restrict_mem measurableSet_Ioo).mono fun x hx => hcoef x hx)
    hEi.integrableOn hDi.integrableOn hXi.integrableOn hHi.integrableOn hf₂ hu₂' heq


end

end ContinuousFlexibility.Analysis
