module

public import ContinuousFlexibility.Radial.MorseMaximalDomain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Right-tail Weyl sequences for the Morse potential

A translated cutoff with width `n + 1` is multiplied by sine or cosine at
the frequency of the target energy. Choosing the larger of the two `L²`
norms gives a uniform normalization estimate, including at zero frequency.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private def weylWidth (n : ℕ) : ℝ := (n : ℝ) + 1

private theorem weylWidth_pos (n : ℕ) : 0 < weylWidth n := by
  unfold weylWidth
  positivity

private theorem weylWidth_tendsto : Tendsto weylWidth atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

private def weylEnvelope (n : ℕ) (x : ℝ) : ℝ :=
  scaledOscillatorCutoff n (x - 3 * weylWidth n)

private theorem weylEnvelope_smooth (n : ℕ) : ContDiff ℝ ∞ (weylEnvelope n) :=
  (contDiff_scaledOscillatorCutoff n).comp (contDiff_id.sub contDiff_const)

private theorem weylEnvelope_one (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (2 * weylWidth n) (4 * weylWidth n)) : weylEnvelope n x = 1 := by
  change oscillatorCutoff ((x - 3 * weylWidth n) / weylWidth n) = 1
  apply oscillatorCutoff_eq_one
  rw [abs_div, abs_of_pos (weylWidth_pos n), div_le_iff₀ (weylWidth_pos n), one_mul]
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem weylEnvelope_zero (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (weylWidth n) (5 * weylWidth n)) : weylEnvelope n x = 0 := by
  change oscillatorCutoff ((x - 3 * weylWidth n) / weylWidth n) = 0
  apply oscillatorCutoff_eq_zero
  rw [abs_div, abs_of_pos (weylWidth_pos n), le_div_iff₀ (weylWidth_pos n)]
  by_contra! h
  obtain ⟨hl, hr⟩ := abs_lt.mp h
  exact hx ⟨by linarith, by linarith⟩

private theorem weylEnvelope_tsupport (n : ℕ) :
    tsupport (weylEnvelope n) ⊆ Icc (weylWidth n) (5 * weylWidth n) := by
  change closure (Function.support (weylEnvelope n)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (weylEnvelope_zero n h)

private theorem weylEnvelope_deriv_zero (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (weylWidth n) (5 * weylWidth n)) :
    deriv (weylEnvelope n) x = 0 ∧ deriv (deriv (weylEnvelope n)) x = 0 :=
  ⟨deriv_of_notMem_tsupport (fun h => hx (weylEnvelope_tsupport n h)),
    deriv_of_notMem_tsupport (fun h => hx (weylEnvelope_tsupport n (tsupport_deriv_subset h)))⟩

private theorem weylEnvelope_compact (n : ℕ) : HasCompactSupport (weylEnvelope n) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => weylEnvelope_zero n hx)

private theorem weylEnvelope_abs (n : ℕ) (x : ℝ) : |weylEnvelope n x| ≤ 1 :=
  morseScaledCutoff_abs_le_one n (x - 3 * weylWidth n)

private theorem weylEnvelope_deriv_bounds (n : ℕ) (x : ℝ) :
    |deriv (weylEnvelope n) x| ≤ morseCutoffDerivativeConstant / weylWidth n ∧
    |deriv (deriv (weylEnvelope n)) x| ≤
      morseCutoffDerivativeConstant / weylWidth n ^ 2 := by
  have h₁ (y : ℝ) : deriv (weylEnvelope n) y =
      deriv (scaledOscillatorCutoff n) (y - 3 * weylWidth n) := by
    unfold weylEnvelope
    rw [deriv_comp_sub_const]
  have h₂ : deriv (deriv (weylEnvelope n)) x =
      deriv (deriv (scaledOscillatorCutoff n)) (x - 3 * weylWidth n) := by
    rw [funext h₁, deriv_comp_sub_const]
  rw [h₁, h₂]
  have hc := Classical.choose_spec oscillatorCutoff_derivative_bounds
  exact scaledOscillatorCutoff_derivative_bounds hc.2.1 hc.2.2 n _

private def weylCarrier (k : ℝ) : Bool → ℝ → ℝ
  | false => fun x => cos (k * x)
  | true => fun x => sin (k * x)

private theorem weylCarrier_smooth (k : ℝ) (s : Bool) : ContDiff ℝ ∞ (weylCarrier k s) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ => k * x) := contDiff_const.mul contDiff_id
  cases s
  · exact Real.contDiff_cos.comp h
  · exact Real.contDiff_sin.comp h

private theorem weylCarrier_abs (k : ℝ) (s : Bool) (x : ℝ) : |weylCarrier k s x| ≤ 1 := by
  cases s
  · exact abs_cos_le_one _
  · exact abs_sin_le_one _

private theorem weylCarrier_deriv_cos (k x : ℝ) :
    deriv (weylCarrier k false) x = -k * weylCarrier k true x := by
  have h := ((hasDerivAt_id x).const_mul k).cos.deriv
  simp only [id_eq, mul_one] at h
  change deriv (fun y : ℝ => cos (k * y)) x = -k * sin (k * x)
  rw [h]
  ring

private theorem weylCarrier_deriv_sin (k x : ℝ) :
    deriv (weylCarrier k true) x = k * weylCarrier k false x := by
  have h := ((hasDerivAt_id x).const_mul k).sin.deriv
  change deriv (fun y : ℝ => sin (k * y)) x = k * cos (k * x)
  simpa only [id_eq, mul_one, mul_comm] using h

private theorem weylCarrier_deriv_abs (k : ℝ) (s : Bool) (x : ℝ) :
    |deriv (weylCarrier k s) x| ≤ |k| := by
  cases s
  · rw [weylCarrier_deriv_cos, abs_mul, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg k) (weylCarrier_abs k true x)
  · rw [weylCarrier_deriv_sin, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg k) (weylCarrier_abs k false x)

private theorem weylCarrier_second (k : ℝ) (s : Bool) (x : ℝ) :
    deriv (deriv (weylCarrier k s)) x = -k ^ 2 * weylCarrier k s x := by
  cases s
  · rw [funext (weylCarrier_deriv_cos k)]
    have hd := ((weylCarrier_smooth k true).differentiable (by simp) x).hasDerivAt
    rw [(hd.const_mul (-k)).deriv, weylCarrier_deriv_sin]
    ring
  · rw [funext (weylCarrier_deriv_sin k)]
    have hd := ((weylCarrier_smooth k false).differentiable (by simp) x).hasDerivAt
    rw [(hd.const_mul k).deriv, weylCarrier_deriv_cos]
    ring

private def weylPacket (k : ℝ) (s : Bool) (n : ℕ) (x : ℝ) : ℝ :=
  weylEnvelope n x * weylCarrier k s x

private theorem weylPacket_smooth (k : ℝ) (s : Bool) (n : ℕ) :
    ContDiff ℝ ∞ (weylPacket k s n) :=
  (weylEnvelope_smooth n).mul (weylCarrier_smooth k s)

private theorem weylPacket_compact (k : ℝ) (s : Bool) (n : ℕ) :
    HasCompactSupport (weylPacket k s n) := (weylEnvelope_compact n).mul_right

private theorem weylPacket_second (k : ℝ) (s : Bool) (n : ℕ) (x : ℝ) :
    deriv (deriv (weylPacket k s n)) x =
      deriv (deriv (weylEnvelope n)) x * weylCarrier k s x +
        2 * deriv (weylEnvelope n) x * deriv (weylCarrier k s) x -
        k ^ 2 * weylPacket k s n x := by
  have hχ := weylEnvelope_smooth n
  have hw := weylCarrier_smooth k s
  have hχ' := (contDiff_infty_iff_deriv.mp hχ).2
  have hw' := (contDiff_infty_iff_deriv.mp hw).2
  have hd (y : ℝ) : deriv (weylPacket k s n) y =
      deriv (weylEnvelope n) y * weylCarrier k s y +
        weylEnvelope n y * deriv (weylCarrier k s) y :=
    (((hχ.differentiable (by simp) y).hasDerivAt).mul
      ((hw.differentiable (by simp) y).hasDerivAt)).deriv
  have hdd : HasDerivAt
      (fun y => deriv (weylEnvelope n) y * weylCarrier k s y +
        weylEnvelope n y * deriv (weylCarrier k s) y)
      ((deriv (deriv (weylEnvelope n)) x * weylCarrier k s x +
        deriv (weylEnvelope n) x * deriv (weylCarrier k s) x) +
        (deriv (weylEnvelope n) x * deriv (weylCarrier k s) x +
          weylEnvelope n x * deriv (deriv (weylCarrier k s)) x)) x :=
    (((hχ'.differentiable (by simp) x).hasDerivAt).mul
      ((hw.differentiable (by simp) x).hasDerivAt)).add
      (((hχ.differentiable (by simp) x).hasDerivAt).mul
        ((hw'.differentiable (by simp) x).hasDerivAt))
  rw [funext hd, hdd.deriv, weylCarrier_second]
  unfold weylPacket
  ring

private def weylPacketL2 (k : ℝ) (s : Bool) (n : ℕ) : MorseL2 :=
  (compactSmooth_morseEnergyDomain (weylPacket_smooth k s n)
    (weylPacket_compact k s n)).2.1.toLp (weylPacket k s n)

private theorem weylPacketL2_ae (k : ℝ) (s : Bool) (n : ℕ) :
    (weylPacketL2 k s n : ℝ → ℝ) =ᵐ[volume] weylPacket k s n :=
  MemLp.coeFn_toLp _

private theorem weylL2_norm_sq (u : MorseL2) {f : ℝ → ℝ}
    (h : (u : ℝ → ℝ) =ᵐ[volume] f) : ‖u‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]

private theorem weylEnvelope_integral_lower (n : ℕ) :
    2 * weylWidth n ≤ ∫ x : ℝ, weylEnvelope n x ^ 2 := by
  let I := Icc (2 * weylWidth n) (4 * weylWidth n)
  have hI : MeasurableSet I := measurableSet_Icc
  have hone : Integrable (I.indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrableOn_const (μ := volume) (C := (1 : ℝ)) (s := I)
      (isCompact_Icc.measure_ne_top)).integrable_indicator hI
  have hχ := (weylEnvelope_smooth n).continuous.memLp_of_hasCompactSupport
    (μ := volume) (p := 2) (weylEnvelope_compact n)
  have hχ₂ := (oscillator_memLp_two_iff_integrable_sq hχ.aestronglyMeasurable).mp hχ
  have h := integral_mono hone hχ₂ (fun x => by
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx, weylEnvelope_one n hx, one_pow]
    · rw [indicator_of_notMem hx]
      exact sq_nonneg _)
  have hlen : 2 * weylWidth n ≤ 4 * weylWidth n := by linarith [weylWidth_pos n]
  rw [integral_indicator_const _ hI] at h
  change (volume : Measure ℝ).real (Icc (2 * weylWidth n) (4 * weylWidth n)) •
    (1 : ℝ) ≤ _ at h
  rw [Real.volume_real_Icc_of_le hlen, smul_eq_mul, mul_one] at h
  linarith

private theorem weylPacket_norm_sq_sum (k : ℝ) (n : ℕ) :
    ‖weylPacketL2 k false n‖ ^ 2 + ‖weylPacketL2 k true n‖ ^ 2 =
      ∫ x : ℝ, weylEnvelope n x ^ 2 := by
  have hi (s : Bool) : Integrable (fun x : ℝ => weylPacket k s n x ^ 2) volume := by
    have hp := (compactSmooth_morseEnergyDomain (weylPacket_smooth k s n)
      (weylPacket_compact k s n)).2.1
    exact (oscillator_memLp_two_iff_integrable_sq hp.aestronglyMeasurable).mp hp
  rw [weylL2_norm_sq _ (weylPacketL2_ae k false n),
    weylL2_norm_sq _ (weylPacketL2_ae k true n), ← integral_add (hi false) (hi true)]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x => ?_)
  change (weylEnvelope n x * cos (k * x)) ^ 2 + (weylEnvelope n x * sin (k * x)) ^ 2 = _
  calc
    _ = weylEnvelope n x ^ 2 * (cos (k * x) ^ 2 + sin (k * x) ^ 2) := by ring
    _ = _ := by rw [cos_sq_add_sin_sq, mul_one]

private def weylPhase (k : ℝ) (n : ℕ) : Bool :=
  if ‖weylPacketL2 k false n‖ ^ 2 ≤ ‖weylPacketL2 k true n‖ ^ 2 then true else false

private theorem weylPacket_norm_sq_lower (k : ℝ) (n : ℕ) :
    weylWidth n ≤ ‖weylPacketL2 k (weylPhase k n) n‖ ^ 2 := by
  have h := weylEnvelope_integral_lower n
  rw [← weylPacket_norm_sq_sum k n] at h
  unfold weylPhase
  split_ifs with hphase
  · linarith
  · linarith [le_of_not_ge hphase]

private def weylPacketImage (j A B k : ℝ) (s : Bool) (n : ℕ) : ℝ → ℝ :=
  morseExpression ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) (weylPacket k s n)

private def weylPacketImageL2 (j A B k : ℝ) (s : Bool) (n : ℕ) : MorseL2 :=
  (morseCompactImage_memLp (weylPacket_smooth k s n) (weylPacket_compact k s n)
    ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B)).toLp (weylPacketImage j A B k s n)

private theorem weylPacket_pair (j A B k : ℝ) (s : Bool) (n : ℕ) :
    (weylPacketL2 k s n, weylPacketImageL2 j A B k s n) ∈
      morseAssociatedGraph ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) :=
  morseCompact_pair_mem_graph (weylPacket_smooth k s n) (weylPacket_compact k s n) _ _ _

private def weylError (j A B k : ℝ) (s : Bool) (n : ℕ) (x : ℝ) : ℝ :=
  -(deriv (deriv (weylEnvelope n)) x * weylCarrier k s x +
      2 * deriv (weylEnvelope n) x * deriv (weylCarrier k s) x) +
    (Statements.morsePotential j A B x - j ^ 2 * B) * weylPacket k s n x

private theorem weylResidual_ae {j A B E k : ℝ} (hA : 0 ≤ A) (hk : k ^ 2 = E - j ^ 2 * B)
    (s : Bool) (n : ℕ) :
    ((weylPacketImageL2 j A B k s n - E • weylPacketL2 k s n : MorseL2) : ℝ → ℝ)
      =ᵐ[volume] weylError j A B k s n := by
  have hi : (weylPacketImageL2 j A B k s n : ℝ → ℝ) =ᵐ[volume] weylPacketImage j A B k s n :=
    MemLp.coeFn_toLp _
  filter_upwards [Lp.coeFn_sub (weylPacketImageL2 j A B k s n) (E • weylPacketL2 k s n),
    Lp.coeFn_smul E (weylPacketL2 k s n), hi, weylPacketL2_ae k s n] with x hsub hsmul hx hpacket
  rw [hsub]
  simp only [Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hx, hpacket]
  rw [weylPacketImage, ← morseSchrodingerExpression_eq hA j B]
  unfold morseSchrodingerExpression
  rw [weylPacket_second, hk]
  unfold weylError Statements.morsePotential
  ring

private theorem weylPotential_bound (j A B : ℝ) (n : ℕ) {x : ℝ} (hx : weylWidth n ≤ x) :
    |Statements.morsePotential j A B x - j ^ 2 * B| ≤
      |j ^ 2 * A| * exp (-weylWidth n) := by
  have hx₀ := (weylWidth_pos n).le.trans hx
  have ht : exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx₀)
  have ht₀ := (exp_pos (-x)).le
  have hs : exp (-x) ^ 2 ≤ exp (-x) := by nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr ht)]
  rw [morsePotential_quadratic, add_sub_cancel_right, abs_mul,
    abs_of_nonpos (sub_nonpos.mpr hs)]
  refine mul_le_mul_of_nonneg_left (?_ : _ ≤ _) (abs_nonneg _)
  exact (by linarith [sq_nonneg (exp (-x))] : -(exp (-x) ^ 2 - exp (-x)) ≤ exp (-x)).trans
    (exp_le_exp.mpr (neg_le_neg hx))

private def weylErrorBound (j A k : ℝ) (n : ℕ) : ℝ :=
  morseCutoffDerivativeConstant / weylWidth n ^ 2 +
    2 * (morseCutoffDerivativeConstant / weylWidth n) * |k| + |j ^ 2 * A| * exp (-weylWidth n)

private theorem weylErrorBound_nonneg (j A k : ℝ) (n : ℕ) : 0 ≤ weylErrorBound j A k n := by
  unfold weylErrorBound
  have hC := morseCutoffDerivativeConstant_nonneg
  have hL := weylWidth_pos n
  positivity

private theorem weylError_zero (j A B k : ℝ) (s : Bool) (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (weylWidth n) (5 * weylWidth n)) : weylError j A B k s n x = 0 := by
  obtain ⟨hd, hdd⟩ := weylEnvelope_deriv_zero n hx
  simp [weylError, weylPacket, weylEnvelope_zero n hx, hd, hdd]

private theorem weylError_abs (j A B k : ℝ) (s : Bool) (n : ℕ) {x : ℝ} (hx : weylWidth n ≤ x) :
    |weylError j A B k s n x| ≤ weylErrorBound j A k n := by
  obtain ⟨h₁, h₂⟩ := weylEnvelope_deriv_bounds n x
  have h₁' : |2 * deriv (weylEnvelope n) x * deriv (weylCarrier k s) x| ≤
      2 * (morseCutoffDerivativeConstant / weylWidth n) * |k| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by norm_num)) (weylCarrier_deriv_abs k s x)
      (abs_nonneg _) (mul_nonneg (by norm_num) (div_nonneg morseCutoffDerivativeConstant_nonneg
        (weylWidth_pos n).le))
  have h₂' : |deriv (deriv (weylEnvelope n)) x * weylCarrier k s x| ≤
      morseCutoffDerivativeConstant / weylWidth n ^ 2 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (weylCarrier_abs k s x)).trans h₂
  have hpacket : |weylPacket k s n x| ≤ 1 := by
    rw [weylPacket, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (weylCarrier_abs k s x)).trans
      (weylEnvelope_abs n x)
  have htail : |(Statements.morsePotential j A B x - j ^ 2 * B) * weylPacket k s n x| ≤
      |j ^ 2 * A| * exp (-weylWidth n) := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hpacket).trans (weylPotential_bound j A B n hx)
  unfold weylError weylErrorBound
  refine (abs_add_le _ _).trans (add_le_add ?_ htail)
  rw [abs_neg]
  exact (abs_add_le _ _).trans (add_le_add h₂' h₁')

private theorem weylErrorBound_tendsto (j A k : ℝ) :
    Tendsto (weylErrorBound j A k) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (weylWidth n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp weylWidth_tendsto
  have h₁ : Tendsto (fun n => morseCutoffDerivativeConstant / weylWidth n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul morseCutoffDerivativeConstant
  have h₂ : Tendsto (fun n => morseCutoffDerivativeConstant / weylWidth n ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (hi.pow 2).const_mul morseCutoffDerivativeConstant
  have ht : Tendsto (fun n => exp (-weylWidth n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp weylWidth_tendsto)
  unfold weylErrorBound
  simpa only [mul_zero, zero_mul, add_zero] using
    (h₂.add ((h₁.const_mul 2).mul_const |k|)).add (ht.const_mul |j ^ 2 * A|)

private theorem weylResidual_norm_sq {j A B E k : ℝ} (hA : 0 ≤ A) (hk : k ^ 2 = E - j ^ 2 * B)
    (s : Bool) (n : ℕ) : ‖weylPacketImageL2 j A B k s n - E • weylPacketL2 k s n‖ ^ 2 ≤
      4 * weylWidth n * weylErrorBound j A k n ^ 2 := by
  let r := weylPacketImageL2 j A B k s n - E • weylPacketL2 k s n
  let I := Icc (weylWidth n) (5 * weylWidth n)
  let ε := weylErrorBound j A k n
  have hr := weylResidual_ae hA hk s n
  change (r : ℝ → ℝ) =ᵐ[volume] weylError j A B k s n at hr
  have hi : Integrable (fun x : ℝ => weylError j A B k s n x ^ 2) volume := by
    apply ((Lp.memLp r).integrable_mul (Lp.memLp r)).congr
    filter_upwards [hr] with x hx
    simp only [Pi.mul_apply, hx, pow_two]
  have hI : MeasurableSet I := measurableSet_Icc
  have hbound : Integrable (I.indicator (fun _ : ℝ => ε ^ 2)) volume :=
    (integrableOn_const (μ := volume) (C := ε ^ 2) (s := I)
      (isCompact_Icc.measure_ne_top)).integrable_indicator hI
  change ‖r‖ ^ 2 ≤ 4 * weylWidth n * ε ^ 2
  rw [weylL2_norm_sq r hr]
  calc
    _ ≤ ∫ x : ℝ, I.indicator (fun _ : ℝ => ε ^ 2) x := by
      refine integral_mono hi hbound (fun x => ?_)
      by_cases hx : x ∈ I
      · rw [indicator_of_mem hx, ← sq_abs (weylError j A B k s n x)]
        exact (sq_le_sq₀ (abs_nonneg _) (weylErrorBound_nonneg j A k n)).2
          (weylError_abs j A B k s n hx.1)
      · rw [indicator_of_notMem hx, weylError_zero j A B k s n hx]
        norm_num
    _ = _ := by
      have hlen : weylWidth n ≤ 5 * weylWidth n := by linarith [weylWidth_pos n]
      rw [integral_indicator_const _ hI]
      change (volume : Measure ℝ).real (Icc (weylWidth n) (5 * weylWidth n)) • ε ^ 2 = _
      rw [Real.volume_real_Icc_of_le hlen, smul_eq_mul]
      ring

private def weylTail (n : ℕ) (h : MorseL2) : MorseL2 :=
  ((Lp.memLp h).indicator measurableSet_Ici).toLp
    ((Ici (weylWidth n)).indicator (h : ℝ → ℝ))

private theorem weylTail_ae (n : ℕ) (h : MorseL2) :
    (weylTail n h : ℝ → ℝ) =ᵐ[volume] (Ici (weylWidth n)).indicator (h : ℝ → ℝ) :=
  MemLp.coeFn_toLp _

private theorem weylTail_tendsto (h : MorseL2) : Tendsto (fun n => weylTail n h) atTop (𝓝 0) := by
  let F (n : ℕ) : ℝ → ℝ := (Ici (weylWidth n)).indicator (h : ℝ → ℝ)
  have hF (n : ℕ) : MemLp (F n) 2 volume := (Lp.memLp h).indicator measurableSet_Ici
  have hzero : MemLp (fun _ : ℝ => (0 : ℝ)) 2 volume := MemLp.zero'
  have hbound (n : ℕ) (x : ℝ) : |F n x - 0| ≤ |h x| := by
    change |(Ici (weylWidth n)).indicator (h : ℝ → ℝ) x - 0| ≤ |h x|
    by_cases hx : x ∈ Ici (weylWidth n)
    · simp [indicator_of_mem hx]
    · simpa only [indicator_of_notMem hx, sub_zero, abs_zero] using abs_nonneg (h x)
  have hlim (x : ℝ) : Tendsto (fun n => F n x) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [weylWidth_tendsto.eventually (eventually_ge_atTop (x + 1))] with n hn
    have hx : x ∉ Ici (weylWidth n) := fun hx => by
      have hx' : weylWidth n ≤ x := hx
      linarith
    change 0 = (Ici (weylWidth n)).indicator (h : ℝ → ℝ) x
    rw [indicator_of_notMem hx]
  have hl := oscillator_tendsto_toLp_of_dominated hF hzero (Lp.memLp h) hbound hlim
  have hz : hzero.toLp (fun _ : ℝ => (0 : ℝ)) = (0 : MorseL2) := by
    change (MemLp.zero' : MemLp (0 : ℝ → ℝ) 2 volume).toLp 0 = 0
    exact MemLp.toLp_zero _
  rw [hz] at hl
  exact hl

private theorem weylWeak_of_right_support (u : ℕ → MorseL2) (hu : ∀ n, ‖u n‖ = 1)
    (hzero : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), x < weylWidth n → u n x = 0) (h : MorseL2) :
    Tendsto (fun n => ⟪u n, h⟫_ℝ) atTop (𝓝 0) := by
  have hpair (n : ℕ) : ⟪u n, h⟫_ℝ = ⟪u n, weylTail n h⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hzero n, weylTail_ae n h] with x hz ht
    by_cases hx : x ∈ Ici (weylWidth n)
    · rw [ht, indicator_of_mem hx]
    · have hx' : x < weylWidth n := lt_of_not_ge hx
      simp only [hz hx', inner_zero_left]
  have hnorm : Tendsto (fun n => ‖weylTail n h‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (weylTail_tendsto h).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hnorm
  rw [hpair n, ← one_mul ‖weylTail n h‖, ← hu n]
  exact norm_inner_le_norm (𝕜 := ℝ) (u n) (weylTail n h)

/-- Every energy at or above the right asymptotic potential has a unit Weyl
sequence of genuine Morse differential graph pairs. -/
theorem morseEssentialWeylValue_of_threshold_le {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B E : ℝ) (hE : j ^ 2 * B ≤ E) :
    Statements.EssentialWeylValue (Statements.morsePotential j A B) E := by
  let k := sqrt (E - j ^ 2 * B)
  have hk : k ^ 2 = E - j ^ 2 * B := sq_sqrt (sub_nonneg.mpr hE)
  let s := weylPhase k
  let p (n : ℕ) := weylPacketL2 k (s n) n
  let q (n : ℕ) := weylPacketImageL2 j A B k (s n) n
  let u (n : ℕ) := ‖p n‖⁻¹ • p n
  let v (n : ℕ) := ‖p n‖⁻¹ • q n
  have hl (n : ℕ) : weylWidth n ≤ ‖p n‖ ^ 2 := weylPacket_norm_sq_lower k n
  have hp (n : ℕ) : 0 < ‖p n‖ := by
    by_contra! hn
    have hz : ‖p n‖ = 0 := le_antisymm hn (norm_nonneg _)
    have h := hl n
    rw [hz] at h
    nlinarith [weylWidth_pos n]
  have hu (n : ℕ) : ‖u n‖ = 1 := by
    change ‖‖p n‖⁻¹ • p n‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp n)), inv_mul_cancel₀ (hp n).ne']
  refine ⟨u, v, fun n => ⟨hu n, ?_⟩, ?_, ?_⟩
  · apply (morsePublicWeakGraph_iff_associated hj hA B (u n) (v n)).mpr
    exact (morseAssociatedGraph _ _ _).smul_mem ‖p n‖⁻¹ (weylPacket_pair j A B k (s n) n)
  · apply weylWeak_of_right_support u hu
    intro n
    filter_upwards [Lp.coeFn_smul ‖p n‖⁻¹ (p n), weylPacketL2_ae k (s n) n] with x hsmul hpx hx
    have hout : x ∉ Icc (weylWidth n) (5 * weylWidth n) := fun hx' => (not_le.mpr hx) hx'.1
    change (p n : ℝ → ℝ) x = weylPacket k (s n) n x at hpx
    change (‖p n‖⁻¹ • p n) x = 0
    simp only [hsmul, Pi.smul_apply, smul_eq_mul, hpx, weylPacket, weylEnvelope_zero n hout,
      zero_mul, mul_zero]
  · have hlim : Tendsto (fun n => 2 * weylErrorBound j A k n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (weylErrorBound_tendsto j A k).const_mul 2
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    let ε := weylErrorBound j A k n
    have hε : 0 ≤ ε := weylErrorBound_nonneg j A k n
    have hq : ‖q n - E • p n‖ ^ 2 ≤ 4 * weylWidth n * ε ^ 2 :=
      weylResidual_norm_sq hA.le hk (s n) n
    have hsq : ‖q n - E • p n‖ ^ 2 ≤ (2 * ε * ‖p n‖) ^ 2 := calc
      _ ≤ 4 * weylWidth n * ε ^ 2 := hq
      _ ≤ 4 * ‖p n‖ ^ 2 * ε ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hl n) (by norm_num)) (sq_nonneg ε)
      _ = _ := by ring
    have he := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ε * ‖p n‖)).1 hsq
    change ‖‖p n‖⁻¹ • q n - E • (‖p n‖⁻¹ • p n)‖ ≤ 2 * ε
    rw [smul_comm E, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp n)),
      ← div_eq_inv_mul, div_le_iff₀ (hp n)]
    exact he

end ContinuousFlexibility.Radial
