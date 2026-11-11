import ContinuousFlexibility.Radial.MorseMaximalDomain
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exclusion of Weyl sequences below the Morse threshold

Uniform energy bounds and weak convergence control the interval averages
of smooth energy approximants. The fundamental theorem of calculus turns
this into pointwise convergence and a uniform bound for the approximants.
The exponentially decaying negative part of the shifted potential then
has vanishing form contribution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

local instance : SeminormedAddCommGroup (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance : NormedSpace ℝ (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private def morseIntervalUnit (x y : ℝ) : MorseL2 :=
  indicatorConstLp (s := Ioc x y) 2 measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) 1

private theorem morseIntervalUnit_ae (x y : ℝ) :
    (morseIntervalUnit x y : ℝ → ℝ) =ᵐ[volume] (Ioc x y).indicator (fun _ => 1) :=
  indicatorConstLp_coeFn

private theorem morseInterval_pairing (g : MorseL2) {f : ℝ → ℝ}
    (hf : (g : ℝ → ℝ) =ᵐ[volume] f) (x y : ℝ) :
    ⟪g, morseIntervalUnit x y⟫_ℝ = ∫ t in Ioc x y, f t := by
  rw [L2.inner_def, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hf, morseIntervalUnit_ae x y] with t hft ht
  simp only [RCLike.inner_apply, conj_trivial, hft, ht]
  by_cases h : t ∈ Ioc x y
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

private theorem morseIntervalUnit_norm {x y : ℝ} (hxy : x ≤ y) :
    ‖morseIntervalUnit x y‖ = sqrt (y - x) := by
  have h : ‖morseIntervalUnit x y‖ ^ 2 = y - x := by
    rw [← real_inner_self_eq_norm_sq, morseInterval_pairing _ (morseIntervalUnit_ae x y) x y]
    calc
      _ = ∫ _ in Ioc x y, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact indicator_of_mem ht _
      _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hxy, smul_eq_mul, mul_one]
  have hs := congrArg sqrt h
  rwa [sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs

private theorem morseSmooth_abs_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (d : MorseL2) (hd : (d : ℝ → ℝ) =ᵐ[volume] deriv φ) {x y : ℝ} (hxy : x ≤ y) :
    |φ y - φ x| ≤ ‖d‖ * sqrt (y - x) := by
  have hs : Continuous (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2.continuous
  have hFTC : (∫ t in x..y, deriv φ t) = φ y - φ x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hφ.differentiable (by simp) t).hasDerivAt) (hs.intervalIntegrable _ _)
  rw [← hFTC, intervalIntegral.integral_of_le hxy, ← morseInterval_pairing d hd x y,
    ← Real.norm_eq_abs, ← morseIntervalUnit_norm hxy]
  exact norm_inner_le_norm (𝕜 := ℝ) _ _

private def morseIntervalAverage (g : MorseL2) (x δ : ℝ) : ℝ :=
  δ⁻¹ * ⟪g, morseIntervalUnit x (x + δ)⟫_ℝ

private theorem morseIntervalAverage_error {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (g d : MorseL2) (hg : (g : ℝ → ℝ) =ᵐ[volume] φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] deriv φ) (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |φ x - morseIntervalAverage g x δ| ≤ ‖d‖ * sqrt δ := by
  have hxy : x ≤ x + δ := by linarith
  have hid : φ x - morseIntervalAverage g x δ =
      δ⁻¹ * (∫ t in x..(x + δ), φ x - φ t) := by
    rw [morseIntervalAverage, morseInterval_pairing g hg, ← intervalIntegral.integral_of_le hxy,
      intervalIntegral.integral_sub intervalIntegrable_const (hφ.continuous.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
    field_simp [hδ.ne']
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + δ)
    (C := ‖d‖ * sqrt δ) (f := fun t => φ x - φ t) (fun t ht => by
      rw [uIoc_of_le hxy] at ht
      rw [Real.norm_eq_abs, abs_sub_comm]
      refine (morseSmooth_abs_sub_le hφ d hd ht.1.le).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [ht.2])) (norm_nonneg d))
  rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hδ] at hi
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  calc
    _ ≤ δ⁻¹ * ((‖d‖ * sqrt δ) * δ) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hδ.le)
    _ = _ := by
      field_simp [hδ.ne']

private theorem morseIntervalAverage_one_bound (g : MorseL2) (x : ℝ) :
    |morseIntervalAverage g x 1| ≤ ‖g‖ := by
  have hxy : x ≤ x + 1 := by linarith
  have hi := norm_inner_le_norm (𝕜 := ℝ) g (morseIntervalUnit x (x + 1))
  rw [morseIntervalUnit_norm hxy, add_sub_cancel_left, sqrt_one, mul_one, Real.norm_eq_abs] at hi
  simpa only [morseIntervalAverage, inv_one, one_mul] using hi

private theorem morseSmooth_limit_of_weak {φ : ℕ → ℝ → ℝ} (hφ : ∀ n, ContDiff ℝ ∞ (φ n))
    (g d : ℕ → MorseL2) (hg : ∀ n, (g n : ℝ → ℝ) =ᵐ[volume] φ n)
    (hd : ∀ n, (d n : ℝ → ℝ) =ᵐ[volume] deriv (φ n))
    (hw : ∀ h : MorseL2, Tendsto (fun n => ⟪g n, h⟫_ℝ) atTop (𝓝 0))
    {C M : ℝ} (hC : 0 ≤ C) (hD : ∀ n, ‖d n‖ ≤ C) (hG : ∀ n, ‖g n‖ ≤ M) :
    (∀ x, Tendsto (fun n => φ n x) atTop (𝓝 0)) ∧ ∀ n x, |φ n x| ≤ C + M := by
  constructor
  · intro x
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let a := ε / (2 * (C + 1))
    have ha : 0 < a := div_pos hε (by positivity)
    let δ := a ^ 2
    have hδ : 0 < δ := sq_pos_of_pos ha
    have hs : C * sqrt δ < ε / 2 := by
      change C * sqrt (a ^ 2) < _
      rw [sqrt_sq_eq_abs, abs_of_pos ha]
      have he : (C + 1) * a = ε / 2 := by
        dsimp [a]
        field_simp [show C + 1 ≠ 0 by linarith]
      nlinarith
    have havg : Tendsto (fun n => morseIntervalAverage (g n) x δ) atTop (𝓝 0) := by
      simpa only [morseIntervalAverage, mul_zero] using
        (hw (morseIntervalUnit x (x + δ))).const_mul δ⁻¹
    filter_upwards [(Metric.tendsto_nhds.mp havg) (ε / 2) (by positivity)] with n hn
    have hn' : |morseIntervalAverage (g n) x δ| < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hn
    have he := (morseIntervalAverage_error (hφ n) (g n) (d n) (hg n) (hd n) x hδ).trans
      (mul_le_mul_of_nonneg_right (hD n) (sqrt_nonneg δ))
    rw [Real.dist_eq, sub_zero]
    calc
      _ = |(φ n x - morseIntervalAverage (g n) x δ) + morseIntervalAverage (g n) x δ| := by
        rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
      _ < ε := by linarith
  · intro n x
    have he := morseIntervalAverage_error (hφ n) (g n) (d n) (hg n) (hd n) x (by norm_num : 0 < (1 : ℝ))
    rw [sqrt_one, mul_one] at he
    calc
      _ = |(φ n x - morseIntervalAverage (g n) x 1) + morseIntervalAverage (g n) x 1| := by
        rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
      _ ≤ C + M := add_le_add (he.trans (hD n)) ((morseIntervalAverage_one_bound _ _).trans (hG n))

private def morseRightWeight : ℝ → ℝ := (Ioi 0).indicator (fun x => exp (-x))

private theorem morseRightWeight_integrable : Integrable morseRightWeight volume :=
  (integrableOn_exp_neg_Ioi 0).integrable_indicator measurableSet_Ioi

private theorem morseRightWeight_nonneg (x : ℝ) : 0 ≤ morseRightWeight x := by
  unfold morseRightWeight
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx]
    exact (exp_pos _).le
  · simp [indicator_of_notMem hx]

private theorem morsePotential_threshold_lower {A : ℝ} (hA : 0 ≤ A) (j B x : ℝ) :
    j ^ 2 * B - (j ^ 2 * A) * morseRightWeight x ≤ Statements.morsePotential j A B x := by
  rw [morsePotential_quadratic]
  unfold morseRightWeight
  have ha := mul_nonneg (sq_nonneg j) hA
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx]
    nlinarith [mul_nonneg ha (sq_nonneg (exp (-x)))]
  · rw [indicator_of_notMem hx, mul_zero, sub_zero]
    have hx' : x ≤ 0 := le_of_not_gt hx
    have he : 1 ≤ exp (-x) := Real.one_le_exp_iff.mpr (neg_nonneg.mpr hx')
    have hq : 0 ≤ exp (-x) ^ 2 - exp (-x) := by
      nlinarith [mul_nonneg (exp_pos (-x)).le (sub_nonneg.mpr he)]
    linarith [mul_nonneg ha hq]

private theorem morseWeighted_mass_tendsto {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ n, Continuous (φ n)) (hlim : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n x, |φ n x| ≤ C) :
    (∀ n, Integrable (fun x => morseRightWeight x * φ n x ^ 2) volume) ∧
    Tendsto (fun n => ∫ x : ℝ, morseRightWeight x * φ n x ^ 2) atTop (𝓝 0) := by
  have hF (n : ℕ) : AEStronglyMeasurable (fun x => morseRightWeight x * φ n x ^ 2) volume :=
    morseRightWeight_integrable.aestronglyMeasurable.mul ((hφ n).pow 2).aestronglyMeasurable
  have hB : Integrable (fun x => morseRightWeight x * C ^ 2) volume :=
    morseRightWeight_integrable.mul_const _
  have hdom (n : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖morseRightWeight x * φ n x ^ 2‖ ≤ morseRightWeight x * C ^ 2 := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (morseRightWeight_nonneg x) (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (morseRightWeight_nonneg x)
    rw [← sq_abs (φ n x)]
    exact (sq_le_sq₀ (abs_nonneg _) hC).2 (hbound n x)
  refine ⟨fun n => hB.mono' (hF n) (hdom n), ?_⟩
  have hp (x : ℝ) : Tendsto (fun n => morseRightWeight x * φ n x ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using ((hlim x).pow 2).const_mul (morseRightWeight x)
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun x => morseRightWeight x * C ^ 2)
      hF hB hdom (Eventually.of_forall hp)

private theorem morseSmooth_form_lower {A : ℝ} (hA : 0 < A) (j B : ℝ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hI : Integrable (fun x => morseRightWeight x * φ x ^ 2) volume) :
    let S := morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)
    (j ^ 2 * B) * ‖morseEnergyBase S‖ ^ 2 - (j ^ 2 * A) * (∫ x : ℝ, morseRightWeight x * φ x ^ 2) ≤
      morsePhysicalForm ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) S S := by
  intro S
  have hf := (compactSmooth_morseEnergyDomain hφ hc).2.1
  have hg : (morseEnergyBase S : ℝ → ℝ) =ᵐ[volume] φ := MemLp.coeFn_toLp hf
  have hφ₂ := (oscillator_memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hnorm : ‖morseEnergyBase S‖ ^ 2 = ∫ x : ℝ, φ x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
  have hpot : (fun x => Statements.morsePotential j A B x * morseEnergyBase S x * morseEnergyBase S x)
      =ᵐ[volume] (fun x => Statements.morsePotential j A B x * φ x * φ x) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have hVI := (morsePotential_pairing_integrable j A B S S).congr hpot
  have hB := (hφ₂.const_mul (j ^ 2 * B)).sub (hI.const_mul (j ^ 2 * A))
  calc
    _ = ∫ x : ℝ, (j ^ 2 * B) * φ x ^ 2 - (j ^ 2 * A) * (morseRightWeight x * φ x ^ 2) := by
      rw [hnorm, ← integral_const_mul, ← integral_const_mul]
      exact (integral_sub (hφ₂.const_mul (j ^ 2 * B)) (hI.const_mul (j ^ 2 * A))).symm
    _ ≤ ∫ x : ℝ, Statements.morsePotential j A B x * φ x * φ x := by
      refine integral_mono hB hVI (fun x => ?_)
      have hb := mul_le_mul_of_nonneg_right (morsePotential_threshold_lower hA.le j B x) (sq_nonneg (φ x))
      change (j ^ 2 * B) * φ x ^ 2 - (j ^ 2 * A) * (morseRightWeight x * φ x ^ 2) ≤ _
      nlinarith only [hb]
    _ ≤ _ := by
      rw [← integral_congr_ae hpot, morsePhysicalForm_eq_potential_integral hA]
      linarith [real_inner_self_nonneg (x := morseEnergyDerivative S)]

private theorem morseForm_approx_limit
    (Q : MorseWeakEnergy →L[ℝ] MorseWeakEnergy →L[ℝ] ℝ) (U S : ℕ → MorseWeakEnergy)
    {M : ℝ} (hU : ∀ n, ‖U n‖ ≤ M) (hS : ∀ n, ‖S n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖S n - U n‖) atTop (𝓝 0)) {E : ℝ}
    (hQ : Tendsto (fun n => Q (U n) (U n)) atTop (𝓝 E)) :
    Tendsto (fun n => Q (S n) (S n)) atTop (𝓝 E) := by
  have hlim : Tendsto (fun n => 2 * ‖Q‖ * M * ‖S n - U n‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hclose.const_mul (2 * ‖Q‖ * M)
  have hdiff : Tendsto (fun n => Q (S n) (S n) - Q (U n) (U n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have he : Q (S n) (S n) - Q (U n) (U n) =
        Q (S n - U n) (S n) + Q (U n) (S n - U n) := by
      simp only [map_sub, sub_apply]
      ring
    rw [he]
    calc
      _ ≤ ‖Q (S n - U n) (S n)‖ + ‖Q (U n) (S n - U n)‖ := norm_add_le _ _
      _ ≤ (‖Q‖ * ‖S n - U n‖) * M + (‖Q‖ * M) * ‖S n - U n‖ := by
        refine add_le_add ((Q.le_opNorm₂ _ _).trans ?_) ((Q.le_opNorm₂ _ _).trans ?_)
        · exact mul_le_mul_of_nonneg_left (hS n) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hU n) (norm_nonneg _))
            (norm_nonneg _)
      _ = _ := by ring
  simpa only [sub_add_cancel, zero_add] using hdiff.add hQ

/-- A genuine Morse Weyl sequence has energy at least the right asymptotic
potential. The estimate uses the actual differential graph and form core. -/
theorem morseThreshold_le_of_essentialWeylValue {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B E : ℝ) (h : Statements.EssentialWeylValue (Statements.morsePotential j A B) E) :
    j ^ 2 * B ≤ E := by
  obtain ⟨u, v, hgraph, hweak, hresidual⟩ := h
  let w := j * sqrt A
  let α := (w - 1) / 2
  let b := j ^ 2 * B
  let Q := morsePhysicalForm α w b
  let r (n : ℕ) := v n - E • u n
  have hnorm (n : ℕ) : ‖u n‖ = 1 := (hgraph n).1
  have hlift (n : ℕ) : ∃ U : MorseWeakEnergy, morseEnergyBase U = u n ∧
      ∀ W : MorseWeakEnergy, Q U W = ⟪v n, morseEnergyBase W⟫_ℝ :=
    (morsePublicWeakGraph_iff_associated hj hA B _ _).mp (hgraph n).2
  choose U hbase hpair using hlift
  have hq (n : ℕ) : Q (U n) (U n) = E + ⟪r n, u n⟫_ℝ := by
    rw [hpair n, hbase n]
    have hv : v n = E • u n + r n := by dsimp [r]; abel
    conv_lhs => rw [hv]
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm n, one_pow, mul_one]
  have hr (n : ℕ) : ‖⟪r n, u n⟫_ℝ‖ ≤ ‖r n‖ := by
    simpa only [hnorm n, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (r n) (u n)
  have hq₀ : Tendsto (fun n => ⟪r n, u n⟫_ℝ) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hr hresidual)
  have hQ : Tendsto (fun n => Q (U n) (U n)) atTop (𝓝 E) := by
    simpa only [hq, add_zero] using hq₀.const_add E
  obtain ⟨N, hN⟩ := (show Tendsto (fun n => ‖r n‖) atTop (𝓝 0) from hresidual).bddAbove_range
  have hNn (n : ℕ) : ‖r n‖ ≤ N := hN (mem_range_self n)
  have hN₀ : 0 ≤ N := (norm_nonneg (r 0)).trans (hNn 0)
  have hc : 0 < morseCoercivityConstant w := morseCoercivityConstant_pos (mul_pos hj (sqrt_pos.mpr hA))
  have hshift : 0 ≤ morseFormShift α b := by
    unfold morseFormShift
    positivity
  let K := sqrt ((|E| + N + morseFormShift α b) / morseCoercivityConstant w)
  have hK : 0 ≤ K := sqrt_nonneg _
  have hU (n : ℕ) : ‖U n‖ ≤ K := by
    have hcoer := morseShiftedForm_coercive_bound α w b (U n)
    rw [morseShiftedForm_apply, hbase n, real_inner_self_eq_norm_sq, hnorm n, one_pow, mul_one] at hcoer
    change morseCoercivityConstant w * ‖U n‖ ^ 2 ≤ Q (U n) (U n) + morseFormShift α b at hcoer
    rw [hq n] at hcoer
    have hinner : ⟪r n, u n⟫_ℝ ≤ N := by
      have hi := hr n
      rw [Real.norm_eq_abs] at hi
      exact (le_abs_self _).trans (hi.trans (hNn n))
    have hb : ‖U n‖ ^ 2 ≤ (|E| + N + morseFormShift α b) / morseCoercivityConstant w := by
      rw [le_div_iff₀ hc]
      linarith [le_abs_self E]
    apply (sq_le_sq₀ (norm_nonneg _) hK).1
    change _ ≤ (sqrt ((|E| + N + morseFormShift α b) / morseCoercivityConstant w)) ^ 2
    rw [sq_sqrt (div_nonneg (add_nonneg (add_nonneg (abs_nonneg E) hN₀) hshift) hc.le)]
    exact hb
  let ε (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := by
    rw [show ε n = 1 / ((n : ℝ) + 1) by rw [one_div]]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1), one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have happrox (n : ℕ) : ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ),
      ‖morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ) - U n‖ < ε n := by
    obtain ⟨Z, ⟨φ, hφ, hcφ, rfl⟩, hdist⟩ := morseCompactSmoothEnergy_dense.exists_dist_lt (U n) (hε n)
    exact ⟨φ, hφ, hcφ, by rwa [dist_comm, dist_eq_norm] at hdist⟩
  choose φ hφ hcφ hApproxBound using happrox
  let S (n : ℕ) := morseEnergyLift (compactSmooth_morseEnergyDomain (hφ n) (hcφ n))
  let g (n : ℕ) := morseEnergyBase (S n)
  let d (n : ℕ) := morseEnergyDerivative (S n)
  have hclose (n : ℕ) : ‖S n - U n‖ ≤ ε n := (hApproxBound n).le
  have hS (n : ℕ) : ‖S n‖ ≤ K + 1 := by
    calc
      _ = ‖(S n - U n) + U n‖ := by rw [sub_add_cancel]
      _ ≤ ‖S n - U n‖ + ‖U n‖ := norm_add_le _ _
      _ ≤ K + 1 := by linarith [hclose n, hε₁ n, hU n]
  have hgl (n : ℕ) : ‖g n - u n‖ ≤ ε n := by
    have hz := morseEnergyCoordinate_norm_le 0 (S n - U n)
    change ‖morseEnergyBase (S n - U n)‖ ≤ _ at hz
    rw [map_sub, hbase n] at hz
    exact hz.trans (hclose n)
  have hgw (h' : MorseL2) : Tendsto (fun n => ⟪g n, h'⟫_ℝ) atTop (𝓝 0) := by
    have hε' : Tendsto (fun n => ε n * ‖h'‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using hεlim.mul_const ‖h'‖
    have hdiff : Tendsto (fun n => ⟪g n, h'⟫_ℝ - ⟪u n, h'⟫_ℝ) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hε'
      rw [← inner_sub_left]
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul_of_nonneg_right (hgl n) (norm_nonneg h'))
    simpa only [sub_add_cancel, zero_add] using hdiff.add (hweak h')
  have hg (n : ℕ) : (g n : ℝ → ℝ) =ᵐ[volume] φ n :=
    MemLp.coeFn_toLp (compactSmooth_morseEnergyDomain (hφ n) (hcφ n)).2.1
  have hd (n : ℕ) : (d n : ℝ → ℝ) =ᵐ[volume] deriv (φ n) :=
    MemLp.coeFn_toLp (compactSmooth_morseEnergyDomain (hφ n) (hcφ n)).2.2.1
  have hbound (i : Fin 3) (n : ℕ) : ‖morseEnergyCoordinate i (S n)‖ ≤ K + 1 :=
    (morseEnergyCoordinate_norm_le i (S n)).trans (hS n)
  have hK₁ : 0 ≤ K + 1 := by linarith
  obtain ⟨hφlim, hφbound⟩ := morseSmooth_limit_of_weak hφ g d hg hd hgw hK₁ (hbound 1) (hbound 0)
  obtain ⟨hI, hIlim⟩ := morseWeighted_mass_tendsto (fun n => (hφ n).continuous) hφlim
    (add_nonneg hK₁ hK₁) hφbound
  have hgNorm : Tendsto (fun n => ‖g n‖) atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hεlim
    rw [Real.norm_eq_abs, ← hnorm n]
    exact (abs_norm_sub_norm_le (g n) (u n)).trans (hgl n)
  have hformLimit : Tendsto (fun n => Q (S n) (S n)) atTop (𝓝 E) :=
    morseForm_approx_limit Q U S (fun n => by linarith [hU n]) hS
      (squeeze_zero (fun n => norm_nonneg _) hclose hεlim) hQ
  have hlimit : Tendsto (fun n => b * ‖g n‖ ^ 2 -
      (j ^ 2 * A) * (∫ x : ℝ, morseRightWeight x * φ n x ^ 2)) atTop (𝓝 b) := by
    simpa only [one_pow, mul_one, mul_zero, sub_zero] using
      ((hgNorm.pow 2).const_mul b).sub (hIlim.const_mul (j ^ 2 * A))
  exact le_of_tendsto_of_tendsto' hlimit hformLimit
    (fun n => morseSmooth_form_lower hA j B (hφ n) (hcφ n) (hI n))

end ContinuousFlexibility.Radial
