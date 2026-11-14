module

public import ContinuousFlexibility.Radial.MorsePotentialEnergy
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The maximal distributional Morse graph

Localization and convolution give an energy inequality for a square-integrable
weak solution at a strictly positive shifted potential. The shifted form inverse
then identifies the distributional graph on the whole Lebesgue L² space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff Convolution RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem morse_mollifier_tsupport_abs (n : ℕ) {x : ℝ}
    (hx : x ∈ tsupport (morseMollifier n)) : |x| ≤ 2 := by
  rw [morseMollifier, (morseMollifierBump n).tsupport_normed_eq] at hx
  have h := Metric.mem_closedBall.mp hx
  change dist x 0 ≤ 2 * (1 / ((n : ℝ) + 1)) at h
  rw [Real.dist_eq, sub_zero] at h
  have h₁ : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

private theorem morse_scaledCutoff_eq_one (n : ℕ) {x : ℝ}
    (hx : |x| ≤ (n : ℝ) + 1) : scaledOscillatorCutoff n x = 1 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply oscillatorCutoff_eq_one
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn, one_mul]
  exact hx

private theorem morse_convolution_second_derivative {κ f : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ) (hf : MemLp f 2 volume) :
    deriv (deriv (κ ⋆ f)) = deriv (deriv κ) ⋆ f := by
  have hκ' := (contDiff_infty_iff_deriv.mp hκ).2
  have hf' := hf.locallyIntegrable (by norm_num)
  have he : deriv (κ ⋆ f) = deriv κ ⋆ f := funext fun x =>
    (hcκ.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (hκ.of_le (by norm_num)) hf' x).deriv
  rw [he]
  exact funext fun x =>
    (hcκ.deriv.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (hκ'.of_le (by norm_num)) hf' x).deriv

/-- Localizing outside the support of the translated kernel preserves the
twice differentiated weak convolution equation at the specified point. -/
private theorem morse_localized_convolution_equation {Q κ ζ : ℝ → ℝ}
    (u : MorseL2)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y : ℝ, u y * deriv (deriv φ) y) = ∫ y : ℝ, Q y * u y * φ y)
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hf : MemLp (fun y => ζ y * u y) 2 volume) (x : ℝ)
    (hζ : ∀ y, x - y ∈ tsupport κ → ζ y = 1) :
    deriv (deriv (κ ⋆ (fun y => ζ y * u y))) x =
      (κ ⋆ (fun y => (ζ y * Q y) * u y)) x := by
  let φ : ℝ → ℝ := fun y => κ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := by
    simpa only [φ, Function.comp_def, Homeomorph.trans_apply, Homeomorph.coe_neg,
      Homeomorph.coe_addLeft, sub_eq_add_neg] using
      hcκ.comp_homeomorph ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft x))
  have hφ' : deriv φ = fun y => -deriv κ (x - y) := by
    funext y
    exact ((hκ.differentiable (by norm_num) (x - y)).hasDerivAt.comp_const_sub x y).deriv
  have hφ'' : deriv (deriv φ) = fun y => deriv (deriv κ) (x - y) := by
    rw [hφ']
    funext y
    have hk := (contDiff_infty_iff_deriv.mp hκ).2
    change deriv (-(fun t : ℝ => deriv κ (x - t))) y = deriv (deriv κ) (x - y)
    simpa only [neg_neg] using
      (((hk.differentiable (by norm_num) (x - y)).hasDerivAt.comp_const_sub x y).neg).deriv
  have hs : Function.support (deriv (deriv κ)) ⊆ tsupport κ :=
    support_deriv_subset.trans tsupport_deriv_subset
  have hw := hweak φ hφ hcφ
  rw [hφ''] at hw
  rw [morse_convolution_second_derivative hκ hcκ hf,
    convolution_lsmul_swap, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ, deriv (deriv κ) (x - y) * (ζ y * u y)) =
        ∫ y : ℝ, u y * deriv (deriv κ) (x - y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : x - y ∈ tsupport κ
      · rw [hζ y hy, one_mul, mul_comm]
      · have hz : deriv (deriv κ) (x - y) = 0 :=
          Function.notMem_support.mp (fun hy' => hy (hs hy'))
        simp [hz]
    _ = ∫ y : ℝ, Q y * u y * φ y := hw
    _ = ∫ y : ℝ, κ (x - y) * ((ζ y * Q y) * u y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : x - y ∈ tsupport κ
      · rw [hζ y hy, one_mul]
        dsimp [φ]
        ring
      · have hz : κ (x - y) = 0 :=
          Function.notMem_support.mp (fun hy' => hy (subset_tsupport κ hy'))
        simp [φ, hz]

private theorem morse_compact_boundary_zero {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    Tendsto g atBot (𝓝 0) ∧ Tendsto g atTop (𝓝 0) := by
  have he : g =ᶠ[cocompact ℝ] (0 : ℝ → ℝ) := by
    simpa only [coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp hg
  exact ⟨tendsto_const_nhds.congr' (he.filter_mono atBot_le_cocompact).symm,
    tendsto_const_nhds.congr' (he.filter_mono atTop_le_cocompact).symm⟩

/-- The real cutoff identity is an integral of the actual classical derivatives. -/
private theorem morse_cutoff_square_identity {χ W : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hW : ContDiff ℝ ∞ W) :
    (∫ x : ℝ, (deriv (χ * W) x) ^ 2) +
        (∫ x : ℝ, χ x ^ 2 * W x * deriv (deriv W) x) =
      ∫ x : ℝ, (deriv χ x) ^ 2 * (W x) ^ 2 := by
  let F : ℝ → ℝ := χ * χ * W
  have hF : ContDiff ℝ ∞ F := (hχ.mul hχ).mul hW
  have hcF : HasCompactSupport F := (hcχ.mul_right : HasCompactSupport (χ * χ)).mul_right
  have hχ' := (contDiff_infty_iff_deriv.mp hχ).2
  have hW' := (contDiff_infty_iff_deriv.mp hW).2
  have hW'' := (contDiff_infty_iff_deriv.mp hW').2
  have hF' := (contDiff_infty_iff_deriv.mp hF).2
  have hI : Integrable (F * deriv (deriv W)) volume :=
    (hF.continuous.mul hW''.continuous).integrable_of_hasCompactSupport hcF.mul_right
  have hJ : Integrable (deriv F * deriv W) volume :=
    (hF'.continuous.mul hW'.continuous).integrable_of_hasCompactSupport hcF.deriv.mul_right
  have hlim := morse_compact_boundary_zero (g := F * deriv W) hcF.mul_right
  have hparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (fun x _ => (hF.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hW'.differentiable (by norm_num) x).hasDerivAt)
    hI hJ hlim.1 hlim.2
  have hK : Integrable (fun x => (deriv χ x) ^ 2 * (W x) ^ 2) volume := by
    apply ((hχ'.continuous.pow 2).mul (hW.continuous.pow 2)).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hcχ.deriv.isCompact
    intro x hx
    have hz : deriv χ x = 0 := Function.notMem_support.mp (fun h => hx (subset_tsupport _ h))
    simp [hz]
  have hsq (x : ℝ) : (deriv (χ * W) x) ^ 2 =
      (deriv χ x) ^ 2 * (W x) ^ 2 + deriv F x * deriv W x := by
    have hcx := (hχ.differentiable (by norm_num) x).hasDerivAt
    have hWx := (hW.differentiable (by norm_num) x).hasDerivAt
    have hp := (hcx.mul hWx).deriv
    have hq := ((hcx.mul hcx).mul hWx).deriv
    change deriv (χ * W) x = _ at hp
    change deriv F x = _ at hq
    simp only [Pi.mul_apply] at hq
    rw [hp, hq]
    ring
  have he : (∫ x : ℝ, χ x ^ 2 * W x * deriv (deriv W) x) =
      ∫ x : ℝ, F x * deriv (deriv W) x := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [F, Pi.mul_apply, pow_two]
  rw [he, integral_congr_ae (ae_of_all volume hsq)]
  have hadd := integral_add hK hJ
  simp only [Pi.mul_apply] at hadd
  rw [hadd, hparts]
  ring

private theorem morse_weighted_pairing {χ f g : ℝ → ℝ} (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ x, |χ x| ≤ C) (u v : MorseL2)
    (hf : (u : ℝ → ℝ) =ᵐ[volume] f) (hg : (v : ℝ → ℝ) =ᵐ[volume] g) :
    Integrable (fun x => χ x ^ 2 * f x * g x) volume ∧
      ⟪morseL2Multiplier χ hχ C hC u, morseL2Multiplier χ hχ C hC v⟫_ℝ =
        ∫ x : ℝ, χ x ^ 2 * f x * g x := by
  let M := morseL2Multiplier χ hχ C hC
  have he : (fun x => M u x * M v x) =ᵐ[volume] (fun x => χ x ^ 2 * f x * g x) := by
    filter_upwards [morseL2Mul_coeFn χ hχ C hC u, morseL2Mul_coeFn χ hχ C hC v,
      hf, hg] with x hu hv hfx hgx
    change morseL2Mul χ hχ C hC u x * morseL2Mul χ hχ C hC v x = _
    rw [hu, hv, hfx, hgx]
    ring
  refine ⟨((Lp.memLp (M u)).integrable_mul (Lp.memLp (M v))).congr he, ?_⟩
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hx

private theorem morse_mollifier_convolution_ae {f : ℝ → ℝ} (u : MorseL2)
    (hc : HasCompactSupport f) (hu : (u : ℝ → ℝ) =ᵐ[volume] f) (n : ℕ) :
    (realL2Convolution (morseMollifier n) u : ℝ → ℝ) =ᵐ[volume]
      (morseMollifier n ⋆ f) := by
  rw [← morseConvolution_toLp u (morseMollifier_contDiff n) (morseMollifier_support n) hc hu]
  exact MemLp.coeFn_toLp _

private theorem morse_weak_positive_cutoff_bound {Q χ : ℝ → ℝ}
    (hQ : Continuous Q) (hQ₁ : ∀ x, 1 ≤ Q x) (u : MorseL2)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y : ℝ, u y * deriv (deriv φ) y) = ∫ y : ℝ, Q y * u y * φ y)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (C D : ℝ)
    (hC : ∀ x, |χ x| ≤ C) (hD : ∀ x, |deriv χ x| ≤ D) :
    ‖morseL2Multiplier χ hχ.continuous C hC u‖ ^ 2 ≤
      ‖morseL2Multiplier (deriv χ) (contDiff_infty_iff_deriv.mp hχ).2.continuous D hD u‖ ^ 2 := by
  obtain ⟨R, hR⟩ := hcχ.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨K, hK⟩ := exists_nat_ge (R + 2)
  let ζ := scaledOscillatorCutoff K
  have hζ : Continuous ζ := (contDiff_scaledOscillatorCutoff K).continuous
  have hcζ : HasCompactSupport ζ := scaledOscillatorCutoff_hasCompactSupport K
  have hR' (x : ℝ) (hx : x ∈ tsupport χ) : |x| ≤ R := by
    simpa only [Real.dist_eq, sub_zero] using Metric.mem_closedBall.mp (hR hx)
  have hζ₁ (y : ℝ) (hy : |y| ≤ R + 2) : ζ y = 1 :=
    morse_scaledCutoff_eq_one K (by linarith)
  have hζχ (x : ℝ) (hx : x ∈ tsupport χ) : ζ x = 1 := hζ₁ x (by linarith [hR' x hx])
  have hlocal (n : ℕ) (x : ℝ) (hx : x ∈ tsupport χ) (y : ℝ)
      (hy : x - y ∈ tsupport (morseMollifier n)) : ζ y = 1 := by
    apply hζ₁
    calc
      |y| = |x - (x - y)| := by
        congr 1
        ring
      _ ≤ |x| + |x - y| := abs_sub _ _
      _ ≤ R + 2 := add_le_add (hR' x hx) (morse_mollifier_tsupport_abs n hy)
  let f : ℝ → ℝ := fun y => ζ y * u y
  let g : ℝ → ℝ := fun y => (ζ y * Q y) * u y
  have hcf : HasCompactSupport f := hcζ.mul_right
  have hcζQ : HasCompactSupport (fun y => ζ y * Q y) := hcζ.mul_right
  have hcg : HasCompactSupport g := hcζQ.mul_right
  have hf : MemLp f 2 volume :=
    morseMemLp_bounded_mul hζ (morseScaledCutoff_abs_le_one K) (Lp.memLp u)
  obtain ⟨B, hB⟩ := (hζ.mul hQ).bounded_above_of_compact_support hcζQ
  have hg : MemLp g 2 volume := morseMemLp_bounded_mul (hζ.mul hQ)
    (fun y => by simpa only [Real.norm_eq_abs, Pi.mul_apply] using hB y) (Lp.memLp u)
  let F : MorseL2 := hf.toLp f
  let G : MorseL2 := hg.toLp g
  have hF : (F : ℝ → ℝ) =ᵐ[volume] f := MemLp.coeFn_toLp hf
  have hG : (G : ℝ → ℝ) =ᵐ[volume] g := MemLp.coeFn_toLp hg
  let W (n : ℕ) : ℝ → ℝ := morseMollifier n ⋆ f
  let Z (n : ℕ) : ℝ → ℝ := morseMollifier n ⋆ g
  let W₂ (n : ℕ) : MorseL2 := realL2Convolution (morseMollifier n) F
  let Z₂ (n : ℕ) : MorseL2 := realL2Convolution (morseMollifier n) G
  have hW₂ (n : ℕ) : (W₂ n : ℝ → ℝ) =ᵐ[volume] W n :=
    morse_mollifier_convolution_ae F hcf hF n
  have hZ₂ (n : ℕ) : (Z₂ n : ℝ → ℝ) =ᵐ[volume] Z n :=
    morse_mollifier_convolution_ae G hcg hG n
  have hW (n : ℕ) : ContDiff ℝ ∞ (W n) :=
    morseConvolution_contDiff (morseMollifier_contDiff n) (morseMollifier_support n) hf
  have hEq (n : ℕ) (x : ℝ) (hx : x ∈ tsupport χ) : deriv (deriv (W n)) x = Z n x :=
    morse_localized_convolution_equation (ζ := ζ) u hweak (morseMollifier_contDiff n)
      (morseMollifier_support n) hf x (hlocal n x hx)
  have hχ' : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  let M := morseL2Multiplier χ hχ.continuous C hC
  let M' := morseL2Multiplier (deriv χ) hχ' D hD
  have hbound (n : ℕ) : ⟪M (W₂ n), M (Z₂ n)⟫_ℝ ≤ ⟪M' (W₂ n), M' (W₂ n)⟫_ℝ := by
    have hL := (morse_weighted_pairing hχ.continuous C hC (W₂ n) (Z₂ n) (hW₂ n) (hZ₂ n)).2
    have hRhs := (morse_weighted_pairing hχ' D hD (W₂ n) (W₂ n) (hW₂ n) (hW₂ n)).2
    change ⟪M (W₂ n), M (Z₂ n)⟫_ℝ = _ at hL
    change ⟪M' (W₂ n), M' (W₂ n)⟫_ℝ = _ at hRhs
    rw [hL, hRhs]
    have he : (fun x => χ x ^ 2 * W n x * deriv (deriv (W n)) x) =ᵐ[volume]
        (fun x => χ x ^ 2 * W n x * Z n x) := by
      filter_upwards [] with x
      by_cases hx : χ x = 0
      · simp [hx]
      · rw [hEq n x (subset_tsupport χ (Function.mem_support.mpr hx))]
    have hi := morse_cutoff_square_identity hχ hcχ (hW n)
    rw [integral_congr_ae he] at hi
    have hsq : (∫ x : ℝ, (deriv χ x) ^ 2 * (W n x) ^ 2) =
        ∫ x : ℝ, (deriv χ x) ^ 2 * W n x * W n x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [hsq] at hi
    have hn : 0 ≤ ∫ x : ℝ, (deriv (χ * W n) x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    linarith only [hi, hn]
  have hWF : Tendsto W₂ atTop (𝓝 F) := morseMollifier_convolution_tendsto F
  have hZG : Tendsto Z₂ atTop (𝓝 G) := morseMollifier_convolution_tendsto G
  have hMF : Tendsto (fun n => M (W₂ n)) atTop (𝓝 (M F)) :=
    (M.continuous.tendsto F).comp hWF
  have hMG : Tendsto (fun n => M (Z₂ n)) atTop (𝓝 (M G)) :=
    (M.continuous.tendsto G).comp hZG
  have hMF' : Tendsto (fun n => M' (W₂ n)) atTop (𝓝 (M' F)) :=
    (M'.continuous.tendsto F).comp hWF
  have hlimit : ⟪M F, M G⟫_ℝ ≤ ⟪M' F, M' F⟫_ℝ :=
    le_of_tendsto_of_tendsto (hMF.inner hMG) (hMF'.inner hMF') (Eventually.of_forall hbound)
  have hU := morse_weighted_pairing hχ.continuous C hC u u EventuallyEq.rfl EventuallyEq.rfl
  have hFG := morse_weighted_pairing hχ.continuous C hC F G hF hG
  have hUUeq : ⟪M u, M u⟫_ℝ = ∫ x : ℝ, χ x ^ 2 * u x * u x := hU.2
  have hFGeq : ⟪M F, M G⟫_ℝ = ∫ x : ℝ, χ x ^ 2 * f x * g x := hFG.2
  have hleft : ⟪M u, M u⟫_ℝ ≤ ⟪M F, M G⟫_ℝ := by
    rw [hUUeq, hFGeq]
    apply integral_mono hU.1 hFG.1
    intro x
    by_cases hx : χ x = 0
    · simp [hx]
    · have hz := hζχ x (subset_tsupport χ (Function.mem_support.mpr hx))
      simp only [f, g, hz, one_mul]
      calc
        χ x ^ 2 * u x * u x = χ x ^ 2 * (u x) ^ 2 := by ring
        _ ≤ Q x * (χ x ^ 2 * (u x) ^ 2) :=
          le_mul_of_one_le_left (by positivity) (hQ₁ x)
        _ = χ x ^ 2 * u x * (Q x * u x) := by ring
  have hF' : ⟪M' F, M' F⟫_ℝ = ∫ x : ℝ, (deriv χ x) ^ 2 * f x * f x :=
    (morse_weighted_pairing hχ' D hD F F hF hF).2
  have hU' : ⟪M' u, M' u⟫_ℝ = ∫ x : ℝ, (deriv χ x) ^ 2 * u x * u x :=
    (morse_weighted_pairing hχ' D hD u u EventuallyEq.rfl EventuallyEq.rfl).2
  have hright : ⟪M' F, M' F⟫_ℝ = ⟪M' u, M' u⟫_ℝ := by
    rw [hF', hU']
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : deriv χ x = 0
    · simp [hx]
    · have hz := hζχ x (support_deriv_subset (Function.mem_support.mpr hx))
      simp only [f, hz, one_mul]
  simpa only [real_inner_self_eq_norm_sq] using hleft.trans (hlimit.trans_eq hright)

/-- A positive shifted potential has trivial distributional L² kernel. -/
theorem morseWeakPositiveKernel_eq_zero {Q : ℝ → ℝ} (hQ : Continuous Q)
    (hQ₁ : ∀ x, 1 ≤ Q x) (u : MorseL2)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y : ℝ, u y * deriv (deriv φ) y) = ∫ y : ℝ, Q y * u y * φ y) : u = 0 := by
  have hχ := (morseScaledL2Multiplier_tendsto u).norm.pow 2
  have hχ' := (morseScaledDerivativeMultiplier_tendsto u).norm.pow 2
  have hsq : ‖u‖ ^ 2 ≤ ‖(0 : MorseL2)‖ ^ 2 :=
    le_of_tendsto_of_tendsto hχ hχ' (Eventually.of_forall fun n =>
      morse_weak_positive_cutoff_bound hQ hQ₁ u hweak (contDiff_scaledOscillatorCutoff n)
        (scaledOscillatorCutoff_hasCompactSupport n) 1 morseCutoffDerivativeConstant
        (morseScaledCutoff_abs_le_one n) (morseScaledCutoff_deriv_abs_le n))
  rw [norm_zero, zero_pow two_ne_zero] at hsq
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _)))

private theorem morse_shifted_residual_eq_zero {V : ℝ → ℝ} (hV : Continuous V)
    (γ : ℝ) (hpos : ∀ x, 1 ≤ V x + γ) (u v f : MorseL2)
    (hu : Statements.WeakSchrodingerGraph V u f)
    (hv : Statements.WeakSchrodingerGraph V v (f + γ • u - γ • v)) : u = v := by
  apply sub_eq_zero.mp
  apply morseWeakPositiveKernel_eq_zero (Q := fun x => V x + γ)
    (hV.add continuous_const) hpos (u - v)
  intro φ hφ hcφ
  let Hφ : ℝ → ℝ := fun x => -deriv (deriv φ) x + V x * φ x
  have hφ₁ := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ₂ := (contDiff_infty_iff_deriv.mp hφ₁).2
  have hP : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hD : MemLp (deriv (deriv φ)) 2 volume :=
    hφ₂.continuous.memLp_of_hasCompactSupport hcφ.deriv.deriv
  have hVφ : MemLp (fun x => V x * φ x) 2 volume :=
    (hV.mul hφ.continuous).memLp_of_hasCompactSupport hcφ.mul_left
  have hHφ : MemLp Hφ 2 volume := hD.neg.add hVφ
  let P := morseTestPairing φ hP
  let L := morseTestPairing Hφ hHφ
  have huf : P f = L u := by
    change morseTestPairing φ hP f = morseTestPairing Hφ hHφ u
    rw [morseTestPairing_apply, morseTestPairing_apply]
    exact hu φ hφ hcφ
  have hvf : P (f + γ • u - γ • v) = L v := by
    change morseTestPairing φ hP (f + γ • u - γ • v) = morseTestPairing Hφ hHφ v
    rw [morseTestPairing_apply, morseTestPairing_apply]
    exact hv φ hφ hcφ
  have hδ : L (u - v) = -(γ * P (u - v)) := by
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hvf
    simp only [map_sub]
    linarith only [huf, hvf]
  let w : MorseL2 := u - v
  change morseTestPairing Hφ hHφ w = -(γ * morseTestPairing φ hP w) at hδ
  rw [morseTestPairing_apply, morseTestPairing_apply] at hδ
  have hd : Integrable (fun x => w x * deriv (deriv φ) x) volume :=
    (Lp.memLp w).integrable_mul hD
  have hp : Integrable (fun x => w x * (V x * φ x)) volume :=
    (Lp.memLp w).integrable_mul hVφ
  have h0 : Integrable (fun x => w x * φ x) volume := (Lp.memLp w).integrable_mul hP
  have hsplit : (∫ x : ℝ, w x * Hφ x) =
      -(∫ x : ℝ, w x * deriv (deriv φ) x) + ∫ x : ℝ, w x * (V x * φ x) := by
    calc
      _ = ∫ x : ℝ, -(w x * deriv (deriv φ) x) + w x * (V x * φ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [Hφ]
        ring
      _ = _ := by
        have ha := integral_add hd.neg hp
        simp only [Pi.neg_apply] at ha
        rw [ha, integral_neg]
  have hQsplit : (∫ x : ℝ, (V x + γ) * w x * φ x) =
      (∫ x : ℝ, w x * (V x * φ x)) + γ * ∫ x : ℝ, w x * φ x := by
    calc
      _ = ∫ x : ℝ, w x * (V x * φ x) + γ * (w x * φ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_add hp (h0.const_mul γ), integral_const_mul]
  change (∫ x : ℝ, w x * deriv (deriv φ) x) = ∫ x : ℝ, (V x + γ) * w x * φ x
  rw [hsplit] at hδ
  rw [hQsplit]
  linarith only [hδ]

/-- The distributional and associated graphs agree for all L² pairs. -/
theorem morsePublicWeakGraph_iff_associated {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (u f : MorseL2) :
    Statements.WeakSchrodingerGraph (Statements.morsePotential j A B) u f ↔
      (u, f) ∈ morseAssociatedGraph ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) := by
  constructor
  · intro hu
    let α : ℝ := (j * sqrt A - 1) / 2
    let omega : ℝ := j * sqrt A
    let b : ℝ := j ^ 2 * B
    let γ := morseFormShift α b
    have hω : 0 < omega := mul_pos hj (sqrt_pos.mpr hA)
    have hω₂ : omega ^ 2 = j ^ 2 * A := by
      dsimp only [omega]
      rw [mul_pow, sq_sqrt hA.le]
    have hα : 2 * α + 1 = omega := by dsimp [α, omega]; ring
    have hγ : γ = 1 + j ^ 2 * A / 2 + |j ^ 2 * B| := by
      simp only [γ, morseFormShift, hα, hω₂, b]
    have hV : Continuous (Statements.morsePotential j A B) := by
      unfold Statements.morsePotential morseRho
      fun_prop
    have hpos (x : ℝ) : 1 ≤ Statements.morsePotential j A B x + γ := by
      rw [hγ]
      linarith only [morsePotential_lower hj hA B x, mul_nonneg (sq_nonneg j) hA.le,
        neg_le_abs (j ^ 2 * B)]
    let v := morseShiftedResolvent α b hω (f + γ • u)
    have hv : (v, f + γ • u - γ • v) ∈ morseAssociatedGraph α omega b :=
      morseShiftedResolvent_mem_graph α b hω (f + γ • u)
    have hw := (morsePublicWeakGraph_iff_compactWeak hA j B v (f + γ • u - γ • v)).mpr
      (morseAssociatedGraph_compact_weak α omega b v (f + γ • u - γ • v) hv)
    have he := morse_shifted_residual_eq_zero hV γ hpos u v f hu hw
    simpa only [he, add_sub_cancel_right] using hv
  · intro h
    exact (morsePublicWeakGraph_iff_compactWeak hA j B u f).mpr
      (morseAssociatedGraph_compact_weak _ _ _ u f h)

theorem morsePublicWeakGraph_iff_formGraph {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (u f : MorseL2) :
    Statements.WeakSchrodingerGraph (Statements.morsePotential j A B) u f ↔
      Statements.SchrodingerFormGraph (Statements.morsePotential j A B) u f :=
  (morsePublicWeakGraph_iff_associated hj hA B u f).trans
    (morsePublicFormGraph_iff_associated hj hA B u f).symm

theorem morseActualClosedFormRealization {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    Statements.ActualClosedFormRealization (Statements.morsePotential j A B) := by
  refine ⟨⟨j ^ 2 * A / 4 - j ^ 2 * B, fun x => ?_⟩,
    morsePublicEnergyLift_isClosed hj hA B, morsePublicEnergyCore_closure hj hA B, ?_⟩
  · linarith only [morsePotential_lower hj hA B x]
  · exact morsePublicWeakGraph_iff_formGraph hj hA B

end ContinuousFlexibility.Radial
