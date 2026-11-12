import ContinuousFlexibility.Analysis.RootCharacteristicFactor
import ContinuousFlexibility.Analysis.N06PositiveClippedJets
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Ordinary jets of the actual factored reference root speed

Only local smoothness is used, since the totalized reciprocal and square
root need not be smooth away from the physical collar. The final estimate
is for `referenceRootSpeedFactor` itself, with its original profile and
the genuine divided derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n06_second_mul_at {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    deriv (deriv (fun t => f t * g t)) x =
      f x * deriv (deriv g) x + 2 * (deriv f x * deriv g x) +
        deriv (deriv f) x * g x := by
  have he := iteratedDeriv_fun_mul (n := 2) (hf.of_le (by simp)) (hg.of_le (by simp))
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero] at he
  exact he.trans (by ring)

/-- The reciprocal estimate remains valid with genuine local regularity. -/
theorem N06ScalarJetTwoBound.inv_at
    {f : ℝ → ℝ} {x B : ℝ} (hf : ContDiffAt ℝ ∞ f x)
    (hne : f x ≠ 0) (hB : 1 ≤ B) (hfb : N06ScalarJetTwoBound f x B)
    (hinv : |(f x)⁻¹| ≤ B) :
    N06ScalarJetTwoBound (fun t => (f t)⁻¹) x (3 * B ^ 5) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB15 : B ≤ B ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 5)
  have hB35 : B ^ 3 ≤ B ^ 5 := pow_le_pow_right₀ hB (by norm_num)
  have hB5 : 0 ≤ B ^ 5 := pow_nonneg hB0 _
  have hg : ContDiffAt ℝ ∞ (fun t => (f t)⁻¹) x := hf.inv hne
  have hfirst : |deriv (fun t => (f t)⁻¹) x| ≤ B ^ 3 := by
    calc
      _ = |deriv f x| * |(f x)⁻¹| ^ 2 := by
        rw [deriv_fun_inv'' (hf.differentiableAt (by simp)) hne,
          abs_div, abs_neg, abs_pow, div_eq_mul_inv, abs_inv, inv_pow]
      _ ≤ B * B ^ 2 := mul_le_mul hfb.first
        (pow_le_pow_left₀ (abs_nonneg _) hinv 2) (pow_nonneg (abs_nonneg _) _) hB0
      _ = B ^ 3 := by ring
  have hprod : (fun t => f t * (f t)⁻¹) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hf.continuousAt.eventually_ne hne] with t ht
    exact mul_inv_cancel₀ ht
  have hzero : deriv (deriv (fun t => f t * (f t)⁻¹)) x = 0 := by
    have he := hprod.iteratedDeriv_eq 2
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero, deriv_const', deriv_const] using he
  have hsecond := n06_second_mul_at hf hg
  rw [hzero] at hsecond
  have hsolve : deriv (deriv (fun t => (f t)⁻¹)) x =
      -(deriv (deriv f) x * (f x)⁻¹ +
        2 * deriv f x * deriv (fun t => (f t)⁻¹) x) / f x := by
    apply (eq_div_iff hne).2
    nlinarith only [hsecond]
  constructor
  · exact hinv.trans (by nlinarith)
  · exact hfirst.trans (by nlinarith)
  · have h₁ : |deriv (deriv f) x * (f x)⁻¹| ≤ B * B := by
      rw [abs_mul]
      exact mul_le_mul hfb.second hinv (abs_nonneg _) hB0
    have h₂ : |2 * deriv f x * deriv (fun t => (f t)⁻¹) x| ≤ 2 * B * B ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfb.first (by norm_num))
        hfirst (abs_nonneg _) (by positivity)
    calc
      _ = |deriv (deriv f) x * (f x)⁻¹ +
          2 * deriv f x * deriv (fun t => (f t)⁻¹) x| * |(f x)⁻¹| := by
        rw [hsolve, abs_div, abs_neg, div_eq_mul_inv, abs_inv]
      _ ≤ (B * B + 2 * B * B ^ 3) * B :=
        mul_le_mul ((abs_add_le _ _).trans (add_le_add h₁ h₂)) hinv
          (abs_nonneg _) (by positivity)
      _ ≤ 3 * B ^ 5 := by nlinarith

/-- Actual square-root jets follow by differentiating its local square
identity twice. Both inverse and ordinary value bounds are retained. -/
theorem N06ScalarJetTwoBound.sqrt_at
    {f : ℝ → ℝ} {x B : ℝ} (hf : ContDiffAt ℝ ∞ f x)
    (hpos : 0 < f x) (hB : 1 ≤ B) (hfb : N06ScalarJetTwoBound f x B)
    (hinv : (f x)⁻¹ ≤ B) :
    N06ScalarJetTwoBound (fun t => Real.sqrt (f t)) x (3 * B ^ 5) ∧
      (Real.sqrt (f x))⁻¹ ≤ B := by
  let s : ℝ → ℝ := fun t => Real.sqrt (f t)
  have hs : ContDiffAt ℝ ∞ s x := hf.sqrt hpos.ne'
  have hsp : 0 < s x := Real.sqrt_pos.mpr hpos
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hvalue : |s x| ≤ B := by
    rw [abs_of_pos hsp]
    exact (Real.sqrt_le_left hB0).mpr (((le_abs_self _).trans hfb.value).trans hBB)
  have hsinv : (s x)⁻¹ ≤ B := by
    change (Real.sqrt (f x))⁻¹ ≤ B
    rw [← Real.sqrt_inv]
    exact (Real.sqrt_le_left hB0).mpr (hinv.trans hBB)
  have hfirst : |deriv s x| ≤ B ^ 2 := by
    rw [show deriv s x = deriv f x / (2 * s x) from
      ((hf.differentiableAt (by simp)).hasDerivAt.sqrt hpos.ne').deriv,
      abs_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hsp)]
    calc
      |deriv f x| / (2 * s x) ≤ |deriv f x| / s x :=
        div_le_div_of_nonneg_left (abs_nonneg _) hsp (by linarith only [hsp])
      _ = |deriv f x| * (s x)⁻¹ := div_eq_mul_inv _ _
      _ ≤ B * B := mul_le_mul hfb.first hsinv (inv_nonneg.mpr hsp.le) hB0
      _ = B ^ 2 := (pow_two B).symm
  have heq : (fun t => s t * s t) =ᶠ[𝓝 x] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)] with t ht
    simpa only [s, ← pow_two] using Real.sq_sqrt (le_of_lt ht)
  have hsecond := n06_second_mul_at hs hs
  have hsecondEq : deriv (deriv (fun t => s t * s t)) x = deriv (deriv f) x := by
    have he := heq.iteratedDeriv_eq 2
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero] using he
  rw [hsecondEq] at hsecond
  have hsolve : deriv (deriv s) x =
      (deriv (deriv f) x - 2 * deriv s x ^ 2) / (2 * s x) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hsp.ne')).mpr
    nlinarith only [hsecond]
  have hB15 : B ≤ B ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 5)
  have hB25 : B ^ 2 ≤ B ^ 5 := pow_le_pow_right₀ hB (by norm_num)
  refine ⟨⟨hvalue.trans (by nlinarith [pow_nonneg hB0 5]),
    hfirst.trans (by nlinarith [pow_nonneg hB0 5]), ?_⟩, hsinv⟩
  have hpow : |deriv s x ^ 2| ≤ B ^ 4 := by
    rw [abs_pow]
    simpa only [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl] using
      pow_le_pow_left₀ (abs_nonneg _) hfirst 2
  have hnum : |deriv (deriv f) x - 2 * deriv s x ^ 2| ≤ B + 2 * B ^ 4 := by
    have hsub := abs_add_le (deriv (deriv f) x) (-(2 * deriv s x ^ 2))
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsub
    have hsub' : |deriv (deriv f) x - 2 * deriv s x ^ 2| ≤
        |deriv (deriv f) x| + 2 * |deriv s x ^ 2| := by
      simpa only [sub_eq_add_neg] using hsub
    exact hsub'.trans (add_le_add hfb.second
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  calc
    |deriv (deriv s) x| =
        |deriv (deriv f) x - 2 * deriv s x ^ 2| / (2 * s x) := by
      rw [hsolve, abs_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hsp)]
    _ ≤ |deriv (deriv f) x - 2 * deriv s x ^ 2| / s x :=
      div_le_div_of_nonneg_left (abs_nonneg _) hsp (by linarith only [hsp])
    _ = |deriv (deriv f) x - 2 * deriv s x ^ 2| * (s x)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (B + 2 * B ^ 4) * B :=
      mul_le_mul hnum hsinv (inv_nonneg.mpr hsp.le) (by positivity)
    _ ≤ 3 * B ^ 5 := by nlinarith [hB25]

/-- A fixed polynomial controls the genuine divided root speed from the
ordinary profile/factor jets and their primitive positive lower bounds. -/
theorem n06_referenceRootSpeedFactor_twoJet
    {w g : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    (r ι t B : ℝ) (hι : ι = 1 ∨ ι = -1) (hB : 1 ≤ B)
    (hr : 0 < r + ι * t) (hwp : 0 < w (r + ι * t)) (hgp : 0 < g t)
    (hrB : |r + ι * t| ≤ B) (hri : (r + ι * t)⁻¹ ≤ B)
    (hwB : N06ScalarJetTwoBound (fun x => w (r + ι * x)) t B)
    (hwi : (w (r + ι * t))⁻¹ ≤ B)
    (hgB : N06ScalarJetTwoBound g t B) (hgi : (g t)⁻¹ ≤ B) :
    ContDiffAt ℝ ∞ (referenceRootSpeedFactor w g r ι) t ∧
      0 < referenceRootSpeedFactor w g r ι t ∧
      N06ScalarJetTwoBound (referenceRootSpeedFactor w g r ι) t
        ((36 * (48 : ℝ) ^ 5) * B ^ 40) ∧
      (referenceRootSpeedFactor w g r ι t)⁻¹ ≤ (36 * (48 : ℝ) ^ 5) * B ^ 40 := by
  let R : ℝ → ℝ := fun x => r + ι * x
  let W : ℝ → ℝ := fun x => w (R x)
  let F : ℝ → ℝ := rootProfileRadicand w g r ι
  let P : ℝ := 48 * B ^ 7
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hR : ContDiff ℝ ∞ R := contDiff_const.add (contDiff_const.mul contDiff_id)
  have hW : ContDiff ℝ ∞ W := hw.comp hR
  have hRd : deriv R = fun _ => ι := by
    funext x
    simpa only [mul_one, id_eq] using
      (((hasDerivAt_id x).const_mul ι).const_add r).deriv
  have hRB : N06ScalarJetTwoBound R t B := by
    refine ⟨hrB, ?_, ?_⟩
    · rw [hRd]
      rcases hι with rfl | rfl <;> simpa only [abs_one, abs_neg] using hB
    · rw [hRd, deriv_const, abs_zero]
      exact hB0
  have hRinv : N06ScalarJetTwoBound (fun x => (R x)⁻¹) t (3 * B ^ 5) :=
    hRB.inv_at hR.contDiffAt hr.ne' hB (by rwa [abs_of_pos (inv_pos.mpr hr)])
  have hWinv : N06ScalarJetTwoBound (fun x => (W x)⁻¹) t (3 * B ^ 5) :=
    hwB.inv_at hW.contDiffAt hwp.ne' hB (by rwa [abs_of_pos (inv_pos.mpr hwp)])
  have hprod := hwB.mul_at hW.contDiffAt hg.contDiffAt hB0 hB0 hgB
  have hraw := hprod.mul_at (hW.contDiffAt.mul hg.contDiffAt)
    (hR.contDiffAt.inv hr.ne') (by positivity) (by positivity) hRinv
  have hFeq : F = fun x => (W x * g x) * (R x)⁻¹ := by
    funext x
    exact div_eq_mul_inv _ _
  have hFB : N06ScalarJetTwoBound F t P := by
    rw [hFeq]
    convert hraw using 1 <;> dsimp only [P] <;> ring
  have hFp : 0 < F t := rootProfileRadicand_pos hr hwp hgp
  have hF : ContDiffAt ℝ ∞ F t := contDiffAt_rootProfileRadicand hw hg hr.ne'
  have hPi : 1 ≤ P := by
    have hpow : 1 ≤ B ^ 7 := one_le_pow₀ hB
    dsimp only [P]
    linarith
  have hFi : (F t)⁻¹ ≤ P := by
    have he : (F t)⁻¹ = R t * (W t)⁻¹ * (g t)⁻¹ := by
      rw [hFeq]
      simp only [mul_inv_rev, inv_inv]
      ring
    rw [he]
    have hrle : R t ≤ B := (le_abs_self _).trans hrB
    have hsmall : R t * (W t)⁻¹ * (g t)⁻¹ ≤ B ^ 3 := by
      calc
        R t * (W t)⁻¹ * (g t)⁻¹ ≤ (B * B) * B := mul_le_mul
          (mul_le_mul hrle hwi (inv_nonneg.mpr hwp.le) hB0) hgi
          (inv_nonneg.mpr hgp.le) (mul_nonneg hB0 hB0)
        _ = B ^ 3 := by ring
    have h37 : B ^ 3 ≤ B ^ 7 := pow_le_pow_right₀ hB (by norm_num)
    exact hsmall.trans (h37.trans (by dsimp only [P]; nlinarith [pow_nonneg hB0 7]))
  obtain ⟨hS, hSi⟩ := hFB.sqrt_at hF hFp hPi hFi
  have hspeed := hS.mul_at (hF.sqrt hFp.ne') (hW.contDiffAt.inv hwp.ne')
    (by positivity) (by positivity) hWinv
  have hspeedB : N06ScalarJetTwoBound (referenceRootSpeedFactor w g r ι) t
      ((36 * (48 : ℝ) ^ 5) * B ^ 40) := by
    convert hspeed using 1
    · funext x
      exact div_eq_mul_inv _ _
    · dsimp only [P]
      ring
  have hc : 0 < referenceRootSpeedFactor w g r ι t :=
    referenceRootSpeedFactor_pos hr hwp hgp
  refine ⟨contDiffAt_referenceRootSpeedFactor hw hg hr hwp hgp, hc, hspeedB, ?_⟩
  have he : (referenceRootSpeedFactor w g r ι t)⁻¹ = W t * (Real.sqrt (F t))⁻¹ := by
    change (Real.sqrt (F t) / W t)⁻¹ = _
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
  rw [he]
  have hval : W t ≤ B := (le_abs_self _).trans hwB.value
  have hsmall := mul_le_mul hval hSi
    (inv_nonneg.mpr (Real.sqrt_nonneg (F t))) hB0
  have h840 : B ^ 8 ≤ B ^ 40 := pow_le_pow_right₀ hB (by norm_num)
  calc
    W t * (Real.sqrt (F t))⁻¹ ≤ B * P := hsmall
    _ = 48 * B ^ 8 := by dsimp only [P]; ring
    _ ≤ 48 * B ^ 40 := mul_le_mul_of_nonneg_left h840 (by norm_num)
    _ ≤ (36 * (48 : ℝ) ^ 5) * B ^ 40 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hB0 40)

end ContinuousFlexibility.Analysis
