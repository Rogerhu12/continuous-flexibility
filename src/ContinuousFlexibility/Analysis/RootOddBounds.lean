module

public import ContinuousFlexibility.Analysis.RootCompositionIntegral
public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A smooth integral model for the odd root quotient

The odd divided difference is the average of the middle partial derivative
over a symmetric interval.  This realizes it as the even root substitution
of a globally smooth function.  Compact-parameter integral estimates and
the ordinary composition bounds control its jets with one input derivative
more than the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology Interval

/-- The middle directional derivative in the source coordinates. -/
def rootMiddleDerivative (G : ℝ × ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ G q (0, 1, 0)

/-- A global smooth model of the odd divided difference. -/
def rootOddIntegral (G : ℝ × ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
    rootMiddleDerivative G (q.1, t * q.2.1, q.2.2)

theorem contDiff_rootMiddleDerivative {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (rootMiddleDerivative G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply contDiff_const

theorem hasDerivAt_rootMiddleDerivative {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (x z θ : ℝ) :
    HasDerivAt (fun t : ℝ => G (x, t, θ)) (rootMiddleDerivative G (x, z, θ)) z := by
  have hc : HasDerivAt (fun t : ℝ => (x, t, θ)) (0, 1, 0) z :=
    (hasDerivAt_const z x).prodMk ((hasDerivAt_id' z).prodMk (hasDerivAt_const z θ))
  simpa only [Function.comp_def, rootMiddleDerivative] using
    ((hG.differentiable (by simp)) (x, z, θ)).hasFDerivAt.comp_hasDerivAt z hc

theorem contDiff_rootOddIntegral {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (rootOddIntegral G) := by
  have hIntegrand : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × ℝ =>
      rootMiddleDerivative G (q.1.1, q.2 * q.1.2.1, q.1.2.2)) :=
    (contDiff_rootMiddleDerivative hG).comp
      (contDiff_fst.fst.prodMk
        ((contDiff_snd.mul contDiff_fst.snd.fst).prodMk contDiff_fst.snd.snd))
  have hI := contDiff_intervalIntegral_of_contDiff hIntegrand (-1) 1
  exact contDiff_const.mul hI

theorem rootOddIntegral_factor {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (q : ℝ × ℝ × ℝ) :
    (2 * q.2.1) * rootOddIntegral G q = G q - G (q.1, -q.2.1, q.2.2) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => G (q.1, t * q.2.1, q.2.2))
      (q.2.1 * rootMiddleDerivative G (q.1, t * q.2.1, q.2.2)) t := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_rootMiddleDerivative hG q.1 (t * q.2.1) q.2.2).scomp t
        (hasDerivAt_mul_const q.2.1)
  have hc : Continuous (fun t : ℝ =>
      q.2.1 * rootMiddleDerivative G (q.1, t * q.2.1, q.2.2)) :=
    continuous_const.mul ((contDiff_rootMiddleDerivative hG).continuous.comp
      (continuous_const.prodMk ((continuous_id.mul continuous_const).prodMk continuous_const)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable (-1) 1)
  calc
    (2 * q.2.1) * rootOddIntegral G q = q.2.1 *
        ∫ t in (-1 : ℝ)..1, rootMiddleDerivative G (q.1, t * q.2.1, q.2.2) := by
      dsimp only [rootOddIntegral]
      ring
    _ = G q - G (q.1, -q.2.1, q.2.2) := by
      simpa only [intervalIntegral.integral_const_mul, one_mul, neg_one_mul, Prod.mk.eta] using h

theorem rootOddIntegral_zero (G : ℝ × ℝ × ℝ → ℝ) (x θ : ℝ) :
    rootOddIntegral G (x, 0, θ) = rootMiddleDerivative G (x, 0, θ) := by
  simp only [rootOddIntegral, mul_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem rootOddIntegral_even {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (x z θ : ℝ) :
    rootOddIntegral G (x, -z, θ) = rootOddIntegral G (x, z, θ) := by
  by_cases hz : z = 0
  · simp only [hz, neg_zero]
  have hp := rootOddIntegral_factor hG (x, z, θ)
  have hm := rootOddIntegral_factor hG (x, -z, θ)
  simp only [neg_neg] at hm
  have heq : (2 * z) * rootOddIntegral G (x, -z, θ) =
      (2 * z) * rootOddIntegral G (x, z, θ) := by
    nlinarith only [hp, hm]
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hz) heq

/-- On the nonnegative halfspace, applying the even construction to the
integral model reproduces the prescribed odd quotient exactly. -/
theorem rootEven_rootOddIntegral_eqOn {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) :
    EqOn (rootEven (rootOddIntegral G)) (rootOdd G) (Ici (0 : ℝ) ×ˢ univ) := by
  intro p hp
  have he : rootEven (rootOddIntegral G) p =
      rootOddIntegral G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) := by
    rw [rootEven, rootOddIntegral_even hG]
    ring
  rw [he]
  by_cases hx : p.1 = 0
  · rw [rootOdd, if_pos hx, hx, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0),
      rootOddIntegral_zero]
    exact (hasDerivAt_rootMiddleDerivative hG 0 0 p.2).deriv.symm
  · have hxpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hx)
    have hrne : p.1 ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hxpos _).ne'
    rw [rootOdd, if_neg hx]
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hrne)).mpr
    calc
      rootOddIntegral G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) * (2 * p.1 ^ (3 / 2 : ℝ)) =
          (2 * p.1 ^ (3 / 2 : ℝ)) *
            rootOddIntegral G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) := mul_comm _ _
      _ = _ := rootOddIntegral_factor hG (p.1, p.1 ^ (3 / 2 : ℝ), p.2)

private theorem exists_compact_jet_power_bound
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E → F} (hA : ContDiff ℝ ∞ A) {K : Set E} (hK : IsCompact K) (s : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ s →
      ∀ q ∈ K, ‖iteratedFDeriv ℝ i A q‖ ≤ D ^ i := by
  let J : E → ℝ := fun q => ∑ i ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ i A q‖
  have hJ : Continuous J :=
    continuous_finsetSum _ (fun i _ => (hA.continuous_iteratedFDeriv (by simp)).norm)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hJ.continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro i hi his q hq
  have hJnonneg : 0 ≤ J q :=
    Finset.sum_nonneg (fun j _ => norm_nonneg (iteratedFDeriv ℝ j A q))
  have hb := hB q hq
  rw [Real.norm_of_nonneg hJnonneg] at hb
  have hiJ : ‖iteratedFDeriv ℝ i A q‖ ≤ J q :=
    Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j A q‖)
      (fun j _ => norm_nonneg (iteratedFDeriv ℝ j A q))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le his))
  exact (hiJ.trans hb).trans ((le_max_right 1 B).trans
    (le_self_pow₀ (le_max_left 1 B) (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi))))

local notation "rootSourceBox" =>
  Set.prod (Icc (0 : ℝ) 1)
    (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))

/-- The integral model of the odd quotient loses precisely one input
derivative in a uniform finite-jet estimate. -/
theorem exists_csBound_rootOddIntegral (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ M : ℝ, CSBound (s + 1) rootSourceBox G M →
        CSBound s rootSourceBox (rootOddIntegral G) (C * M) := by
  let A : (ℝ × ℝ × ℝ) × ℝ → ℝ × ℝ × ℝ :=
    fun q => (q.1.1, q.2 * q.1.2.1, q.1.2.2)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_fst.fst.prodMk
      ((contDiff_snd.mul contDiff_fst.snd.fst).prodMk contDiff_fst.snd.snd)
  have hcompact : IsCompact (rootSourceBox ×ˢ Icc (-1 : ℝ) 1) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc
  obtain ⟨D, hD, hDjets⟩ := exists_compact_jet_power_bound hA hcompact s
  let C : ℝ := 1 + ∑ i ∈ Finset.range (s + 1), (i.factorial : ℝ) * D ^ i
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hterm (i : ℕ) : 0 ≤ (i.factorial : ℝ) * D ^ i :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hDnonneg _)
  have hCpos : 0 < C :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => hterm i))
  have hcoeff (n : ℕ) (hn : n ≤ s) : (n.factorial : ℝ) * D ^ n ≤ C := by
    have hnSum : (n.factorial : ℝ) * D ^ n ≤
        ∑ i ∈ Finset.range (s + 1), (i.factorial : ℝ) * D ^ i :=
      Finset.single_le_sum (fun i _ => hterm i)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    exact hnSum.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hCpos, ?_⟩
  intro G hG M hB
  have hzero : ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ rootSourceBox :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨by norm_num, by norm_num⟩,
      ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) _ hzero)
  have hMiddle := contDiff_rootMiddleDerivative hG
  have hMiddleBound (i : ℕ) (hi : i ≤ s) (y : ℝ × ℝ × ℝ) (hy : y ∈ rootSourceBox) :
      ‖iteratedFDeriv ℝ i (rootMiddleDerivative G) y‖ ≤ M := by
    have hv : ‖((0, 1, 0) : ℝ × ℝ × ℝ)‖ = 1 := by norm_num [Prod.norm_mk]
    have h := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ G) (c := ((0, 1, 0) : ℝ × ℝ × ℝ)) (x := y) (n := i)
      (contDiff_infty_iff_fderiv.mp hG).2.contDiffAt (by simp)
    have hnext : ‖iteratedFDeriv ℝ i (rootMiddleDerivative G) y‖ ≤
        ‖iteratedFDeriv ℝ (i + 1) G y‖ := by
      unfold rootMiddleDerivative
      simpa only [hv, one_mul, norm_iteratedFDeriv_fderiv] using h
    exact hnext.trans (hB (i + 1) (Nat.add_le_add_right hi 1) y hy)
  have hIntegrand : ContDiff ℝ ∞ (rootMiddleDerivative G ∘ A) := hMiddle.comp hA
  have hI : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ =>
      ∫ t in (-1 : ℝ)..1, (rootMiddleDerivative G ∘ A) (q, t)) :=
    contDiff_intervalIntegral_of_contDiff hIntegrand (-1) 1
  intro n hn q hq
  have hIntegrandBound : ∀ t ∈ uIcc (-1 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (rootMiddleDerivative G ∘ A) (q, t)‖ ≤ C * M := by
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htq : (q, t) ∈ rootSourceBox ×ˢ Icc (-1 : ℝ) 1 := ⟨hq, ht'⟩
    have hprod : |t * q.2.1| ≤ 1 := by
      rw [abs_mul]
      calc
        |t| * |q.2.1| ≤ 1 * 1 :=
          mul_le_mul (abs_le.mpr ht') (abs_le.mpr hq.2.1) (abs_nonneg _) (by norm_num)
        _ = 1 := one_mul _
    have hImage : A (q, t) ∈ rootSourceBox := ⟨hq.1, abs_le.mp hprod, hq.2.2⟩
    have hcomp := norm_iteratedFDeriv_comp_le hMiddle hA (by simp) (q, t)
      (C := M) (D := D)
      (fun i hi => hMiddleBound i (hi.trans hn) (A (q, t)) hImage)
      (fun i hi hin => hDjets i hi (hin.trans hn) (q, t) htq)
    calc
      _ ≤ (n.factorial : ℝ) * M * D ^ n := hcomp
      _ = ((n.factorial : ℝ) * D ^ n) * M := by ring
      _ ≤ C * M := mul_le_mul_of_nonneg_right (hcoeff n hn) hM
  have hIntegralBound := norm_iteratedFDeriv_intervalIntegral_le hIntegrand n (-1) 1 q
    (C * M) hIntegrandBound
  norm_num at hIntegralBound
  have hscale : iteratedFDeriv ℝ n (rootOddIntegral G) q =
      (1 / 2 : ℝ) • iteratedFDeriv ℝ n
        (fun q : ℝ × ℝ × ℝ => ∫ t in (-1 : ℝ)..1,
          (rootMiddleDerivative G ∘ A) (q, t)) q := by
    unfold rootOddIntegral
    simpa only [Function.comp_def, A, smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := (1 / 2 : ℝ))
        (hI.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)))
  rw [hscale, norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  calc
    _ ≤ (1 / 2 : ℝ) * ((C * M) * 2) :=
      mul_le_mul_of_nonneg_left hIntegralBound (by norm_num)
    _ = C * M := by ring

end ContinuousFlexibility.Statements
