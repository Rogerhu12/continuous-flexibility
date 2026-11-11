import ContinuousFlexibility.Analysis.DegenerateEnergy
import Mathlib.Tactic.GCongr

/-!
# The second stage of the positive-cylinder graph estimate

All functions are smooth enough for the ordinary integration-by-parts identities.
The vanishing weight supplies the boundary conditions, so none is imposed on the
original solution. This file uses the energy identities of `DegenerateEnergy`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set intervalIntegral

private theorem n06_three_square (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- The second derivative of the conjugated unknown, with all lower-order
terms displayed. -/
theorem n06_cylinder_conjugate_second_deriv {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (y : ℝ) :
    deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y =
      cylinderWeight y ^ 2 * deriv (deriv u) y +
        4 * cylinderWeight y * (1 - 2 * y) * deriv u y +
        (2 * (1 - 2 * y) ^ 2 - 4 * cylinderWeight y) * u y := by
  have hfirst : deriv (fun t => cylinderWeight t ^ 2 * u t) =
      fun t => 2 * cylinderWeight t * (1 - 2 * t) * u t +
        cylinderWeight t ^ 2 * deriv u t :=
    funext fun t => (hasDerivAt_cw_sq_mul hu t).deriv
  have hlin : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) y := by
    convert (((hasDerivAt_id' y).const_mul 2).const_sub 1) using 1 <;> ring
  have hleft := (((cylinderWeight_hasDerivAt y).const_mul 2).fun_mul hlin).fun_mul
    (hasDerivAt_of_contDiff_two hu y)
  have hright := (cylinderWeight_sq_hasDerivAt y).fun_mul
    (hasDerivAt_deriv_of_contDiff_two hu y)
  rw [hfirst, (hleft.fun_add hright).deriv]
  ring

/-- The square identity yields a coercive weighted estimate whenever the
potential coefficient dominates the vanishing cylinder weight. -/
theorem n06_dirichlet_weighted_square_bound {v q F₁ : ℝ → ℝ} {j α Q : ℝ}
    (hv : ContDiff ℝ 2 v) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hq : ContDiff ℝ 2 q) (hα : 0 ≤ α) (hQ : 0 ≤ Q)
    (hqlower : ∀ y ∈ Icc (0 : ℝ) 1, α * cylinderWeight y ≤ q y)
    (hqsecond : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ Q)
    (hF₁ : ∀ y, F₁ y = -deriv (deriv v) y + j ^ 2 * q y * v y) :
    (∫ y in (0 : ℝ)..1, deriv (deriv v) y ^ 2) +
        j ^ 4 * α ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * v y ^ 2) +
        2 * j ^ 2 * α * (∫ y in (0 : ℝ)..1, cylinderWeight y * deriv v y ^ 2) ≤
      (∫ y in (0 : ℝ)..1, F₁ y ^ 2) +
        j ^ 2 * Q * (∫ y in (0 : ℝ)..1, v y ^ 2) := by
  have hvc := hv.continuous
  have hvdc := (contDiff_deriv_of_two hv).continuous
  have hqc := hq.continuous
  have hqddc := (contDiff_deriv_of_two hq).continuous_deriv le_rfl
  have hdc := cylinderWeight_continuous
  have hid := dirichlet_square_identity hv hv0 hv1 hq hF₁
  have hpotential :
      α ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * v y ^ 2) ≤
        ∫ y in (0 : ℝ)..1, (q y * v y) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    have h0 := mul_nonneg hα (cylinderWeight_nonneg hy)
    have hs := pow_le_pow_left₀ h0 (hqlower y hy) 2
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (v y))
    nlinarith only [hm]
  have hgradient :
      α * (∫ y in (0 : ℝ)..1, cylinderWeight y * deriv v y ^ 2) ≤
        ∫ y in (0 : ℝ)..1, q y * deriv v y ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hqlower y hy) (sq_nonneg (deriv v y))
  have herror :
      (∫ y in (0 : ℝ)..1, deriv (deriv q) y * v y ^ 2) ≤
        Q * (∫ y in (0 : ℝ)..1, v y ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (hqsecond y hy)) (sq_nonneg _)
  have hp := mul_le_mul_of_nonneg_left hpotential (show 0 ≤ j ^ 4 by positivity)
  have hg := mul_le_mul_of_nonneg_left hgradient
    (show 0 ≤ 2 * j ^ 2 by positivity)
  have he := mul_le_mul_of_nonneg_left herror (sq_nonneg j)
  nlinarith only [hid, hp, hg, he]

/-- Pointwise control of the forcing in the conjugated normalized equation.
The constants are uniform in the frequency. -/
theorem n06_conjugated_forcing_square {K a a₁ V d e F w u G : ℝ}
    (hK : 1 ≤ K) (ha : 1 / K ≤ a) (ha' : a ≤ K)
    (ha₁ : |a₁| ≤ K) (hV : |V| ≤ K)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : e ^ 2 ≤ 1)
    (hG : a * G = d ^ 2 * F + (a₁ * d - 4 * a * e) * w +
      (a * (4 * d - 2 * e ^ 2) - V * d ^ 2) * u) :
    G ^ 2 ≤ 3 * K ^ 2 * F ^ 2 + 75 * K ^ 4 * w ^ 2 +
      147 * K ^ 4 * u ^ 2 := by
  have hKpos : 0 < K := by linarith
  have ha0 : 0 < a := (one_div_pos.mpr hKpos).trans_le ha
  have hea : |e| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (e + 1), sq_nonneg (e - 1)]
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hepart : |4 * d - 2 * e ^ 2| ≤ 6 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg e]
  have hcoef₁ : |a₁ * d - 4 * a * e| ≤ 5 * K := by
    calc
      |a₁ * d - 4 * a * e| ≤ |a₁ * d| + |4 * a * e| := abs_sub _ _
      _ = |a₁| * d + 4 * a * |e| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_pos ha0]
        norm_num
      _ ≤ K * 1 + 4 * K * 1 := by gcongr
      _ = 5 * K := by ring
  have hcoef₂ : |a * (4 * d - 2 * e ^ 2) - V * d ^ 2| ≤ 7 * K := by
    calc
      |a * (4 * d - 2 * e ^ 2) - V * d ^ 2| ≤
          |a * (4 * d - 2 * e ^ 2)| + |V * d ^ 2| := abs_sub _ _
      _ = a * |4 * d - 2 * e ^ 2| + |V| * d ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos ha0, abs_of_nonneg (sq_nonneg d)]
      _ ≤ K * 6 + K * 1 := by gcongr
      _ = 7 * K := by ring
  have hsum : |a * G| ≤ |F| + 5 * K * |w| + 7 * K * |u| := by
    rw [hG]
    calc
      |d ^ 2 * F + (a₁ * d - 4 * a * e) * w +
          (a * (4 * d - 2 * e ^ 2) - V * d ^ 2) * u| ≤
          |d ^ 2 * F| + |(a₁ * d - 4 * a * e) * w| +
            |(a * (4 * d - 2 * e ^ 2) - V * d ^ 2) * u| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ |F| + 5 * K * |w| + 7 * K * |u| := by
        have hx : |d ^ 2 * F| ≤ |F| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hd2 (abs_nonneg F)
        have hy : |(a₁ * d - 4 * a * e) * w| ≤ 5 * K * |w| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hcoef₁ (abs_nonneg w)
        have hz : |(a * (4 * d - 2 * e ^ 2) - V * d ^ 2) * u| ≤ 7 * K * |u| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hcoef₂ (abs_nonneg u)
        exact add_le_add (add_le_add hx hy) hz
  have hdiv : |G| ≤ K * (|F| + 5 * K * |w| + 7 * K * |u|) := by
    have hmul := mul_le_mul_of_nonneg_right ha (abs_nonneg G)
    have hcancel : K * (1 / K * |G|) = |G| := by
      field_simp [hKpos.ne']
    calc
      |G| = K * (1 / K * |G|) := hcancel.symm
      _ ≤ K * (a * |G|) := mul_le_mul_of_nonneg_left hmul hKpos.le
      _ = K * |a * G| := by rw [abs_mul, abs_of_pos ha0]
      _ ≤ K * (|F| + 5 * K * |w| + 7 * K * |u|) :=
        mul_le_mul_of_nonneg_left hsum hKpos.le
  have hsquare := pow_le_pow_left₀ (abs_nonneg G) hdiv 2
  have hthree := mul_le_mul_of_nonneg_left
    (n06_three_square |F| (5 * K * |w|) (7 * K * |u|)) (sq_nonneg K)
  simp only [mul_pow, sq_abs] at hsquare hthree
  nlinarith only [hsquare, hthree]

/-- The forcing after multiplication by the double vanishing weight is
controlled by the original forcing and the first weighted energy estimate. -/
theorem n06_conjugated_forcing_bound {a u c V q F F₁ : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u)
    (hc : Continuous c) (hV : Continuous V) (hq : Continuous q)
    (hF : ∀ y, F y = -deriv (fun t => a t * deriv u t) y +
      j ^ 2 * c y * u y + V y * u y)
    (hF₁ : ∀ y, F₁ y = -deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y +
      j ^ 2 * q y * (cylinderWeight y ^ 2 * u y))
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y) :
    (∫ y in (0 : ℝ)..1, F₁ y ^ 2) ≤
      1024 * K ^ 6 * ((∫ y in (0 : ℝ)..1, F y ^ 2) +
        ∫ y in (0 : ℝ)..1, u y ^ 2) := by
  have huc := hu.continuous
  have hudc := (contDiff_deriv_of_two hu).continuous
  have hdc := cylinderWeight_continuous
  have hFc := continuous_forcing ha hu hc hV hF
  have hd : ContDiff ℝ 2 cylinderWeight := by
    unfold cylinderWeight
    fun_prop
  have hv : ContDiff ℝ 2 (fun t => cylinderWeight t ^ 2 * u t) :=
    (hd.pow 2).mul hu
  have hvddc := (contDiff_deriv_of_two hv).continuous_deriv le_rfl
  have hF₁c : Continuous F₁ := by
    have heq := funext hF₁
    rw [heq]
    fun_prop
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      F₁ y ^ 2 ≤ 3 * K ^ 2 * F y ^ 2 +
        75 * K ^ 4 * (cylinderWeight y * deriv u y) ^ 2 +
        147 * K ^ 4 * u y ^ 2 := by
    apply n06_conjugated_forcing_square hK (ha₁ y hy) (ha₂ y hy)
      (ha₃ y hy) (hV₁ y hy) (cylinderWeight_nonneg hy)
      (cylinderWeight_le_one hy) (one_sub_two_mul_sq_le_one hy)
    have haderiv : deriv (fun t => a t * deriv u t) y =
        deriv a y * deriv u y + a y * deriv (deriv u) y :=
      ((hasDerivAt_of_contDiff_one ha y).fun_mul
        (hasDerivAt_deriv_of_contDiff_two hu y)).deriv
    rw [hF₁ y, n06_cylinder_conjugate_second_deriv hu y, hF y, haderiv, hqa y hy]
    ring
  have hint : (∫ y in (0 : ℝ)..1, F₁ y ^ 2) ≤
      ∫ y in (0 : ℝ)..1, (3 * K ^ 2 * F y ^ 2 +
        75 * K ^ 4 * (cylinderWeight y * deriv u y) ^ 2 +
        147 * K ^ 4 * u y ^ 2) :=
    intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) hpoint
  have hlin : (∫ y in (0 : ℝ)..1, (3 * K ^ 2 * F y ^ 2 +
        75 * K ^ 4 * (cylinderWeight y * deriv u y) ^ 2 +
        147 * K ^ 4 * u y ^ 2)) =
      3 * K ^ 2 * (∫ y in (0 : ℝ)..1, F y ^ 2) +
        75 * K ^ 4 * (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2) +
        147 * K ^ 4 * (∫ y in (0 : ℝ)..1, u y ^ 2) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hlin] at hint
  have hgrad := degenerate_gradient_bound ha hu hc hV hF hK ha₁ ha₂ hc₁ hV₁
  have hFn : 0 ≤ ∫ y in (0 : ℝ)..1, F y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hUn : 0 ≤ ∫ y in (0 : ℝ)..1, u y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hK26 : K ^ 2 ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  have hK46 : K ^ 4 ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  have hfirst := mul_le_mul_of_nonneg_right hK26 hFn
  have hlast := mul_le_mul_of_nonneg_right hK46 hUn
  have hmiddle := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 75 * K ^ 4 by positivity)
  have hKF := mul_nonneg (show 0 ≤ K ^ 6 by positivity) hFn
  have hKU := mul_nonneg (show 0 ≤ K ^ 6 by positivity) hUn
  nlinarith only [hint, hfirst, hlast, hmiddle, hKF, hKU]

/-- The normalized coefficient retains a quantitative linear degeneracy. -/
theorem n06_normalized_coefficient_lower {K a c q d : ℝ}
    (hK : 1 ≤ K) (ha₁ : 1 / K ≤ a) (ha₂ : a ≤ K)
    (hd : 0 ≤ d) (hc : d / K ≤ c) (hqa : c = a * q) :
    d / K ^ 2 ≤ q := by
  have hKpos : 0 < K := by linarith
  have hapos : 0 < a := (one_div_pos.mpr hKpos).trans_le ha₁
  have hc0 : 0 ≤ c := (div_nonneg hd hKpos.le).trans hc
  have hq0 : 0 ≤ q := by
    by_contra h
    have hneg := mul_neg_of_pos_of_neg hapos (lt_of_not_ge h)
    rw [← hqa] at hneg
    exact (not_lt_of_ge hc0) hneg
  have hdc := (div_le_iff₀ hKpos).mp hc
  rw [hqa] at hdc
  have hmul := mul_le_mul_of_nonneg_right ha₂ (mul_nonneg hq0 hKpos.le)
  apply (div_le_iff₀ (sq_pos_of_pos hKpos)).mpr
  nlinarith only [hdc, hmul]

/-- The full second-stage energy estimate for the conjugated unknown.
Its boundary values vanish automatically, regardless of the values of `u`. -/
theorem n06_conjugate_energy_bound {a u c V q F : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u)
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ y, F y = -deriv (fun t => a t * deriv u t) y +
      j ^ 2 * c y * u y + V y * u y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    let v := fun y => cylinderWeight y ^ 2 * u y
    (∫ y in (0 : ℝ)..1, deriv (deriv v) y ^ 2) +
        j ^ 4 * (1 / K ^ 2) ^ 2 *
          (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * v y ^ 2) +
        2 * j ^ 2 * (1 / K ^ 2) *
          (∫ y in (0 : ℝ)..1, cylinderWeight y * deriv v y ^ 2) ≤
      2048 * K ^ 6 * ((∫ y in (0 : ℝ)..1, F y ^ 2) +
        ∫ y in (0 : ℝ)..1, u y ^ 2) := by
  let v : ℝ → ℝ := fun y => cylinderWeight y ^ 2 * u y
  let F₁ : ℝ → ℝ := fun y => -deriv (deriv v) y + j ^ 2 * q y * v y
  have hKpos : 0 < K := by linarith
  have hq₁ (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      cylinderWeight y / K ^ 2 ≤ q y :=
    n06_normalized_coefficient_lower hK (ha₁ y hy) (ha₂ y hy)
      (cylinderWeight_nonneg hy) (hc₁ y hy) (hqa y hy)
  have huc := hu.continuous
  have hdc := cylinderWeight_continuous
  have hd : ContDiff ℝ 2 cylinderWeight := by
    unfold cylinderWeight
    fun_prop
  have hv : ContDiff ℝ 2 v := (hd.pow 2).mul hu
  have hv0 : v 0 = 0 := by simp [v]
  have hv1 : v 1 = 0 := by simp [v]
  have hvlow : (∫ y in (0 : ℝ)..1, v y ^ 2) ≤
      ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2 := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by dsimp [v]; fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro y hy
    have hd0 := cylinderWeight_nonneg hy
    have hd1 := cylinderWeight_le_one hy
    have hp := mul_le_mul_of_nonneg_right hd1 (pow_nonneg hd0 3)
    have hp' : cylinderWeight y ^ 4 ≤ cylinderWeight y ^ 3 := by nlinarith only [hp]
    have hm := mul_le_mul_of_nonneg_right hp' (sq_nonneg (u y))
    dsimp [v]
    nlinarith only [hm]
  have hfirst := degenerate_energy_bound ha hu hc hV hF hK ha₁ ha₂ hc₁ hV₁
  have hfirst_nonneg : 0 ≤
      ∫ y in (0 : ℝ)..1, (deriv (fun t => cylinderWeight t * u t) y) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hlow : j ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2) ≤
      3 * K ^ 2 * ((∫ y in (0 : ℝ)..1, F y ^ 2) +
        ∫ y in (0 : ℝ)..1, u y ^ 2) := by linarith only [hfirst, hfirst_nonneg]
  have hforcing := n06_conjugated_forcing_bound ha hu hc hV hq.continuous hF
    (F₁ := F₁) (fun _ => rfl) hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa
  have henergy := n06_dirichlet_weighted_square_bound hv hv0 hv1 hq
    (show 0 ≤ 1 / K ^ 2 by positivity) hKpos.le
    (fun y hy => by simpa only [one_div, div_eq_mul_inv, mul_comm] using hq₁ y hy)
    hq₂ (F₁ := F₁) (fun _ => rfl)
  have hsmall := mul_le_mul_of_nonneg_left hvlow
    (show 0 ≤ j ^ 2 * K by positivity)
  have hlowK := mul_le_mul_of_nonneg_left hlow hKpos.le
  have hFn : 0 ≤ ∫ y in (0 : ℝ)..1, F y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hUn : 0 ≤ ∫ y in (0 : ℝ)..1, u y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hK36 : K ^ 3 ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  have hpower := mul_le_mul_of_nonneg_right hK36 (add_nonneg hFn hUn)
  have hnonneg := mul_nonneg (show 0 ≤ K ^ 6 by positivity) (add_nonneg hFn hUn)
  change (∫ y in (0 : ℝ)..1, deriv (deriv v) y ^ 2) +
      j ^ 4 * (1 / K ^ 2) ^ 2 *
        (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * v y ^ 2) +
      2 * j ^ 2 * (1 / K ^ 2) *
        (∫ y in (0 : ℝ)..1, cylinderWeight y * deriv v y ^ 2) ≤ _
  nlinarith only [henergy, hforcing, hsmall, hlowK, hpower, hnonneg]

/-- Passing from the second derivative of `d²u` to the weighted second
derivative of `u` costs only the first weighted energy. -/
theorem n06_second_derivative_transfer {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) :
    (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv u) y) ^ 2) ≤
      3 * (∫ y in (0 : ℝ)..1,
        deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y ^ 2) +
      48 * (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2) +
      108 * (∫ y in (0 : ℝ)..1, u y ^ 2) := by
  have huc := hu.continuous
  have hudc := (contDiff_deriv_of_two hu).continuous
  have hudd := (contDiff_deriv_of_two hu).continuous_deriv le_rfl
  have hdc := cylinderWeight_continuous
  have hd : ContDiff ℝ 2 cylinderWeight := by
    unfold cylinderWeight
    fun_prop
  have hv : ContDiff ℝ 2 (fun t => cylinderWeight t ^ 2 * u t) := (hd.pow 2).mul hu
  have hvdd := (contDiff_deriv_of_two hv).continuous_deriv le_rfl
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      (cylinderWeight y ^ 2 * deriv (deriv u) y) ^ 2 ≤
        3 * deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y ^ 2 +
        48 * (cylinderWeight y * deriv u y) ^ 2 + 108 * u y ^ 2 := by
    have he := one_sub_two_mul_sq_le_one hy
    have hd0 := cylinderWeight_nonneg hy
    have hd1 := cylinderWeight_le_one hy
    have hcoef : |2 * (1 - 2 * y) ^ 2 - 4 * cylinderWeight y| ≤ 6 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (1 - 2 * y)]
    have hcoefsq := pow_le_pow_left₀
      (abs_nonneg (2 * (1 - 2 * y) ^ 2 - 4 * cylinderWeight y)) hcoef 2
    rw [sq_abs] at hcoefsq
    have hterm₁ := mul_le_mul_of_nonneg_right he
      (show 0 ≤ 16 * (cylinderWeight y * deriv u y) ^ 2 by positivity)
    have hterm₂ := mul_le_mul_of_nonneg_right hcoefsq (sq_nonneg (u y))
    have hthree := n06_three_square
      (deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y)
      (-4 * cylinderWeight y * (1 - 2 * y) * deriv u y)
      (-(2 * (1 - 2 * y) ^ 2 - 4 * cylinderWeight y) * u y)
    rw [n06_cylinder_conjugate_second_deriv hu y] at hthree ⊢
    nlinarith only [hterm₁, hterm₂, hthree]
  have hint := intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (show Continuous (fun y =>
      (cylinderWeight y ^ 2 * deriv (deriv u) y) ^ 2) by fun_prop) 0 1)
    (Continuous.intervalIntegrable (show Continuous (fun y =>
      3 * deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y ^ 2 +
        48 * (cylinderWeight y * deriv u y) ^ 2 + 108 * u y ^ 2) by fun_prop) 0 1)
    hpoint
  have hlin : (∫ y in (0 : ℝ)..1,
      (3 * deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y ^ 2 +
        48 * (cylinderWeight y * deriv u y) ^ 2 + 108 * u y ^ 2)) =
      3 * (∫ y in (0 : ℝ)..1,
        deriv (deriv (fun t => cylinderWeight t ^ 2 * u t)) y ^ 2) +
      48 * (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2) +
      108 * (∫ y in (0 : ℝ)..1, u y ^ 2) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  exact hint.trans_eq hlin

/-- Passing from the first derivative of `d²u` to the mixed weighted
derivative of `u`. -/
theorem n06_mixed_derivative_transfer {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) :
    (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv u y ^ 2) ≤
      2 * (∫ y in (0 : ℝ)..1,
        cylinderWeight y * deriv (fun t => cylinderWeight t ^ 2 * u t) y ^ 2) +
      8 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2) := by
  have huc := hu.continuous
  have hudc := (contDiff_deriv_of_two hu).continuous
  have hdc := cylinderWeight_continuous
  have hd : ContDiff ℝ 2 cylinderWeight := by
    unfold cylinderWeight
    fun_prop
  have hv : ContDiff ℝ 2 (fun t => cylinderWeight t ^ 2 * u t) := (hd.pow 2).mul hu
  have hvdc := (contDiff_deriv_of_two hv).continuous
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      cylinderWeight y ^ 5 * deriv u y ^ 2 ≤
        2 * cylinderWeight y * deriv (fun t => cylinderWeight t ^ 2 * u t) y ^ 2 +
        8 * cylinderWeight y ^ 3 * u y ^ 2 := by
    have hd0 := cylinderWeight_nonneg hy
    have he := one_sub_two_mul_sq_le_one hy
    have hs : (cylinderWeight y ^ 2 * deriv u y) ^ 2 ≤
        2 * (2 * cylinderWeight y * (1 - 2 * y) * u y +
          cylinderWeight y ^ 2 * deriv u y) ^ 2 +
        2 * (2 * cylinderWeight y * (1 - 2 * y) * u y) ^ 2 := by
      nlinarith only [sq_nonneg (4 * cylinderWeight y * (1 - 2 * y) * u y +
        cylinderWeight y ^ 2 * deriv u y)]
    have hs' := mul_le_mul_of_nonneg_left hs hd0
    have he' := mul_le_mul_of_nonneg_right he
      (show 0 ≤ 8 * cylinderWeight y ^ 3 * u y ^ 2 by positivity)
    rw [(hasDerivAt_cw_sq_mul hu y).deriv]
    nlinarith only [hs', he']
  have hint := intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (show Continuous (fun y =>
      cylinderWeight y ^ 5 * deriv u y ^ 2) by fun_prop) 0 1)
    (Continuous.intervalIntegrable (show Continuous (fun y =>
      2 * cylinderWeight y * deriv (fun t => cylinderWeight t ^ 2 * u t) y ^ 2 +
        8 * cylinderWeight y ^ 3 * u y ^ 2) by fun_prop) 0 1) hpoint
  have hlin : (∫ y in (0 : ℝ)..1,
      (2 * cylinderWeight y * deriv (fun t => cylinderWeight t ^ 2 * u t) y ^ 2 +
        8 * cylinderWeight y ^ 3 * u y ^ 2)) =
      2 * (∫ y in (0 : ℝ)..1,
        cylinderWeight y * deriv (fun t => cylinderWeight t ^ 2 * u t) y ^ 2) +
      8 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2) := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  exact hint.trans_eq hlin

/-- Increasing a nonnegative power of the cylinder weight only decreases
the weighted square integral. -/
theorem n06_cylinder_power_integral_mono {f : ℝ → ℝ} (hf : Continuous f)
    {p q : ℕ} (hpq : p ≤ q) :
    (∫ y in (0 : ℝ)..1, cylinderWeight y ^ q * f y ^ 2) ≤
      ∫ y in (0 : ℝ)..1, cylinderWeight y ^ p * f y ^ 2 := by
  have hd := cylinderWeight_continuous
  refine intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
  intro y hy
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  have hsmall : cylinderWeight y ^ r ≤ 1 :=
    pow_le_one₀ (cylinderWeight_nonneg hy) (cylinderWeight_le_one hy)
  have hp := mul_le_mul_of_nonneg_left hsmall
    (pow_nonneg (cylinderWeight_nonneg hy) p)
  have h := mul_le_mul_of_nonneg_right hp (sq_nonneg (f y))
  simpa only [pow_add, mul_one] using h

/-- The smooth positive-cylinder graph estimate with arbitrary endpoint
values. This squared form is uniform in the real frequency `j`; it controls
all five weights used by the Fourier multiplier argument in Section 8. -/
theorem n06_smooth_cubic_graph_bound {a u c V q F : ℝ → ℝ} {j K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ContDiff ℝ 2 u)
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ y, F y = -deriv (fun t => a t * deriv u t) y +
      j ^ 2 * c y * u y + V y * u y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2) +
      (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2) +
      (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv u) y) ^ 2) +
      (1 + j ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * u y ^ 2) +
      (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv u y ^ 2) ≤
      16384 * K ^ 10 * ((∫ y in (0 : ℝ)..1, F y ^ 2) +
        ∫ y in (0 : ℝ)..1, u y ^ 2) := by
  let v : ℝ → ℝ := fun y => cylinderWeight y ^ 2 * u y
  let E : ℝ := (∫ y in (0 : ℝ)..1, F y ^ 2) + ∫ y in (0 : ℝ)..1, u y ^ 2
  let R : ℝ := K ^ 10 * E
  let A : ℝ := ∫ y in (0 : ℝ)..1, deriv (deriv v) y ^ 2
  let B : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * u y ^ 2
  let C : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y * deriv v y ^ 2
  let G : ℝ := ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv u y) ^ 2
  let L : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * u y ^ 2
  let U : ℝ := ∫ y in (0 : ℝ)..1, u y ^ 2
  let D : ℝ := ∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv u) y) ^ 2
  let J : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv u y ^ 2
  have hKpos : 0 < K := by linarith
  have hKne : K ≠ 0 := hKpos.ne'
  have hFn : 0 ≤ ∫ y in (0 : ℝ)..1, F y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hUn : 0 ≤ U :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hEn : 0 ≤ E := add_nonneg hFn hUn
  have hRn : 0 ≤ R := mul_nonneg (by positivity) hEn
  have hAn : 0 ≤ A :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hBn : 0 ≤ B :=
    intervalIntegral.integral_nonneg zero_le_one (fun y hy =>
      mul_nonneg (pow_nonneg (cylinderWeight_nonneg hy) 6) (sq_nonneg _))
  have hCn : 0 ≤ C :=
    intervalIntegral.integral_nonneg zero_le_one (fun y hy =>
      mul_nonneg (cylinderWeight_nonneg hy) (sq_nonneg _))
  have hG := degenerate_gradient_bound ha hu hc hV hF hK ha₁ ha₂ hc₁ hV₁
  have hlow := degenerate_energy_bound ha hu hc hV hF hK ha₁ ha₂ hc₁ hV₁
  have hlow0 : 0 ≤
      ∫ y in (0 : ℝ)..1, (deriv (fun t => cylinderWeight t * u t) y) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hL : j ^ 2 * L ≤ 3 * K ^ 2 * E := by
    dsimp [L, E]
    linarith only [hlow, hlow0]
  have hmain := n06_conjugate_energy_bound ha hu hc hV hq hF hK
    ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  have hBchange : (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * v y ^ 2) = B := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [v]
    ring
  change A + j ^ 4 * (1 / K ^ 2) ^ 2 *
      (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * v y ^ 2) +
      2 * j ^ 2 * (1 / K ^ 2) * C ≤ 2048 * K ^ 6 * E at hmain
  rw [hBchange] at hmain
  have hBterm : 0 ≤ j ^ 4 * (1 / K ^ 2) ^ 2 * B := by positivity
  have hCterm : 0 ≤ 2 * j ^ 2 * (1 / K ^ 2) * C := by positivity
  have hA : A ≤ 2048 * K ^ 6 * E := by linarith only [hmain, hBterm, hCterm]
  have hBsmall : j ^ 4 * (1 / K ^ 2) ^ 2 * B ≤ 2048 * K ^ 6 * E := by
    linarith only [hmain, hAn, hCterm]
  have hB : j ^ 4 * B ≤ 2048 * R := by
    have h := mul_le_mul_of_nonneg_left hBsmall (show 0 ≤ K ^ 4 by positivity)
    have hcancel : K ^ 4 * (j ^ 4 * (1 / K ^ 2) ^ 2 * B) = j ^ 4 * B := by
      field_simp [hKne]
      <;> ring
    rw [hcancel] at h
    dsimp [R]
    nlinarith only [h]
  have hCsmall : 2 * j ^ 2 * (1 / K ^ 2) * C ≤ 2048 * K ^ 6 * E := by
    linarith only [hmain, hAn, hBterm]
  have hC : j ^ 2 * C ≤ 1024 * K ^ 8 * E := by
    have h := mul_le_mul_of_nonneg_left hCsmall (show 0 ≤ K ^ 2 by positivity)
    have hcancel : K ^ 2 * (2 * j ^ 2 * (1 / K ^ 2) * C) = 2 * j ^ 2 * C := by
      field_simp [hKne]
      <;> ring
    rw [hcancel] at h
    nlinarith only [h]
  have h210 := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hK (by norm_num : 2 ≤ 10)) hEn
  have h610 := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hK (by norm_num : 6 ≤ 10)) hEn
  have h810 := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hK (by norm_num : 8 ≤ 10)) hEn
  have h010 := mul_le_mul_of_nonneg_right
    (show 1 ≤ K ^ 10 from one_le_pow₀ hK) hEn
  have hUR : U ≤ R := by
    have hUE : U ≤ E := by dsimp [E]; linarith only [hFn]
    dsimp [R]
    linarith only [hUE, h010]
  have hGR : G ≤ 8 * R := by
    change G ≤ 8 * K ^ 2 * E at hG
    dsimp [R]
    linarith only [hG, h210]
  have hLR : j ^ 2 * L ≤ 3 * R := by
    dsimp [R]
    linarith only [hL, h210]
  have hAR : A ≤ 2048 * R := by
    dsimp [R]
    linarith only [hA, h610]
  have hCR : j ^ 2 * C ≤ 1024 * R := by
    dsimp [R]
    linarith only [hC, h810]
  have hD := n06_second_derivative_transfer hu
  change D ≤ 3 * A + 48 * G + 108 * U at hD
  have hDR : D ≤ 6636 * R := by linarith only [hD, hAR, hGR, hUR]
  have hJ := n06_mixed_derivative_transfer hu
  change J ≤ 2 * C + 8 * L at hJ
  have hJmul := mul_le_mul_of_nonneg_left hJ (sq_nonneg j)
  have hJR : j ^ 2 * J ≤ 2072 * R := by
    nlinarith only [hJmul, hCR, hLR]
  have hLU : L ≤ U := by
    simpa only [pow_zero, one_mul] using
      (n06_cylinder_power_integral_mono hu.continuous (p := 0) (q := 3) (by omega))
  have hBL : B ≤ L :=
    n06_cylinder_power_integral_mono hu.continuous (p := 3) (q := 6) (by omega)
  have hBLmul := mul_le_mul_of_nonneg_left hBL (sq_nonneg j)
  have hJG : J ≤ G := by
    have h := n06_cylinder_power_integral_mono
      (contDiff_deriv_of_two hu).continuous (p := 2) (q := 5) (by omega)
    have heq : (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 2 * deriv u y ^ 2) = G := by
      apply intervalIntegral.integral_congr
      intro y _
      ring
    exact h.trans_eq heq
  change G + (1 + j ^ 2) * L + D + (1 + j ^ 2) ^ 2 * B +
      (1 + j ^ 2) * J ≤ 16384 * R
  nlinarith only [hRn, hUR, hGR, hLR, hDR, hJR, hB, hLU, hBL, hBLmul, hJG]

end ContinuousFlexibility.Analysis

