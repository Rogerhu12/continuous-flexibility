module

public import ContinuousFlexibility.Analysis.N05OpticalRootQuotient
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# First derivative bounds for an optical root coordinate

The derivative of the actual principal-symbol identity is combined with
the regular root average. Both apparent inverse-distance terms have
numerators of order the root distance. No estimate for the second
coordinate derivative is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

def n05OpticalRootAverage (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  3 * ∫ t in (0 : ℝ)..1, t ^ 2 * Real.sqrt (g (t ^ 2 * x))

theorem n05_optical_unit_sq_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ^ 2 ∈ Icc (0 : ℝ) 1 := by
  exact ⟨sq_nonneg _, by nlinarith only [ht.1, ht.2]⟩

theorem n05OpticalRootAverage_integrable {g : ℝ → ℝ} {a x : ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) a)) (hx : x ∈ Icc (0 : ℝ) a) :
    IntervalIntegrable (fun t => t ^ 2 * Real.sqrt (g (t ^ 2 * x))) volume 0 1 := by
  have hc : ContinuousOn (fun t => g (t ^ 2 * x)) (Icc (0 : ℝ) 1) :=
    hg.comp ((continuous_id.pow 2).mul continuous_const).continuousOn
      (fun t ht => n05_optical_unit_mul_mem hx (n05_optical_unit_sq_mem ht))
  exact ((continuous_id.pow 2).continuousOn.mul
    (Real.continuous_sqrt.comp_continuousOn hc)).intervalIntegrable_of_Icc zero_le_one

theorem n05_optical_root_average_constant (c : ℝ) :
    3 * (∫ t in (0 : ℝ)..1, t ^ 2 * c) = c := by
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num <;> ring

theorem n05OpticalRootAverage_bounds {g : ℝ → ℝ} {a x κ B : ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) a))
    (hbound : ∀ y ∈ Icc (0 : ℝ) a, κ ≤ g y ∧ g y ≤ B)
    (hx : x ∈ Icc (0 : ℝ) a) :
    Real.sqrt κ ≤ n05OpticalRootAverage g x ∧
      n05OpticalRootAverage g x ≤ Real.sqrt B := by
  have hi := n05OpticalRootAverage_integrable hg hx
  have hiConst (c : ℝ) : IntervalIntegrable (fun t : ℝ => t ^ 2 * c) volume 0 1 :=
    ((continuous_id.pow 2).mul continuous_const).intervalIntegrable 0 1
  have hl := intervalIntegral.integral_mono_on zero_le_one (hiConst (Real.sqrt κ)) hi
    (fun t ht => mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hbound (t ^ 2 * x)
        (n05_optical_unit_mul_mem hx (n05_optical_unit_sq_mem ht))).1) (sq_nonneg t))
  have hu := intervalIntegral.integral_mono_on zero_le_one hi (hiConst (Real.sqrt B))
    (fun t ht => mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hbound (t ^ 2 * x)
        (n05_optical_unit_mul_mem hx (n05_optical_unit_sq_mem ht))).2) (sq_nonneg t))
  constructor
  · simpa only [n05OpticalRootAverage, n05_optical_root_average_constant] using
      mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 3)
  · simpa only [n05OpticalRootAverage, n05_optical_root_average_constant] using
      mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 3)

/-- On a positive interval the square-root difference is controlled by
the original difference and the common lower bound. -/
theorem n05_optical_sqrt_sub_le {κ u v : ℝ} (hκ : 0 < κ)
    (hu : κ ≤ u) (hv : κ ≤ v) :
    |Real.sqrt u - Real.sqrt v| ≤ |u - v| / (2 * Real.sqrt κ) := by
  have hsum : 2 * Real.sqrt κ ≤ Real.sqrt u + Real.sqrt v := by
    linarith only [Real.sqrt_le_sqrt hu, Real.sqrt_le_sqrt hv]
  have he : (Real.sqrt u - Real.sqrt v) * (Real.sqrt u + Real.sqrt v) = u - v := by
    nlinarith only [Real.sq_sqrt (hκ.le.trans hu), Real.sq_sqrt (hκ.le.trans hv)]
  have habs : |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) = |u - v| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)),
      ← abs_mul, he]
  apply (le_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hκ))).mpr
  calc
    _ ≤ |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := habs

/-- The average differs from the square root at its outer endpoint by
`O(x)`. This is the cancellation estimate used for the actual `q'`. -/
theorem n05OpticalRootAverage_sub_sqrt_le {g : ℝ → ℝ} {a x κ : ℝ} {M : NNReal}
    (hκ : 0 < κ) (hg : LipschitzOnWith M g (Icc (0 : ℝ) a))
    (hlower : ∀ y ∈ Icc (0 : ℝ) a, κ ≤ g y)
    (hx : x ∈ Icc (0 : ℝ) a) :
    |n05OpticalRootAverage g x - Real.sqrt (g x)| ≤
      (M : ℝ) * x / (2 * Real.sqrt κ) := by
  have hi := n05OpticalRootAverage_integrable hg.continuousOn hx
  have hic : IntervalIntegrable (fun t : ℝ => t ^ 2 * Real.sqrt (g x)) volume 0 1 :=
    ((continuous_id.pow 2).mul continuous_const).intervalIntegrable 0 1
  have hid : IntervalIntegrable
      (fun t : ℝ => t ^ 2 * (Real.sqrt (g (t ^ 2 * x)) - Real.sqrt (g x))) volume 0 1 := by
    convert hi.sub hic using 1
    funext t
    ring
  have he : n05OpticalRootAverage g x - Real.sqrt (g x) =
      3 * ∫ t in (0 : ℝ)..1,
        t ^ 2 * (Real.sqrt (g (t ^ 2 * x)) - Real.sqrt (g x)) := by
    calc
      _ = 3 * (∫ t in (0 : ℝ)..1, t ^ 2 * Real.sqrt (g (t ^ 2 * x))) -
          3 * (∫ t in (0 : ℝ)..1, t ^ 2 * Real.sqrt (g x)) := by
        rw [n05_optical_root_average_constant]
        rfl
      _ = _ := by
        rw [← mul_sub, ← intervalIntegral.integral_sub hi hic]
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        ring
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |t ^ 2 * (Real.sqrt (g (t ^ 2 * x)) - Real.sqrt (g x))| ≤
        t ^ 2 * ((M : ℝ) * x / (2 * Real.sqrt κ)) := by
    have ht2 := n05_optical_unit_sq_mem ht
    have htx := n05_optical_unit_mul_mem hx ht2
    have hdist := hg.dist_le_mul (t ^ 2 * x) htx x hx
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (t ^ 2 * x) x,
      abs_of_nonneg (by nlinarith only [ht2.2, hx.1] : 0 ≤ x - t ^ 2 * x)] at hdist
    have hd : |g (t ^ 2 * x) - g x| ≤ (M : ℝ) * x :=
      hdist.trans (mul_le_mul_of_nonneg_left
        (by nlinarith only [mul_nonneg ht2.1 hx.1] : x - t ^ 2 * x ≤ x) M.coe_nonneg)
    have hs := (n05_optical_sqrt_sub_le hκ (hlower _ htx) (hlower _ hx)).trans
      (div_le_div_of_nonneg_right hd (by positivity))
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  have hmajor : IntervalIntegrable
      (fun t : ℝ => t ^ 2 * ((M : ℝ) * x / (2 * Real.sqrt κ))) volume 0 1 :=
    ((continuous_id.pow 2).mul continuous_const).intervalIntegrable 0 1
  have hb := (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    (intervalIntegral.integral_mono_on zero_le_one hid.abs hmajor hp)
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
    (n05_optical_root_average_constant _)

/-- Squaring the integration parameter removes the endpoint square root
without changing the actual optical integral. -/
theorem n05OpticalRootAverage_time {F g : ℝ → ℝ} {a x : ℝ}
    (hF : ContinuousOn F (Icc (0 : ℝ) a))
    (hg : ContinuousOn g (Icc (0 : ℝ) a))
    (hfactor : ∀ y ∈ Icc (0 : ℝ) a, F y = y * g y)
    (hx : x ∈ Icc (0 : ℝ) a) :
    (∫ y in (0 : ℝ)..x, Real.sqrt (F y)) =
      (2 / 3 : ℝ) * x * Real.sqrt x * n05OpticalRootAverage g x := by
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x * t ^ 2 ∈ Icc (0 : ℝ) a := by
    simpa only [mul_comm x] using n05_optical_unit_mul_mem hx (n05_optical_unit_sq_mem ht)
  have hchange : (∫ t in (0 : ℝ)..1,
      Real.sqrt (F (x * t ^ 2)) * (2 * x * t)) =
      ∫ y in (0 : ℝ)..x, Real.sqrt (F y) := by
    have hh := intervalIntegral.integral_comp_mul_deriv'
      (f := fun t : ℝ => x * t ^ 2) (f' := fun t => 2 * x * t)
      (g := fun y => Real.sqrt (F y)) (a := (0 : ℝ)) (b := 1)
      (fun t _ => by
        convert (hasDerivAt_pow 2 t).const_mul x using 1 <;> norm_num <;> ring)
      (by fun_prop) ?_
    · simpa only [Function.comp_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
        one_pow, mul_zero, mul_one] using hh
    · apply (Real.continuous_sqrt.comp_continuousOn hF).mono
      rintro y ⟨t, ht, rfl⟩
      rw [uIcc_of_le zero_le_one] at ht
      exact hmap t ht
  have he : (∫ t in (0 : ℝ)..1,
      Real.sqrt (F (x * t ^ 2)) * (2 * x * t)) =
      (2 * x * Real.sqrt x) *
        ∫ t in (0 : ℝ)..1, t ^ 2 * Real.sqrt (g (t ^ 2 * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    change Real.sqrt (F (x * t ^ 2)) * (2 * x * t) =
      (2 * x * Real.sqrt x) * (t ^ 2 * Real.sqrt (g (t ^ 2 * x)))
    rw [hfactor _ (hmap t ht), Real.sqrt_mul (mul_nonneg hx.1 (sq_nonneg t)),
      Real.sqrt_mul hx.1, Real.sqrt_sq ht.1]
    simp only [mul_comm x (t ^ 2)]
    ring
  rw [← hchange, he, n05OpticalRootAverage]
  ring

/-- The exact time and principal-symbol identities imply a cubic
identity for the actual positive root derivative. -/
theorem n05_optical_root_cubic_identity {x ξ q g A : ℝ}
    (hx : 0 < x) (hξ : 0 < ξ) (hq : 0 < q) (hg : 0 ≤ g)
    (hsymbol : ξ * q ^ 2 = x * g)
    (htime : ξ * Real.sqrt ξ = x * Real.sqrt x * A) :
    q ^ 3 * A = g * Real.sqrt g := by
  have hs := congrArg Real.sqrt hsymbol
  rw [Real.sqrt_mul hξ.le, Real.sqrt_sq hq.le, Real.sqrt_mul hx.le] at hs
  have hm : (x * Real.sqrt x) * (q ^ 3 * A) =
      (x * Real.sqrt x) * (g * Real.sqrt g) := by
    calc
      _ = (ξ * Real.sqrt ξ) * q ^ 3 := by rw [htime]; ring
      _ = (ξ * q ^ 2) * (Real.sqrt ξ * q) := by ring
      _ = (x * g) * (Real.sqrt x * Real.sqrt g) := by rw [hsymbol, hs]
      _ = _ := by ring
  exact mul_left_cancel₀ (mul_ne_zero hx.ne' (Real.sqrt_pos.mpr hx).ne') hm

theorem n05_optical_sqrt_envelope {P g : ℝ} (hP : 1 ≤ P)
    (hg : 1 / P ≤ g ∧ g ≤ P) :
    1 / P ≤ Real.sqrt g ∧ Real.sqrt g ≤ P := by
  have hp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hi : 0 ≤ 1 / P := by positivity
  have hi1 : 1 / P ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hP)
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith only [mul_nonneg hi (sub_nonneg.mpr hi1), hg.1]
  · apply (Real.sqrt_le_left hp.le).mpr
    nlinarith only [hg.2, hP, sq_nonneg (P - 1)]

/-- A coarse reciprocal envelope uses only integer powers. -/
theorem n05_optical_root_cubic_bounds {P q g A : ℝ}
    (hP : 1 ≤ P) (hq : 0 < q)
    (hg : 1 / P ≤ g ∧ g ≤ P) (hA : 1 / P ≤ A ∧ A ≤ P)
    (hcubic : q ^ 3 * A = g * Real.sqrt g) :
    1 / P ≤ q ∧ q ≤ P := by
  have hp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hi : 0 ≤ 1 / P := by positivity
  have hs := n05_optical_sqrt_envelope hP hg
  have hu : g * Real.sqrt g ≤ P ^ 2 := by
    simpa only [pow_two] using mul_le_mul hg.2 hs.2 (Real.sqrt_nonneg _) hp.le
  have hl : (1 / P) ^ 2 ≤ g * Real.sqrt g := by
    simpa only [pow_two] using mul_le_mul hg.1 hs.1 hi (hi.trans hg.1)
  have hPA : 1 ≤ A * P := (div_le_iff₀ hp).mp hA.1
  have hqu : q ^ 3 ≤ P ^ 3 := by
    calc
      q ^ 3 = q ^ 3 * 1 := (mul_one _).symm
      _ ≤ q ^ 3 * (A * P) := mul_le_mul_of_nonneg_left hPA (pow_nonneg hq.le 3)
      _ = (g * Real.sqrt g) * P := by rw [← mul_assoc, hcubic]
      _ ≤ P ^ 2 * P := mul_le_mul_of_nonneg_right hu hp.le
      _ = P ^ 3 := by ring
  have hql : (1 / P) ^ 3 ≤ q ^ 3 := by
    apply le_of_mul_le_mul_right (a := P) ?_ hp
    calc
      (1 / P) ^ 3 * P = (1 / P) ^ 2 := by field_simp [hp.ne'] <;> ring
      _ ≤ g * Real.sqrt g := hl
      _ = q ^ 3 * A := hcubic.symm
      _ ≤ q ^ 3 * P := mul_le_mul_of_nonneg_left hA.2 (pow_nonneg hq.le 3)
  exact ⟨(pow_le_pow_iff_left₀ hi hq.le (by decide : (3 : ℕ) ≠ 0)).mp hql,
    (pow_le_pow_iff_left₀ hq.le hp.le (by decide : (3 : ℕ) ≠ 0)).mp hqu⟩

/-- The cancellation is entirely algebraic once the two actual identities
and their first derivative are known. The two remainders are both `O(x)`. -/
theorem n05_optical_root_log_deriv_bound {x ξ q g A p d κ M : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hg : κ ≤ g) (hA : Real.sqrt κ ≤ A)
    (hsymbol : ξ * q ^ 2 = x * g)
    (hcubic : q ^ 3 * A = g * Real.sqrt g)
    (hderiv : q ^ 3 + 2 * ξ * q * d = p)
    (hp : |p - g| ≤ M * x)
    (haverage : |A - Real.sqrt g| ≤ M * x / (2 * Real.sqrt κ)) :
    |d / q| ≤ M / κ := by
  have hgpos : 0 < g := hκ.trans_le hg
  have hspos : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hApos : 0 < A := hspos.trans_le hA
  have hquot : d / q = (p - q ^ 3) / (2 * x * g) := by
    apply (div_eq_div_iff hq.ne' (by positivity : (2 : ℝ) * x * g ≠ 0)).mpr
    calc
      d * (2 * x * g) = 2 * d * (x * g) := by ring
      _ = (2 * ξ * q * d) * q := by rw [← hsymbol]; ring
      _ = (p - q ^ 3) * q := by rw [show 2 * ξ * q * d = p - q ^ 3 by
        linarith only [hderiv]]
  have hcube : q ^ 3 = g * Real.sqrt g / A := (eq_div_iff hApos.ne').mpr hcubic
  have he : d / q = (p - g) / (2 * x * g) +
      (A - Real.sqrt g) / (2 * x * A) := by
    rw [hquot, hcube]
    field_simp [hx.ne', hgpos.ne', hApos.ne'] <;> ring
  have hfirst : |(p - g) / (2 * x * g)| ≤ M / (2 * κ) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) * x * g)]
    calc
      |p - g| / (2 * x * g) ≤ (M * x) / (2 * x * g) :=
        div_le_div_of_nonneg_right hp (by positivity)
      _ = M / (2 * g) := by field_simp [hx.ne', hgpos.ne'] <;> ring
      _ ≤ M / (2 * κ) := div_le_div_of_nonneg_left hM (by positivity)
        (mul_le_mul_of_nonneg_left hg (by norm_num))
  have hsA : κ ≤ Real.sqrt κ * A := by
    have hm := mul_le_mul_of_nonneg_left hA hspos.le
    nlinarith only [hm, Real.sq_sqrt hκ.le]
  have hsecond : |(A - Real.sqrt g) / (2 * x * A)| ≤ M / (4 * κ) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) * x * A)]
    calc
      |A - Real.sqrt g| / (2 * x * A) ≤
          (M * x / (2 * Real.sqrt κ)) / (2 * x * A) :=
        div_le_div_of_nonneg_right haverage (by positivity)
      _ = M / (4 * Real.sqrt κ * A) := by
        field_simp [hx.ne', hspos.ne', hApos.ne'] <;> ring
      _ ≤ M / (4 * κ) := div_le_div_of_nonneg_left hM (by positivity)
        (by nlinarith only [hsA])
  have hsum : M / (2 * κ) + M / (4 * κ) ≤ M / κ := by
    have heq : M / (2 * κ) + M / (4 * κ) = (3 / 4 : ℝ) * (M / κ) := by
      field_simp [hκ.ne'] <;> ring
    rw [heq]
    nlinarith only [div_nonneg hM hκ.le]
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans hsum)

/-- Differentiating the true principal-symbol equation supplies the
identity used in the preceding cancellation lemma. -/
theorem n05_optical_symbol_deriv {F ξ : ℝ → ℝ} {a x : ℝ}
    (hF : DifferentiableAt ℝ F x) (hξ : ContDiffAt ℝ 2 ξ x)
    (hsymbol : ∀ y ∈ Ioo (0 : ℝ) a, ξ y * (deriv ξ y) ^ 2 = F y)
    (hx : x ∈ Ioo (0 : ℝ) a) :
    (deriv ξ x) ^ 3 + 2 * ξ x * deriv ξ x * deriv (deriv ξ) x = deriv F x := by
  have hq := (hξ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp := (hξ.differentiableAt (by norm_num)).hasDerivAt.mul (hq.hasDerivAt.pow 2)
  have he : F =ᶠ[𝓝 x] fun y => ξ y * (deriv ξ y) ^ 2 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hsymbol y hy).symm
  have hd := (hp.congr_of_eventuallyEq he).unique hF.hasDerivAt
  simp only [Pi.pow_apply, Pi.mul_apply] at hd
  convert hd using 1 <;> ring

/-- Closed-interval first geometry for the actual root coordinate.
The coordinate is identified by its actual optical time and symbol;
its second derivative bound is a conclusion, including at the root. -/
theorem n05_optical_root_first_geometry {F ξ : ℝ → ℝ} {a κ P : ℝ} {M : NNReal}
    (ha : 0 < a) (hκ : 0 < κ) (hP : 1 ≤ P) (hPκ : 1 / P ≤ κ)
    (hF : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 F x)
    (hξ : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 ξ x)
    (hzero : F 0 = 0)
    (hlower : ∀ x ∈ Icc (0 : ℝ) a, κ * x ≤ F x)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) a, |deriv F x| ≤ P)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) a, |deriv (deriv F) x| ≤ M)
    (hξpos : ∀ x ∈ Ioo (0 : ℝ) a, 0 < ξ x)
    (hqpos : ∀ x ∈ Ioo (0 : ℝ) a, 0 < deriv ξ x)
    (hsymbol : ∀ x ∈ Ioo (0 : ℝ) a, ξ x * (deriv ξ x) ^ 2 = F x)
    (htime : ∀ x ∈ Icc (0 : ℝ) a,
      (∫ y in (0 : ℝ)..x, Real.sqrt (F y)) = (2 / 3 : ℝ) * ξ x * Real.sqrt (ξ x)) :
    ∀ x ∈ Icc (0 : ℝ) a,
      1 / P ≤ deriv ξ x ∧ deriv ξ x ≤ P ∧
        |deriv (deriv ξ) x| ≤ ((M : ℝ) / κ) * deriv ξ x := by
  let g := n05OpticalRootQuotient F
  let A := n05OpticalRootAverage g
  have hFC : ContinuousOn F (Icc (0 : ℝ) a) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hdC := n05_optical_deriv_continuousOn hF
  have hdL := n05_optical_deriv_lipschitz hF hsecond
  have hgL : LipschitzOnWith M g (Icc (0 : ℝ) a) :=
    n05OpticalRootQuotient_lipschitz hdC hdL
  have hgκ : ∀ x ∈ Icc (0 : ℝ) a, κ ≤ g x :=
    n05OpticalRootQuotient_lower ha hF hzero hdL hlower
  have hgb : ∀ x ∈ Icc (0 : ℝ) a, 1 / P ≤ g x ∧ g x ≤ P := by
    intro x hx
    exact ⟨hPκ.trans (hgκ x hx),
      (le_abs_self _).trans (n05OpticalRootQuotient_abs_le hdC hfirst hx)⟩
  have hp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hiP : 1 / P ≤ P :=
    ((div_le_iff₀ hp).mpr (by simpa using hP) : 1 / P ≤ 1).trans hP
  have hAb : ∀ x ∈ Icc (0 : ℝ) a, 1 / P ≤ A x ∧ A x ≤ P := by
    intro x hx
    have hb := n05OpticalRootAverage_bounds hgL.continuousOn hgb hx
    exact ⟨(n05_optical_sqrt_envelope hP ⟨le_rfl, hiP⟩).1.trans hb.1,
      hb.2.trans (n05_optical_sqrt_envelope hP ⟨hiP, le_rfl⟩).2⟩
  have hfactor : ∀ x ∈ Icc (0 : ℝ) a, F x = x * g x := by
    intro x hx
    exact (n05OpticalRootQuotient_mul hF hzero hx).symm
  have ho (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) :
      1 / P ≤ deriv ξ x ∧ deriv ξ x ≤ P ∧
        |deriv (deriv ξ) x| ≤ ((M : ℝ) / κ) * deriv ξ x := by
    have hxc := Ioo_subset_Icc_self hx
    have hs : ξ x * (deriv ξ x) ^ 2 = x * g x :=
      (hsymbol x hx).trans (hfactor x hxc)
    have ht : ξ x * Real.sqrt (ξ x) = x * Real.sqrt x * A x := by
      have ht1 := htime x hxc
      have ht2 := n05OpticalRootAverage_time hFC hgL.continuousOn hfactor hxc
      change (∫ y in (0 : ℝ)..x, Real.sqrt (F y)) =
        (2 / 3 : ℝ) * x * Real.sqrt x * A x at ht2
      nlinarith only [ht1, ht2]
    have hc := n05_optical_root_cubic_identity hx.1 (hξpos x hx) (hqpos x hx)
      (hκ.le.trans (hgκ x hxc)) hs ht
    have hb := n05_optical_root_cubic_bounds hP (hqpos x hx) (hgb x hxc) (hAb x hxc) hc
    have hAK : Real.sqrt κ ≤ A x :=
      (n05OpticalRootAverage_bounds hgL.continuousOn
        (fun y hy => ⟨hgκ y hy, (hgb y hy).2⟩) hxc).1
    have hlog := n05_optical_root_log_deriv_bound hx.1 (hqpos x hx) hκ M.coe_nonneg
      (hgκ x hxc) hAK hs hc
      (n05_optical_symbol_deriv ((hF x hxc).differentiableAt (by norm_num))
        (hξ x hxc) hsymbol hx)
      (n05OpticalRootQuotient_deriv_sub_le hdC hdL hxc)
      (n05OpticalRootAverage_sub_sqrt_le hκ hgL hgκ hxc)
    rw [abs_div, abs_of_pos (hqpos x hx)] at hlog
    exact ⟨hb.1, hb.2, (div_le_iff₀ (hqpos x hx)).mp hlog⟩
  have hqC := n05_optical_deriv_continuousOn hξ
  have hqqC : ContinuousOn (deriv (deriv ξ)) (Icc (0 : ℝ) a) := by
    intro x hx
    exact (((hξ x hx).derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  intro x hx
  have hxc : x ∈ closure (Ioo (0 : ℝ) a) := by
    simpa only [closure_Ioo ha.ne] using hx
  refine ⟨?_, ?_, ?_⟩
  · exact le_on_closure (fun y hy => (ho y hy).1) continuousOn_const
      (by simpa only [closure_Ioo ha.ne] using hqC) hxc
  · exact le_on_closure (fun y hy => (ho y hy).2.1)
      (by simpa only [closure_Ioo ha.ne] using hqC) continuousOn_const hxc
  · exact le_on_closure (fun y hy => (ho y hy).2.2)
      (by simpa only [closure_Ioo ha.ne] using hqqC.abs)
      (by simpa only [closure_Ioo ha.ne] using hqC.const_mul ((M : ℝ) / κ)) hxc

/-- The true height normalization gives reciprocal bounds without any
derivative estimate or choice of a square-root representative. -/
theorem n05_optical_height_envelope {H w q P W : ℝ}
    (hH : 0 < H) (hP : 0 < P) (hW : 0 < W)
    (hw : 1 / W ≤ w ∧ w ≤ W) (hq : 1 / P ≤ q ∧ q ≤ P)
    (hnormal : H ^ 2 * w * q = 1) :
    H ≤ Real.sqrt (W * P) ∧ H⁻¹ ≤ Real.sqrt (W * P) := by
  have hwp : 0 < w := (one_div_pos.mpr hW).trans_le hw.1
  have hqp : 0 < q := (one_div_pos.mpr hP).trans_le hq.1
  have hn : H ^ 2 * (w * q) = 1 := by simpa only [mul_assoc] using hnormal
  have hlow : 1 / (W * P) ≤ w * q := by
    calc
      1 / (W * P) = (1 / W) * (1 / P) := by
        field_simp [hW.ne', hP.ne'] <;> ring
      _ ≤ w * q := mul_le_mul hw.1 hq.1 (by positivity) hwp.le
  have hupp : w * q ≤ W * P := mul_le_mul hw.2 hq.2 hqp.le hW.le
  have hsq : H ^ 2 = 1 / (w * q) :=
    (eq_div_iff (mul_ne_zero hwp.ne' hqp.ne')).mpr hn
  have hHsq : H ^ 2 ≤ W * P := by
    rw [hsq]
    simpa only [one_div_one_div] using
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 < 1 / (W * P)) hlow
  have hprod : w * q = 1 / H ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hH.ne')).mpr
    simpa only [mul_comm] using hn
  have hinv : (H⁻¹) ^ 2 = w * q := by
    rw [hprod]
    simp only [one_div, inv_pow]
  exact ⟨Real.le_sqrt_of_sq_le hHsq,
    Real.le_sqrt_of_sq_le (hinv.trans_le hupp)⟩

/-- The height logarithmic derivative is obtained by differentiating
the actual normalization, rather than by postulating a derivative formula. -/
theorem n05_optical_height_log_deriv_of_eventuallyEq {H w q : ℝ → ℝ} {x : ℝ}
    (hH : DifferentiableAt ℝ H x) (hw : DifferentiableAt ℝ w x)
    (hq : DifferentiableAt ℝ q x)
    (hHpos : 0 < H x) (hwpos : 0 < w x) (hqpos : 0 < q x)
    (hnormal : (fun y => H y ^ 2 * w y * q y) =ᶠ[𝓝 x] fun _ => 1) :
    deriv H x = -(H x / 2) * (deriv w x / w x + deriv q x / q x) := by
  have hp := ((hH.hasDerivAt.pow 2).mul hw.hasDerivAt).mul hq.hasDerivAt
  have hd := (hp.congr_of_eventuallyEq hnormal.symm).unique (hasDerivAt_const x (1 : ℝ))
  simp only [Pi.pow_apply, Pi.mul_apply] at hd
  have hm : H x * (2 * w x * q x * deriv H x +
      H x * (deriv w x * q x + w x * deriv q x)) = 0 := by
    convert hd using 1 <;> ring
  have hc := (mul_eq_zero.mp hm).resolve_left hHpos.ne'
  apply mul_right_cancel₀ (show (2 : ℝ) * w x * q x ≠ 0 by positivity)
  calc
    deriv H x * (2 * w x * q x) =
        -(H x * (deriv w x * q x + w x * deriv q x)) := by
      nlinarith only [hc]
    _ = (-(H x / 2) * (deriv w x / w x + deriv q x / q x)) *
        (2 * w x * q x) := by
      field_simp [hwpos.ne', hqpos.ne'] <;> ring

theorem n05_optical_height_log_deriv {H w q : ℝ → ℝ} {a x : ℝ}
    (hH : DifferentiableAt ℝ H x) (hw : DifferentiableAt ℝ w x)
    (hq : DifferentiableAt ℝ q x)
    (hHpos : 0 < H x) (hwpos : 0 < w x) (hqpos : 0 < q x)
    (hnormal : ∀ y ∈ Ioo (0 : ℝ) a, H y ^ 2 * w y * q y = 1)
    (hx : x ∈ Ioo (0 : ℝ) a) :
    deriv H x = -(H x / 2) * (deriv w x / w x + deriv q x / q x) := by
  apply n05_optical_height_log_deriv_of_eventuallyEq hH hw hq hHpos hwpos hqpos
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact hnormal y hy

/-- Complete first-order optical geometry on the closed root half.
The weight enters through its own reciprocal envelope and logarithmic
derivative bound. In the radial application the latter is `|r F(r)|`.
All coordinate and height derivative estimates remain conclusions. -/
theorem n05_optical_root_height_geometry {F ξ w H : ℝ → ℝ}
    {a κ P W V : ℝ} {M : NNReal}
    (ha : 0 < a) (hκ : 0 < κ) (hP : 1 ≤ P) (hPκ : 1 / P ≤ κ)
    (hW : 0 < W) (hV : 0 ≤ V)
    (hF : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 F x)
    (hξ : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 ξ x)
    (hw : ∀ x ∈ Icc (0 : ℝ) a, DifferentiableAt ℝ w x)
    (hH : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 1 H x)
    (hzero : F 0 = 0)
    (hlower : ∀ x ∈ Icc (0 : ℝ) a, κ * x ≤ F x)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) a, |deriv F x| ≤ P)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) a, |deriv (deriv F) x| ≤ M)
    (hξpos : ∀ x ∈ Ioo (0 : ℝ) a, 0 < ξ x)
    (hqpos : ∀ x ∈ Ioo (0 : ℝ) a, 0 < deriv ξ x)
    (hsymbol : ∀ x ∈ Ioo (0 : ℝ) a, ξ x * (deriv ξ x) ^ 2 = F x)
    (htime : ∀ x ∈ Icc (0 : ℝ) a,
      (∫ y in (0 : ℝ)..x, Real.sqrt (F y)) = (2 / 3 : ℝ) * ξ x * Real.sqrt (ξ x))
    (hweight : ∀ x ∈ Icc (0 : ℝ) a, 1 / W ≤ w x ∧ w x ≤ W)
    (hweightDeriv : ∀ x ∈ Icc (0 : ℝ) a, |deriv w x / w x| ≤ V)
    (hHpos : ∀ x ∈ Icc (0 : ℝ) a, 0 < H x)
    (hnormal : ∀ x ∈ Icc (0 : ℝ) a, H x ^ 2 * w x * |deriv ξ x| = 1) :
    ∀ x ∈ Icc (0 : ℝ) a,
      1 / P ≤ deriv ξ x ∧ deriv ξ x ≤ P ∧ (deriv ξ x)⁻¹ ≤ P ∧
        |deriv (deriv ξ) x| ≤ ((M : ℝ) / κ) * deriv ξ x ∧
        H x ≤ Real.sqrt (W * P) ∧ (H x)⁻¹ ≤ Real.sqrt (W * P) ∧
        |deriv H x| ≤ Real.sqrt (W * P) / 2 * (V + (M : ℝ) / κ) := by
  have hgeom := n05_optical_root_first_geometry ha hκ hP hPκ hF hξ hzero hlower
    hfirst hsecond hξpos hqpos hsymbol htime
  have hp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hqclosed (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : 0 < deriv ξ x :=
    (one_div_pos.mpr hp).trans_le (hgeom x hx).1
  have hnormalPos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) :
      H x ^ 2 * w x * deriv ξ x = 1 := by
    simpa only [abs_of_pos (hqclosed x hx)] using hnormal x hx
  have hHbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) :
      H x ≤ Real.sqrt (W * P) ∧ (H x)⁻¹ ≤ Real.sqrt (W * P) :=
    n05_optical_height_envelope (hHpos x hx) hp hW (hweight x hx)
      ⟨(hgeom x hx).1, (hgeom x hx).2.1⟩ (hnormalPos x hx)
  have hHder (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) :
      |deriv H x| ≤ Real.sqrt (W * P) / 2 * (V + (M : ℝ) / κ) := by
    have hxc := Ioo_subset_Icc_self hx
    have hqp := hqclosed x hxc
    have he := n05_optical_height_log_deriv
      ((hH x hxc).differentiableAt (by norm_num)) (hw x hxc)
      (((hξ x hxc).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
      (hHpos x hxc) ((one_div_pos.mpr hW).trans_le (hweight x hxc).1) hqp
      (fun y hy => hnormalPos y (Ioo_subset_Icc_self hy)) hx
    have hqlog : |deriv (deriv ξ) x / deriv ξ x| ≤ (M : ℝ) / κ := by
      rw [abs_div, abs_of_pos hqp]
      exact (div_le_iff₀ hqp).mpr (hgeom x hxc).2.2
    have hsum : |deriv w x / w x + deriv (deriv ξ) x / deriv ξ x| ≤
        V + (M : ℝ) / κ :=
      (abs_add_le _ _).trans (add_le_add (hweightDeriv x hxc) hqlog)
    rw [he, abs_mul, abs_neg,
      abs_of_pos (div_pos (hHpos x hxc) (by norm_num : (0 : ℝ) < 2))]
    exact mul_le_mul (div_le_div_of_nonneg_right (hHbound x hxc).1 (by norm_num))
      hsum (abs_nonneg _) (by positivity)
  have hHdC : ContinuousOn (deriv H) (Icc (0 : ℝ) a) := by
    intro x hx
    exact ((hH x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  intro x hx
  have hqinv : (deriv ξ x)⁻¹ ≤ P := by
    have hmul : 1 ≤ deriv ξ x * P := (div_le_iff₀ hp).mp (hgeom x hx).1
    have hi : 1 / deriv ξ x ≤ P := (div_le_iff₀ (hqclosed x hx)).mpr (by
      simpa only [mul_comm] using hmul)
    simpa only [one_div] using hi
  refine ⟨(hgeom x hx).1, (hgeom x hx).2.1, hqinv, (hgeom x hx).2.2,
    (hHbound x hx).1, (hHbound x hx).2, ?_⟩
  apply le_on_closure hHder
    (by simpa only [closure_Ioo ha.ne] using hHdC.abs) continuousOn_const
  simpa only [closure_Ioo ha.ne] using hx

/-- An equal-travel cut supplies the root quotient lower bound itself.
The constants are explicit finite algebraic expressions in the original
two-root lower bound, travel, interval length and derivative bounds. -/
theorem n05_optical_equal_cut_height_geometry {F ξ w H : ℝ → ℝ}
    {L a α τ B B₁ W V : ℝ} {M : NNReal}
    (ha : 0 < a) (haL : a < L) (hα : 0 < α) (hτ : 0 < τ)
    (hB : 0 < B) (hB₁ : 0 ≤ B₁) (hW : 0 < W) (hV : 0 ≤ V)
    (hF : ∀ x ∈ Icc (0 : ℝ) L, ContDiffAt ℝ 2 F x)
    (hξ : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 2 ξ x)
    (hw : ∀ x ∈ Icc (0 : ℝ) a, DifferentiableAt ℝ w x)
    (hH : ∀ x ∈ Icc (0 : ℝ) a, ContDiffAt ℝ 1 H x)
    (hzero : F 0 = 0)
    (hlower : ∀ x ∈ Icc (0 : ℝ) L, α * min x (L - x) ≤ F x)
    (hupper : ∀ x ∈ Icc (0 : ℝ) L, F x ≤ B ^ 2)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) L, |deriv F x| ≤ B₁)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) L, |deriv (deriv F) x| ≤ M)
    (hleft : τ / 2 ≤ ∫ x in (0 : ℝ)..a, Real.sqrt (F x))
    (hright : τ / 2 ≤ ∫ x in a..L, Real.sqrt (F x))
    (hξpos : ∀ x ∈ Ioo (0 : ℝ) a, 0 < ξ x)
    (hqpos : ∀ x ∈ Ioo (0 : ℝ) a, 0 < deriv ξ x)
    (hsymbol : ∀ x ∈ Ioo (0 : ℝ) a, ξ x * (deriv ξ x) ^ 2 = F x)
    (htime : ∀ x ∈ Icc (0 : ℝ) a,
      (∫ y in (0 : ℝ)..x, Real.sqrt (F y)) = (2 / 3 : ℝ) * ξ x * Real.sqrt (ξ x))
    (hweight : ∀ x ∈ Icc (0 : ℝ) a, 1 / W ≤ w x ∧ w x ≤ W)
    (hweightDeriv : ∀ x ∈ Icc (0 : ℝ) a, |deriv w x / w x| ≤ V)
    (hHpos : ∀ x ∈ Icc (0 : ℝ) a, 0 < H x)
    (hnormal : ∀ x ∈ Icc (0 : ℝ) a, H x ^ 2 * w x * |deriv ξ x| = 1) :
    let δ := τ / (2 * B)
    let κ := α * δ / L
    let P := 1 + B₁ + 1 / κ
    δ ≤ a ∧ δ ≤ L - a ∧ 0 < κ ∧
      ∀ x ∈ Icc (0 : ℝ) a,
        1 / P ≤ deriv ξ x ∧ deriv ξ x ≤ P ∧ (deriv ξ x)⁻¹ ≤ P ∧
          |deriv (deriv ξ) x| ≤ ((M : ℝ) / κ) * deriv ξ x ∧
          H x ≤ Real.sqrt (W * P) ∧ (H x)⁻¹ ≤ Real.sqrt (W * P) ∧
          |deriv H x| ≤ Real.sqrt (W * P) / 2 * (V + (M : ℝ) / κ) := by
  let δ := τ / (2 * B)
  let κ := α * δ / L
  let P := 1 + B₁ + 1 / κ
  change δ ≤ a ∧ δ ≤ L - a ∧ 0 < κ ∧ _
  have hL : 0 < L := ha.trans haL
  have hFC : ContinuousOn F (Icc (0 : ℝ) L) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hcut := n05_optical_equal_cut_distance ha haL hB hFC hupper hleft hright
  have hδa : δ ≤ a := by simpa only [sub_zero] using hcut.1
  have hδright : δ ≤ L - a := hcut.2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hP : 1 ≤ P := by
    dsimp only [P]
    linarith only [hB₁, one_div_pos.mpr hκ]
  have hPκ : 1 / P ≤ κ := by
    have hle : 1 / κ ≤ P := by dsimp only [P]; linarith only [hB₁]
    simpa only [one_div_one_div] using
      one_div_le_one_div_of_le (one_div_pos.mpr hκ) hle
  have hB₁P : B₁ ≤ P := by
    dsimp only [P]
    linarith only [one_div_pos.mpr hκ]
  have hsub : Icc (0 : ℝ) a ⊆ Icc (0 : ℝ) L := Icc_subset_Icc le_rfl haL.le
  have hlowerHalf (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : κ * x ≤ F x := by
    exact (n05_optical_root_distance_lower hL hδ.le (hδa.trans haL.le)
      hx.1 (by linarith only [hx.2, hδright]) hα.le).trans (hlower x (hsub hx))
  refine ⟨hδa, hδright, hκ, ?_⟩
  exact n05_optical_root_height_geometry ha hκ hP hPκ hW hV
    (fun x hx => hF x (hsub hx)) hξ hw hH hzero hlowerHalf
    (fun x hx => (hfirst x (hsub hx)).trans hB₁P)
    (fun x hx => hsecond x (hsub hx)) hξpos hqpos hsymbol htime
    hweight hweightDeriv hHpos hnormal

end ContinuousFlexibility.Statements
