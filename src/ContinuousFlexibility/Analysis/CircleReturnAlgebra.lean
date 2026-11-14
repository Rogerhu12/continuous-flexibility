module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Algebra of the circle return operator

Paper §7 (`07-fixed-geometry.tex`, the return residual and the circle operator `M_T`).
Everything here concerns plain real functions of one real variable: even/odd projections,
the operator `M_T ψ = E[ψ(· + T)]`, its action on trigonometric modes, its inverse on finite
trigonometric sums, the small-divisor coefficient bound, and the corresponding `L²` estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Even part. -/
def circleReturnEven (g : ℝ → ℝ) (θ : ℝ) : ℝ := (g θ + g (-θ)) / 2

/-- Odd part. -/
def circleReturnOdd (g : ℝ → ℝ) (θ : ℝ) : ℝ := (g θ - g (-θ)) / 2

/-- The circle operator `M_T ψ = E[ψ(· + T)]`. -/
def circleReturnShift (T : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  circleReturnEven (fun t => ψ (t + T)) θ

/-- The inverse of `M_T` on finite cosine sums, as a finite sine sum. -/
def circleReturnInverse (J : Finset ℕ) (c : ℕ → ℝ) (T θ : ℝ) : ℝ :=
  ∑ j ∈ J, c j / Real.sin (j * T) * Real.sin (j * θ)

/-! ### Item 1: mode action -/

theorem circleReturnShift_sin_mode (j T θ : ℝ) :
    circleReturnShift T (fun θ => Real.sin (j * θ)) θ = Real.sin (j * T) * Real.cos (j * θ) := by
  simp only [circleReturnShift, circleReturnEven, mul_add, mul_neg, Real.sin_add, Real.sin_neg,
    Real.cos_neg]
  ring

theorem circleReturnShift_cos_mode (j T θ : ℝ) :
    circleReturnShift T (fun θ => Real.cos (j * θ)) θ = Real.cos (j * T) * Real.cos (j * θ) := by
  simp only [circleReturnShift, circleReturnEven, mul_add, mul_neg, Real.cos_add, Real.sin_neg,
    Real.cos_neg]
  ring

theorem circleReturnShift_odd {ψ : ℝ → ℝ} (hψ : ∀ θ, ψ (-θ) = -ψ θ) (T θ : ℝ) :
    circleReturnShift T ψ θ = (ψ (θ + T) - ψ (θ - T)) / 2 := by
  have h : ψ (-θ + T) = -ψ (θ - T) := by
    rw [← hψ]; congr 1; ring
  simp only [circleReturnShift, circleReturnEven]
  rw [h]; ring

/-! ### Item 2: projections -/

theorem circleReturnEven_add_odd (g : ℝ → ℝ) (θ : ℝ) :
    circleReturnEven g θ + circleReturnOdd g θ = g θ := by
  simp only [circleReturnEven, circleReturnOdd]; ring

theorem circleReturnEven_even (g : ℝ → ℝ) (θ : ℝ) :
    circleReturnEven g (-θ) = circleReturnEven g θ := by
  simp only [circleReturnEven, neg_neg]; ring

theorem circleReturnOdd_odd (g : ℝ → ℝ) (θ : ℝ) :
    circleReturnOdd g (-θ) = -circleReturnOdd g θ := by
  simp only [circleReturnOdd, neg_neg]; ring

theorem circleReturnEven_comp_odd (g h : ℝ → ℝ) (hh : ∀ θ, h (-θ) = -h θ) :
    circleReturnEven (g ∘ h) = circleReturnEven g ∘ h := by
  funext θ
  simp only [circleReturnEven, Function.comp_apply, hh θ]

theorem circleReturnOdd_comp_odd (g h : ℝ → ℝ) (hh : ∀ θ, h (-θ) = -h θ) :
    circleReturnOdd (g ∘ h) = circleReturnOdd g ∘ h := by
  funext θ
  simp only [circleReturnOdd, Function.comp_apply, hh θ]

/-! ### Item 3: inverse on finite trigonometric sums -/

theorem circleReturnInverse_odd (J : Finset ℕ) (c : ℕ → ℝ) (T θ : ℝ) :
    circleReturnInverse J c T (-θ) = -circleReturnInverse J c T θ := by
  unfold circleReturnInverse
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg, Real.sin_neg]; ring

theorem circleReturnShift_inverse (J : Finset ℕ) (c : ℕ → ℝ) (T : ℝ)
    (hT : ∀ j ∈ J, Real.sin (j * T) ≠ 0) (θ : ℝ) :
    circleReturnShift T (circleReturnInverse J c T) θ = ∑ j ∈ J, c j * Real.cos (j * θ) := by
  rw [circleReturnShift_odd (circleReturnInverse_odd J c T)]
  simp only [circleReturnInverse]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hs := hT j hj
  have key : Real.sin (j * (θ + T)) - Real.sin (j * (θ - T))
      = 2 * Real.cos (j * θ) * Real.sin (j * T) := by
    rw [mul_add, mul_sub, Real.sin_add, Real.sin_sub]; ring
  calc (c j / Real.sin (j * T) * Real.sin (j * (θ + T))
        - c j / Real.sin (j * T) * Real.sin (j * (θ - T))) / 2
      = c j / Real.sin (j * T) * (Real.sin (j * (θ + T)) - Real.sin (j * (θ - T))) / 2 := by ring
    _ = (c j / Real.sin (j * T) * Real.sin (j * T)) * Real.cos (j * θ) := by rw [key]; ring
    _ = c j * Real.cos (j * θ) := by rw [div_mul_cancel₀ _ hs]

/-! ### Orthogonality on `[0, 2π]` -/

theorem circleReturn_integral_cos_int (n : ℤ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos ((n:ℝ) * θ) = if n = 0 then 2 * Real.pi else 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  · have hc : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos]
    have h : Real.sin ((n:ℝ) * (2 * Real.pi)) = 0 := by
      have h0 := Real.sin_int_mul_pi (2 * n)
      have h1 : ((n:ℝ) * (2 * Real.pi)) = ((2 * n : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [h1]; exact h0
    rw [h]; simp [hn]

theorem circleReturn_integral_cos_mul_cos (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos (j * θ) * Real.cos (k * θ)
      = if j = k then Real.pi else 0 := by
  have h : ∀ θ : ℝ, Real.cos (j * θ) * Real.cos (k * θ)
      = (Real.cos ((((j:ℤ) - (k:ℤ) : ℤ) : ℝ) * θ) + Real.cos ((((j:ℤ) + (k:ℤ) : ℤ) : ℝ) * θ))
        / 2 := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  have i1 : IntervalIntegrable (fun θ : ℝ => Real.cos ((((j:ℤ) - (k:ℤ) : ℤ) : ℝ) * θ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => Real.cos ((((j:ℤ) + (k:ℤ) : ℤ) : ℝ) * θ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add i1 i2,
    circleReturn_integral_cos_int, circleReturn_integral_cos_int]
  by_cases hjk : j = k
  · subst hjk
    have h2 : (j:ℤ) + (j:ℤ) ≠ 0 := by omega
    simp only [sub_self, h2, eq_self, ↓reduceIte]; ring
  · have h1 : (j:ℤ) - (k:ℤ) ≠ 0 := by omega
    have h2 : (j:ℤ) + (k:ℤ) ≠ 0 := by omega
    simp only [h1, h2, hjk, ↓reduceIte]; ring

theorem circleReturn_integral_sin_mul_sin (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.sin (j * θ) * Real.sin (k * θ)
      = if j = k then Real.pi else 0 := by
  have h : ∀ θ : ℝ, Real.sin (j * θ) * Real.sin (k * θ)
      = (Real.cos ((((j:ℤ) - (k:ℤ) : ℤ) : ℝ) * θ) - Real.cos ((((j:ℤ) + (k:ℤ) : ℤ) : ℝ) * θ))
        / 2 := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  have i1 : IntervalIntegrable (fun θ : ℝ => Real.cos ((((j:ℤ) - (k:ℤ) : ℤ) : ℝ) * θ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => Real.cos ((((j:ℤ) + (k:ℤ) : ℤ) : ℝ) * θ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub i1 i2,
    circleReturn_integral_cos_int, circleReturn_integral_cos_int]
  by_cases hjk : j = k
  · subst hjk
    have h2 : (j:ℤ) + (j:ℤ) ≠ 0 := by omega
    simp only [sub_self, h2, eq_self, ↓reduceIte]; ring
  · have h1 : (j:ℤ) - (k:ℤ) ≠ 0 := by omega
    have h2 : (j:ℤ) + (k:ℤ) ≠ 0 := by omega
    simp only [h1, h2, hjk, ↓reduceIte]; ring

/-- Pairing of a finite orthogonal expansion with one of its members. -/
theorem circleReturn_integral_sum_mul (J : Finset ℕ) (φ : ℕ → ℝ → ℝ)
    (hφ : ∀ j, Continuous (φ j))
    (horth : ∀ j ∈ J, ∀ k ∈ J,
      ∫ θ in (0:ℝ)..(2 * Real.pi), φ j θ * φ k θ = if j = k then Real.pi else 0)
    (a : ℕ → ℝ) (k : ℕ) (hk : k ∈ J) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), (∑ j ∈ J, a j * φ j θ) * φ k θ = a k * Real.pi := by
  have hint : ∀ j ∈ J, IntervalIntegrable (fun θ => a j * φ j θ * φ k θ)
      MeasureTheory.volume 0 (2 * Real.pi) := fun j _ =>
    ((continuous_const.mul (hφ j)).mul (hφ k)).intervalIntegrable _ _
  have h1 : ∀ j ∈ J, ∫ θ in (0:ℝ)..(2 * Real.pi), a j * φ j θ * φ k θ
      = if j = k then a j * Real.pi else 0 := by
    intro j hj
    have e : ∫ θ in (0:ℝ)..(2 * Real.pi), a j * φ j θ * φ k θ
        = ∫ θ in (0:ℝ)..(2 * Real.pi), a j * (φ j θ * φ k θ) :=
      intervalIntegral.integral_congr (fun θ _ => by ring)
    rw [e, intervalIntegral.integral_const_mul, horth j hj k hk]
    split_ifs <;> simp
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum hint, Finset.sum_congr rfl h1, Finset.sum_ite_eq']
  simp [hk]

/-- Parseval on a finite orthogonal expansion. -/
theorem circleReturn_parseval (J : Finset ℕ) (φ : ℕ → ℝ → ℝ)
    (hφ : ∀ j, Continuous (φ j))
    (horth : ∀ j ∈ J, ∀ k ∈ J,
      ∫ θ in (0:ℝ)..(2 * Real.pi), φ j θ * φ k θ = if j = k then Real.pi else 0)
    (a : ℕ → ℝ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), (∑ j ∈ J, a j * φ j θ) ^ 2
      = ∑ k ∈ J, a k ^ 2 * Real.pi := by
  have h1 : ∀ θ : ℝ, (∑ j ∈ J, a j * φ j θ) ^ 2
      = ∑ k ∈ J, a k * ((∑ j ∈ J, a j * φ j θ) * φ k θ) := by
    intro θ
    calc (∑ j ∈ J, a j * φ j θ) ^ 2
        = (∑ j ∈ J, a j * φ j θ) * (∑ k ∈ J, a k * φ k θ) := sq _
      _ = ∑ k ∈ J, (∑ j ∈ J, a j * φ j θ) * (a k * φ k θ) := by rw [← Finset.mul_sum]
      _ = ∑ k ∈ J, a k * ((∑ j ∈ J, a j * φ j θ) * φ k θ) :=
          Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ k ∈ J, IntervalIntegrable
      (fun θ => a k * ((∑ j ∈ J, a j * φ j θ) * φ k θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
    fun k _ => by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul ((continuous_finsetSum _ fun j _ =>
        continuous_const.mul (hφ j)).mul (hφ k))
  simp_rw [h1]
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_const_mul, circleReturn_integral_sum_mul J φ hφ horth a k hk]
  ring

/-- Uniqueness of the `M_T`-preimage of zero in the class of finite sine sums. -/
theorem circleReturnShift_sine_sum_eq_zero (J : Finset ℕ) (b : ℕ → ℝ) (T : ℝ) (ψ : ℝ → ℝ)
    (hψ : ∀ θ, ψ θ = ∑ j ∈ J, b j * Real.sin (j * θ))
    (hz : circleReturnShift T ψ = fun _ => 0)
    (hJ : ∀ j ∈ J, 0 < j ∧ Real.sin (j * T) ≠ 0) :
    ∀ j ∈ J, b j = 0 := by
  have hodd : ∀ θ, ψ (-θ) = -ψ θ := by
    intro θ
    rw [hψ, hψ, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_neg, Real.sin_neg]; ring
  have hsum : ∀ θ : ℝ, ∑ j ∈ J, (b j * Real.sin (j * T)) * Real.cos (j * θ) = 0 := by
    intro θ
    have h0 : circleReturnShift T ψ θ = 0 := congrFun hz θ
    rw [circleReturnShift_odd hodd, hψ, hψ] at h0
    have e : ∑ j ∈ J, (b j * Real.sin (j * T)) * Real.cos (j * θ)
        = (∑ j ∈ J, b j * Real.sin (j * (θ + T)) - ∑ j ∈ J, b j * Real.sin (j * (θ - T))) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_add, mul_sub, Real.sin_add, Real.sin_sub]; ring
    rw [e]; exact h0
  intro k hk
  have horth : ∀ j ∈ J, ∀ k ∈ J,
      ∫ θ in (0:ℝ)..(2 * Real.pi), (fun (j : ℕ) (θ : ℝ) => Real.cos (j * θ)) j θ
        * (fun (j : ℕ) (θ : ℝ) => Real.cos (j * θ)) k θ = if j = k then Real.pi else 0 :=
    fun j hj k hk => circleReturn_integral_cos_mul_cos j k (hJ j hj).1 (hJ k hk).1
  have h3 := circleReturn_integral_sum_mul J (fun (j : ℕ) (θ : ℝ) => Real.cos (j * θ))
    (fun j => by show Continuous fun θ : ℝ => Real.cos (j * θ); fun_prop) horth
    (fun j => b j * Real.sin (j * T)) k hk
  simp only [hsum, zero_mul, intervalIntegral.integral_zero] at h3
  have h4 : b k * Real.sin (k * T) = 0 := (mul_eq_zero.mp h3.symm).resolve_right Real.pi_ne_zero
  exact (mul_eq_zero.mp h4).resolve_right (hJ k hk).2

/-! ### Item 4: small-divisor bound -/

theorem circleReturn_coeff_bound (c : ℕ → ℝ) (T γ : ℝ) (j : ℕ) (hγ : 0 < γ) (hj : 1 ≤ j)
    (hs : γ / j ≤ |Real.sin (j * T)|) :
    |c j / Real.sin (j * T)| ≤ (j : ℝ) * |c j| / γ := by
  have hj' : (0:ℝ) < j := by exact_mod_cast hj
  have hpos : 0 < |Real.sin (j * T)| := lt_of_lt_of_le (div_pos hγ hj') hs
  rw [abs_div, div_le_iff₀ hpos]
  have hne1 : (j:ℝ) ≠ 0 := hj'.ne'
  have hne2 : γ ≠ 0 := hγ.ne'
  calc |c j| = ((j:ℝ) * |c j| / γ) * (γ / j) := by field_simp
    _ ≤ ((j:ℝ) * |c j| / γ) * |Real.sin (j * T)| := by gcongr

/-! ### Item 5: quantitative `L²` statement -/

theorem circleReturn_l2_bound (J : Finset ℕ) (c : ℕ → ℝ) (T γ : ℝ) (hγ : 0 < γ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ γ / j ≤ |Real.sin (j * T)|) (b : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi),
        (∑ j ∈ J, (j:ℝ) ^ b * (c j / Real.sin (j * T)) * Real.sin (j * θ)) ^ 2
      ≤ γ⁻¹ ^ 2 * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (∑ j ∈ J, (j:ℝ) ^ (b + 1) * c j * Real.cos (j * θ)) ^ 2 := by
  have hS := circleReturn_parseval J (fun (j : ℕ) (θ : ℝ) => Real.sin (j * θ))
    (fun j => by show Continuous fun θ : ℝ => Real.sin (j * θ); fun_prop)
    (fun j hj k hk => circleReturn_integral_sin_mul_sin j k (hJ j hj).1 (hJ k hk).1)
    (fun j => (j:ℝ) ^ b * (c j / Real.sin (j * T)))
  have hC := circleReturn_parseval J (fun (j : ℕ) (θ : ℝ) => Real.cos (j * θ))
    (fun j => by show Continuous fun θ : ℝ => Real.cos (j * θ); fun_prop)
    (fun j hj k hk => circleReturn_integral_cos_mul_cos j k (hJ j hj).1 (hJ k hk).1)
    (fun j => (j:ℝ) ^ (b + 1) * c j)
  rw [hS, hC, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  obtain ⟨hj1, hs⟩ := hJ j hj
  have hb := circleReturn_coeff_bound c T γ j hγ hj1 hs
  have hj' : (0:ℝ) < j := by exact_mod_cast hj1
  have habs : |(j:ℝ) ^ b * (c j / Real.sin (j * T))| ≤ γ⁻¹ * |(j:ℝ) ^ (b + 1) * c j| := by
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hj' _), abs_of_pos (pow_pos hj' _)]
    calc (j:ℝ) ^ b * |c j / Real.sin (j * T)| ≤ (j:ℝ) ^ b * ((j:ℝ) * |c j| / γ) := by gcongr
      _ = γ⁻¹ * ((j:ℝ) ^ (b + 1) * |c j|) := by ring
  have hsq : ((j:ℝ) ^ b * (c j / Real.sin (j * T))) ^ 2
      ≤ γ⁻¹ ^ 2 * ((j:ℝ) ^ (b + 1) * c j) ^ 2 := by
    calc ((j:ℝ) ^ b * (c j / Real.sin (j * T))) ^ 2
        = |(j:ℝ) ^ b * (c j / Real.sin (j * T))| ^ 2 := (sq_abs _).symm
      _ ≤ (γ⁻¹ * |(j:ℝ) ^ (b + 1) * c j|) ^ 2 := by gcongr
      _ = γ⁻¹ ^ 2 * ((j:ℝ) ^ (b + 1) * c j) ^ 2 := by rw [mul_pow, sq_abs]
  calc ((j:ℝ) ^ b * (c j / Real.sin (j * T))) ^ 2 * Real.pi
      ≤ (γ⁻¹ ^ 2 * ((j:ℝ) ^ (b + 1) * c j) ^ 2) * Real.pi := by gcongr
    _ = γ⁻¹ ^ 2 * (((j:ℝ) ^ (b + 1) * c j) ^ 2 * Real.pi) := by ring

end ContinuousFlexibility.Analysis
