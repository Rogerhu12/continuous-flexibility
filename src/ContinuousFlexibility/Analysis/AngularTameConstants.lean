import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar estimates for the angular commutator lemma

The large coefficient in the commutator estimate must occur linearly in
the final inverse estimate. These inequalities isolate the two scalar
steps: weighted Young's inequality and absorption of one lower derivative.
The absorption constant is an explicit function of the derivative order,
the preceding estimate constant, and the base inverse norm; it has no
argument for the large coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- The weighted geometric mean is bounded by the unweighted sum, also at
the two endpoints of the interpolation interval. -/
theorem angular_geometric_mean_le_add {A x theta : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (htheta : 0 ≤ theta) (htheta' : theta ≤ 1) :
    A ^ theta * x ^ (1 - theta) ≤ x + A := by
  have h := Real.geom_mean_le_arith_mean2_weighted htheta
    (sub_nonneg.mpr htheta') hA hx (by ring : theta + (1 - theta) = 1)
  have h₁ : theta * A ≤ A := by nlinarith
  have h₂ : (1 - theta) * x ≤ x := by nlinarith
  linarith

/-- The coefficient produced by interpolation costs one top-order weight
and one copy of `A`, uniformly over all intermediate integer orders. -/
theorem angular_mixed_weight_le {A w : ℝ} (hA : 0 ≤ A) (hw : 0 ≤ w)
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    A ^ ((k : ℝ) / m) * w ^ (m - k) ≤ w ^ m + A := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
  have ht : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg k) hmR.le
  have ht' : (k : ℝ) / m ≤ 1 := (div_le_one hmR).mpr hkR
  have hexp : (m : ℝ) * (1 - (k : ℝ) / m) = ((m - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]
    field_simp
  have hpow : (w ^ m : ℝ) ^ (1 - (k : ℝ) / m) = w ^ (m - k) := by
    rw [← Real.rpow_natCast w m, ← Real.rpow_mul hw, hexp, Real.rpow_natCast]
  simpa only [hpow] using
    angular_geometric_mean_le_add hA (pow_nonneg hw m) ht ht'

/-- A pointwise form of the adjacent-order interpolation inequality. Its
constant is explicit and does not involve the angular frequency. -/
theorem angular_pow_le_epsilon_succ {w epsilon : ℝ}
    (hw : 0 ≤ w) (hepsilon : 0 < epsilon) (m : ℕ) :
    w ^ m ≤ epsilon * w ^ (m + 1) + epsilon⁻¹ ^ m := by
  by_cases hcut : w ≤ epsilon⁻¹
  · exact (pow_le_pow_left₀ hw hcut m).trans
      (le_add_of_nonneg_left (mul_nonneg hepsilon.le (pow_nonneg hw _)))
  · have hcut' : epsilon⁻¹ ≤ w := le_of_lt (lt_of_not_ge hcut)
    have hone : 1 ≤ epsilon * w := by
      calc
        1 = epsilon * epsilon⁻¹ := (mul_inv_cancel₀ hepsilon.ne').symm
        _ ≤ epsilon * w := mul_le_mul_of_nonneg_left hcut' hepsilon.le
    have hmul := mul_le_mul_of_nonneg_right hone (pow_nonneg hw m)
    have hfirst : w ^ m ≤ epsilon * w ^ (m + 1) := by
      simpa only [one_mul, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hfirst.trans (le_add_of_nonneg_right (pow_nonneg (inv_nonneg.mpr hepsilon.le) m))

/-- The explicit constant after absorption. `m` is one less than the
desired Sobolev order, `D` bounds the commuted equation, and `B` bounds the
inverse on the base Hilbert space. -/
def angularAbsorptionConstant (m : ℕ) (D B : ℝ) : ℝ :=
  2 * D * (1 + B) * (1 + (2 * D) ^ m)

theorem angularAbsorptionConstant_pos (m : ℕ) {D B : ℝ}
    (hD : 0 < D) (hB : 0 ≤ B) : 0 < angularAbsorptionConstant m D B := by
  unfold angularAbsorptionConstant
  positivity

/-- Absorb one lower derivative while keeping the large coefficient `A`
linear. The constant in the conclusion is independent of `A`. -/
theorem angular_absorb_lower_order (m : ℕ) {D B A X Y U F Fzero : ℝ}
    (hD : 0 < D) (hB : 0 ≤ B) (hA : 1 ≤ A)
    (hU : 0 ≤ U) (hF : 0 ≤ F) (hFzero : 0 ≤ Fzero)
    (hbase : U ≤ B * Fzero)
    (hinterpolate : Y ≤ (2 * D)⁻¹ * X + (2 * D) ^ m * U)
    (hequation : X ≤ D * (F + Y + A * U)) :
    X ≤ angularAbsorptionConstant m D B * (F + A * Fzero) := by
  let T : ℝ := (2 * D) ^ m
  have hT : 0 ≤ T := pow_nonneg (by positivity) m
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hhalf : D * (2 * D)⁻¹ = (1 : ℝ) / 2 := by
    field_simp
  have hhalfX : D * ((2 * D)⁻¹ * X) = X / 2 := by
    rw [← mul_assoc, hhalf]
    ring
  have hinterpolate' := mul_le_mul_of_nonneg_left hinterpolate hD.le
  have habsorbed : X ≤ 2 * D * F + 2 * D * (T + A) * U := by
    dsimp only [T]
    nlinarith only [hequation, hinterpolate', hhalfX]
  have hTA : T + A ≤ (1 + T) * A := by
    nlinarith only [mul_nonneg hT (sub_nonneg.mpr hA)]
  have hcoef : 0 ≤ 2 * D * (T + A) := by positivity
  have hbase' := mul_le_mul_of_nonneg_left hbase hcoef
  have hbound : X ≤ 2 * D * F + 2 * D * (T + A) * (B * Fzero) :=
    habsorbed.trans (add_le_add_left hbase' _)
  have hB1 : B ≤ 1 + B := le_add_of_nonneg_left zero_le_one
  have hnext : 2 * D * (T + A) * (B * Fzero) ≤
      2 * D * ((1 + T) * A) * ((1 + B) * Fzero) := by
    gcongr
  have hFnext : 2 * D * F ≤ 2 * D * (1 + B) * (1 + T) * F := by
    have hBT : 1 ≤ (1 + B) * (1 + T) := by
      nlinarith only [hB, hT, mul_nonneg hB hT]
    have h := mul_le_mul_of_nonneg_left hBT (mul_nonneg (by positivity : 0 ≤ 2 * D) hF)
    nlinarith only [h]
  calc
    X ≤ 2 * D * F + 2 * D * (T + A) * (B * Fzero) := hbound
    _ ≤ 2 * D * (1 + B) * (1 + T) * F +
        2 * D * ((1 + T) * A) * ((1 + B) * Fzero) := add_le_add hFnext hnext
    _ = angularAbsorptionConstant m D B * (F + A * Fzero) := by
      dsimp only [angularAbsorptionConstant, T]
      ring

end ContinuousFlexibility.Analysis
