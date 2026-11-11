import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Radial.TransitionTransfer

/-!
# Transfer of the actual reference Jacobi state

The squared state energy of a solution of `(w u')' = 4 w' u / r`
has a two-sided transfer bound involving the total variation of `log w`.
This estimate will compare the weighted decay of the reference kernel
with the number of negative components of the profile.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

def n01aJacobiEnergy (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  u r ^ 2 + deriv u r ^ 2

theorem n01aJacobiEnergy_nonneg (u : ℝ → ℝ) (r : ℝ) :
    0 ≤ n01aJacobiEnergy u r := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem n01aJacobiEnergy_pos {u : ℝ → ℝ} {r : ℝ} (hu : u r ≠ 0) :
    0 < n01aJacobiEnergy u r :=
  add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg _)

theorem hasDerivAt_n01aJacobiEnergy {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    HasDerivAt (n01aJacobiEnergy u)
      (2 * u r * deriv u r + 2 * deriv u r * deriv (deriv u) r) r := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have h := ((hu.differentiable (by simp) r).hasDerivAt.pow 2).add
    ((hdu.differentiable (by simp) r).hasDerivAt.pow 2)
  simpa only [n01aJacobiEnergy, Nat.cast_ofNat, pow_one] using h

theorem n01a_second_deriv_of_jacobi {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) {r : ℝ}
    (hr : r ≠ 0) (hwr : w r ≠ 0) (hJ : Radial.radialJacobi 4 w u r = 0) :
    deriv (deriv u) r = (deriv w r / w r) * (4 * u r / r - deriv u r) := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hp := ((hw.differentiable (by simp) r).hasDerivAt.mul
    (hdu.differentiable (by simp) r).hasDerivAt).deriv
  rw [Radial.radialJacobi, hp] at hJ
  field_simp [hr] at hJ
  field_simp [hr, hwr]
  nlinarith only [hJ]

/-- The pointwise energy estimate is purely scalar algebra. -/
theorem n01a_jacobi_energy_abs_bound (α r u v g : ℝ)
    (hα : 0 < α) (hr : α ≤ r) :
    |2 * u * v + 2 * v * (4 * u / r - v) * g| ≤
      (1 + (4 / α + 2) * |g|) * (u ^ 2 + v ^ 2) := by
  have hrpos : 0 < r := hα.trans_le hr
  have hE : 0 ≤ u ^ 2 + v ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcross : |2 * u * v| ≤ u ^ 2 + v ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u - v), sq_nonneg (u + v)]
  have hratio : 4 / r ≤ 4 / α :=
    (div_le_div_iff₀ hrpos hα).mpr (by nlinarith only [hr])
  have hv : 2 * v ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by nlinarith [sq_nonneg u]
  have hinner : |2 * v * (4 * u / r - v)| ≤ (4 / α + 2) * (u ^ 2 + v ^ 2) := by
    calc
      |2 * v * (4 * u / r - v)| = |(4 / r) * (2 * u * v) - 2 * v ^ 2| := by
        congr 1
        ring
      _ ≤ |(4 / r) * (2 * u * v)| + |2 * v ^ 2| := abs_sub _ _
      _ = (4 / r) * |2 * u * v| + 2 * v ^ 2 := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) hrpos.le),
          abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg v))]
      _ ≤ (4 / α) * (u ^ 2 + v ^ 2) + 2 * (u ^ 2 + v ^ 2) :=
        add_le_add (mul_le_mul hratio hcross (abs_nonneg _) (by positivity)) hv
      _ = (4 / α + 2) * (u ^ 2 + v ^ 2) := by ring
  calc
    |2 * u * v + 2 * v * (4 * u / r - v) * g| ≤
        |2 * u * v| + |2 * v * (4 * u / r - v) * g| := abs_add _ _
    _ = |2 * u * v| + |2 * v * (4 * u / r - v)| * |g| := by rw [abs_mul]
    _ ≤ (u ^ 2 + v ^ 2) + ((4 / α + 2) * (u ^ 2 + v ^ 2)) * |g| :=
      add_le_add hcross (mul_le_mul_of_nonneg_right hinner (abs_nonneg _))
    _ = (1 + (4 / α + 2) * |g|) * (u ^ 2 + v ^ 2) := by ring

/-- The actual Jacobi energy transfers in either direction on a positive-radius interval. -/
theorem n01aJacobiEnergy_transfer {w u : ℝ → ℝ} {α a b : ℝ}
    (hα : 0 < α) (hαa : α ≤ a) (hab : a ≤ b)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hwpos : ∀ r ∈ Icc a b, 0 < w r)
    (hJ : ∀ r ∈ Icc a b, Radial.radialJacobi 4 w u r = 0)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    n01aJacobiEnergy u t ≤ n01aJacobiEnergy u s *
      Real.exp |∫ r in s..t, (1 + (4 / α + 2) * |deriv w r / w r|)| := by
  have hwd : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hκ : ContinuousOn (fun r => 1 + (4 / α + 2) * |deriv w r / w r|) (Icc a b) :=
    continuousOn_const.add (continuousOn_const.mul
      ((hwd.continuousOn.div hw.continuous.continuousOn (fun r hr => (hwpos r hr).ne')).abs))
  apply Radial.gronwall_integral_exp hab hκ
    (fun r _ => by positivity) (fun r _ => hasDerivAt_n01aJacobiEnergy hu r) _ hs ht
  intro r hr
  have hrpos : 0 < r := hα.trans_le (hαa.trans hr.1)
  rw [n01a_second_deriv_of_jacobi hw hu hrpos.ne' (hwpos r hr).ne' (hJ r hr)]
  exact n01a_jacobi_energy_abs_bound α r (u r) (deriv u r) (deriv w r / w r)
    hα (hαa.trans hr.1)

/-- Exponential state decay forces a corresponding lower bound for its
actual transfer exponent. This scalar step keeps the later counting
argument independent of the representation of the weighted function space. -/
theorem n01a_energy_decay_forces_transfer (E₀ E₁ A c x I : ℝ)
    (hE₀ : 0 < E₀) (hA : 0 < A)
    (htransfer : E₀ ≤ E₁ * Real.exp I)
    (hdecay : E₁ ≤ A * Real.exp (-c * x ^ 3)) :
    c * x ^ 3 ≤ I + Real.log A - Real.log E₀ := by
  have hb : E₀ ≤ A * Real.exp (I - c * x ^ 3) := by
    calc
      E₀ ≤ E₁ * Real.exp I := htransfer
      _ ≤ (A * Real.exp (-c * x ^ 3)) * Real.exp I :=
        mul_le_mul_of_nonneg_right hdecay (Real.exp_pos I).le
      _ = A * Real.exp (I - c * x ^ 3) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hl := Real.log_le_log hE₀ hb
  rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  linarith

end ContinuousFlexibility.Statements
