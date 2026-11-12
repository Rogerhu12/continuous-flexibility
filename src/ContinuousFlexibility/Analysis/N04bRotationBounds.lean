import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Translation-number bounds from a bounded corrector

A bounded change of the angular coordinate need not be proved invertible
for this estimate. Telescope its displacement along a genuine lift's
orbits. Its two bounded endpoint terms disappear after division by the
number of iterates, leaving the actual translation number.

The second result applies this to a uniform first-order expansion with an
actual bounded Lipschitz solution of the finite cohomological equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology

/-- A bounded corrector turns a pointwise displacement bound into the same
bound for the actual translation number. -/
theorem n04b_translationNumber_bound_of_bounded_corrector
    (f : CircleDeg1Lift) (H : ℝ → ℝ) (B α E : ℝ)
    (hB : ∀ x : ℝ, |H x - x| ≤ B)
    (hstep : ∀ x : ℝ, |H (f x) - H x - α| ≤ E) :
    |f.translationNumber - α| ≤ E := by
  have hiter (n : ℕ) :
      H 0 + (n : ℝ) * (α - E) ≤ H ((f ^ n) 0) ∧
        H ((f ^ n) 0) ≤ H 0 + (n : ℝ) * (α + E) := by
    induction n with
    | zero => simp only [pow_zero, CircleDeg1Lift.coe_one, id_eq,
        Nat.cast_zero, zero_mul, add_zero, le_refl, and_self]
    | succ n ih =>
      have h := abs_le.mp (hstep ((f ^ n) 0))
      rw [pow_succ', CircleDeg1Lift.mul_apply]
      simp only [Nat.cast_succ]
      constructor
      · calc
          H 0 + ((n : ℝ) + 1) * (α - E) =
              (H 0 + (n : ℝ) * (α - E)) + (α - E) := by ring
          _ ≤ H ((f ^ n) 0) + (α - E) := add_le_add ih.1 le_rfl
          _ ≤ H (f ((f ^ n) 0)) := by linarith [h.1]
      · calc
          H (f ((f ^ n) 0)) ≤ H ((f ^ n) 0) + (α + E) := by linarith [h.2]
          _ ≤ (H 0 + (n : ℝ) * (α + E)) + (α + E) :=
            add_le_add ih.2 le_rfl
          _ = H 0 + ((n : ℝ) + 1) * (α + E) := by ring
  have hzero := abs_le.mp (hB 0)
  simp only [sub_zero] at hzero
  have hbound (n : ℕ) :
      |(f ^ (n + 1)) 0 / ((n : ℝ) + 1) - α| ≤
        E + (2 * B) / ((n : ℝ) + 1) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hi := hiter (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hi
    have hp := abs_le.mp (hB ((f ^ (n + 1)) 0))
    have hnum :
        |(f ^ (n + 1)) 0 - ((n : ℝ) + 1) * α| ≤
          ((n : ℝ) + 1) * E + 2 * B := by
      apply abs_le.mpr
      constructor <;> nlinarith [hi.1, hi.2, hp.1, hp.2, hzero.1, hzero.2]
    have he :
        (f ^ (n + 1)) 0 / ((n : ℝ) + 1) - α =
          ((f ^ (n + 1)) 0 - ((n : ℝ) + 1) * α) / ((n : ℝ) + 1) := by
      field_simp [ne_of_gt hn] <;> ring
    rw [he, abs_div, abs_of_pos hn]
    calc
      _ ≤ (((n : ℝ) + 1) * E + 2 * B) / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right hnum hn.le
      _ = E + (2 * B) / ((n : ℝ) + 1) := by
        field_simp [ne_of_gt hn] <;> ring
  have hvanish :
      Tendsto (fun n : ℕ => (2 * B) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 * B)).comp
        (tendsto_add_atTop_nat 1)
  have hright : Tendsto (fun n : ℕ => E + (2 * B) / ((n : ℝ) + 1))
      atTop (𝓝 E) := by
    simpa only [add_zero] using tendsto_const_nhds.add hvanish
  have hleft : Tendsto
      (fun n : ℕ => |(f ^ (n + 1)) 0 / ((n : ℝ) + 1) - α|)
      atTop (𝓝 |f.translationNumber - α|) :=
    (f.tendsto_translation_number₀'.sub tendsto_const_nhds).abs
  exact le_of_tendsto_of_tendsto' hleft hright hbound

/-- The pointwise corrected displacement, with its explicit uniform
quadratic error. No rotation number or transformed displacement is assumed. -/
theorem n04b_bounded_corrector_displacement
    (F g ψ : ℝ → ℝ) (T c q η M L : ℝ)
    (hL : 0 ≤ L)
    (hψ : ∀ x : ℝ, |c + ψ x| ≤ M)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hcorrect : ∀ x : ℝ, g (x + T) - g x = -ψ x)
    (hrem : ∀ x : ℝ, |F x - x - T - q * (c + ψ x)| ≤ |q| * η)
    (x : ℝ) :
    |(F x + q * g (F x)) - (x + q * g x) - (T + q * c)| ≤
      |q| * η + q ^ 2 * L * (M + η) := by
  have hmove : |F x - (x + T)| ≤ |q| * (M + η) := by
    calc
      _ = |(F x - x - T - q * (c + ψ x)) + q * (c + ψ x)| := by
        congr 1
        ring
      _ ≤ |F x - x - T - q * (c + ψ x)| + |q * (c + ψ x)| :=
        abs_add_le _ _
      _ ≤ |q| * η + |q| * M := by
        rw [abs_mul]
        exact add_le_add (hrem x) (mul_le_mul_of_nonneg_left (hψ x) (abs_nonneg q))
      _ = _ := by ring
  have hcorrect' : g (x + T) = g x - ψ x := by
    linarith [hcorrect x]
  have he :
      (F x + q * g (F x)) - (x + q * g x) - (T + q * c) =
        (F x - x - T - q * (c + ψ x)) + q * (g (F x) - g (x + T)) := by
    rw [hcorrect']
    ring
  rw [he]
  calc
    _ ≤ |F x - x - T - q * (c + ψ x)| + |q * (g (F x) - g (x + T))| :=
      abs_add_le _ _
    _ ≤ |q| * η + |q| * (L * |F x - (x + T)|) := by
      rw [abs_mul]
      exact add_le_add (hrem x)
        (mul_le_mul_of_nonneg_left (hLip (F x) (x + T)) (abs_nonneg q))
    _ ≤ |q| * η + |q| * (L * (|q| * (M + η))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmove hL) (abs_nonneg q))
    _ = |q| * η + |q| ^ 2 * L * (M + η) := by ring
    _ = |q| * η + q ^ 2 * L * (M + η) := by rw [sq_abs]

/-- A true monotone degree-one lift with a uniform first-order expansion
has the stated quantitative translation-number expansion. -/
theorem n04b_translationNumber_corrector_estimate
    (f : CircleDeg1Lift) (g ψ : ℝ → ℝ) (T c q η M L B : ℝ)
    (hL : 0 ≤ L)
    (hg : ∀ x : ℝ, |g x| ≤ B)
    (hψ : ∀ x : ℝ, |c + ψ x| ≤ M)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hcorrect : ∀ x : ℝ, g (x + T) - g x = -ψ x)
    (hrem : ∀ x : ℝ, |f x - x - T - q * (c + ψ x)| ≤ |q| * η) :
    |f.translationNumber - (T + q * c)| ≤
      |q| * η + q ^ 2 * L * (M + η) := by
  apply n04b_translationNumber_bound_of_bounded_corrector
    f (fun x => x + q * g x) (|q| * B) (T + q * c)
      (|q| * η + q ^ 2 * L * (M + η))
  · intro x
    rw [add_sub_cancel_left, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg x) (abs_nonneg q)
  · intro x
    exact n04b_bounded_corrector_displacement f g ψ T c q η M L
      hL hψ hLip hcorrect hrem x

end ContinuousFlexibility.Analysis

