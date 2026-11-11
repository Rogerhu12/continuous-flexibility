import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Spectral projections for an integer angular frequency

The bounded resolvent `(I + Λ)⁻¹` of an angular frequency has spectrum in
`{0} ∪ {1 / (n + 1) | n : ℕ}`. Continuous triangular functions isolate
each nonzero spectral value. Their functional calculus gives the spectral
projections without a finite-multiplicity or compactness assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

/-- The nonzero spectral values of the bounded angular resolvent. -/
def angularResolventEigenvalue (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem angularResolventEigenvalue_pos (n : ℕ) : 0 < angularResolventEigenvalue n := by
  unfold angularResolventEigenvalue
  positivity

theorem angularResolventEigenvalue_strictAnti : StrictAnti angularResolventEigenvalue := by
  intro m n hmn
  apply one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < (m : ℝ) + 1)
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  linarith

private def angularResolventUpper (n : ℕ) : ℝ := if n = 0 then 2 else 1 / (n : ℝ)

private theorem angularResolvent_lt_upper (n : ℕ) :
    angularResolventEigenvalue n < angularResolventUpper n := by
  by_cases hn : n = 0
  · subst n
    norm_num [angularResolventEigenvalue, angularResolventUpper]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [angularResolventUpper, if_neg hn, angularResolventEigenvalue]
    exact one_div_lt_one_div_of_lt hnR (lt_add_one _)

private theorem angularResolventUpper_le_of_lt {m n : ℕ} (hmn : m < n) :
    angularResolventUpper n ≤ angularResolventEigenvalue m := by
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_le m |>.trans_lt hmn)
  simp only [angularResolventUpper, if_neg hn, angularResolventEigenvalue]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
  exact_mod_cast Nat.succ_le_of_lt hmn

/-- A continuous function equal to one at the `n`th reciprocal frequency
and zero at every other spectral value, including zero. -/
def angularReciprocalBump (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min
    ((x - angularResolventEigenvalue (n + 1)) /
      (angularResolventEigenvalue n - angularResolventEigenvalue (n + 1)))
    ((angularResolventUpper n - x) /
      (angularResolventUpper n - angularResolventEigenvalue n)))

theorem continuous_angularReciprocalBump (n : ℕ) : Continuous (angularReciprocalBump n) := by
  unfold angularReciprocalBump
  fun_prop

private theorem angularReciprocalBump_eq_zero_of_le (n : ℕ) {x : ℝ}
    (hx : x ≤ angularResolventEigenvalue (n + 1)) : angularReciprocalBump n x = 0 := by
  unfold angularReciprocalBump
  apply max_eq_left
  exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (sub_nonneg.mpr (angularResolventEigenvalue_strictAnti (Nat.lt_succ_self n)).le))

private theorem angularReciprocalBump_eq_zero_of_ge (n : ℕ) {x : ℝ}
    (hx : angularResolventUpper n ≤ x) : angularReciprocalBump n x = 0 := by
  unfold angularReciprocalBump
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (sub_nonneg.mpr (angularResolvent_lt_upper n).le))

@[simp] theorem angularReciprocalBump_zero (n : ℕ) : angularReciprocalBump n 0 = 0 :=
  angularReciprocalBump_eq_zero_of_le n (angularResolventEigenvalue_pos _).le

@[simp] theorem angularReciprocalBump_self (n : ℕ) :
    angularReciprocalBump n (angularResolventEigenvalue n) = 1 := by
  have hleft : angularResolventEigenvalue n - angularResolventEigenvalue (n + 1) ≠ 0 :=
    (sub_pos.mpr (angularResolventEigenvalue_strictAnti (Nat.lt_succ_self n))).ne'
  have hright : angularResolventUpper n - angularResolventEigenvalue n ≠ 0 :=
    (sub_pos.mpr (angularResolvent_lt_upper n)).ne'
  simp only [angularReciprocalBump, div_self hleft, div_self hright, min_self,
    max_eq_right zero_le_one]

theorem angularReciprocalBump_other {m n : ℕ} (hmn : m ≠ n) :
    angularReciprocalBump n (angularResolventEigenvalue m) = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact angularReciprocalBump_eq_zero_of_ge n (angularResolventUpper_le_of_lt hlt)
  · exact angularReciprocalBump_eq_zero_of_le n
      (angularResolventEigenvalue_strictAnti.antitone (Nat.succ_le_of_lt hgt))

theorem angularReciprocalBump_nonneg (n : ℕ) (x : ℝ) : 0 ≤ angularReciprocalBump n x :=
  le_max_left _ _

theorem angularReciprocalBump_le_one (n : ℕ) (x : ℝ) : angularReciprocalBump n x ≤ 1 := by
  apply max_le zero_le_one
  by_cases hx : x ≤ angularResolventEigenvalue n
  · apply (min_le_left _ _).trans
    apply (div_le_one (sub_pos.mpr (angularResolventEigenvalue_strictAnti
      (Nat.lt_succ_self n)))).mpr
    exact sub_le_sub_right hx _
  · apply (min_le_right _ _).trans
    apply (div_le_one (sub_pos.mpr (angularResolvent_lt_upper n))).mpr
    exact sub_le_sub_left (le_of_lt (lt_of_not_ge hx)) _

/-- The exact bounded-resolvent form of the nonnegative integer spectrum. -/
def angularReciprocalSpectrum : Set ℝ := insert 0 (range angularResolventEigenvalue)

theorem angularReciprocalBump_mul (n : ℕ) {x : ℝ} (hx : x ∈ angularReciprocalSpectrum) :
    x * angularReciprocalBump n x =
      angularResolventEigenvalue n * angularReciprocalBump n x := by
  rcases hx with rfl | ⟨m, rfl⟩
  · simp only [angularReciprocalBump_zero, mul_zero]
  · by_cases hmn : m = n
    · subst m
      rfl
    · simp only [angularReciprocalBump_other hmn, mul_zero]

theorem angularReciprocalBump_idempotent (n : ℕ) {x : ℝ}
    (hx : x ∈ angularReciprocalSpectrum) :
    angularReciprocalBump n x * angularReciprocalBump n x = angularReciprocalBump n x := by
  rcases hx with rfl | ⟨m, rfl⟩
  · simp only [angularReciprocalBump_zero, mul_zero]
  · by_cases hmn : m = n
    · subst m
      simp only [angularReciprocalBump_self, one_mul]
    · simp only [angularReciprocalBump_other hmn, mul_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral projection constructed by continuous functional calculus. -/
def angularResolventProjection (B : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  cfc (angularReciprocalBump n) B

theorem angularResolventProjection_selfAdjoint (B : H →L[ℂ] H) (n : ℕ) :
    IsSelfAdjoint (angularResolventProjection B n) := IsSelfAdjoint.cfc

theorem angularResolventProjection_norm_le (B : H →L[ℂ] H) (n : ℕ) :
    ‖angularResolventProjection B n‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro x _
  rw [Real.norm_eq_abs, abs_of_nonneg (angularReciprocalBump_nonneg n x)]
  exact angularReciprocalBump_le_one n x

theorem angularResolventProjection_eigen {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) (n : ℕ) :
    B * angularResolventProjection B n =
      angularResolventEigenvalue n • angularResolventProjection B n := by
  calc
    _ = cfc (fun x : ℝ => x * angularReciprocalBump n x) B := by
      rw [cfc_mul _ _ _ continuous_id.continuousOn
        (continuous_angularReciprocalBump n).continuousOn, cfc_id' ℝ B hB]
      rfl
    _ = cfc (fun x : ℝ => angularResolventEigenvalue n * angularReciprocalBump n x) B :=
      cfc_congr (fun x hx => angularReciprocalBump_mul n (hSpectrum hx))
    _ = _ := cfc_const_mul _ _ _ (continuous_angularReciprocalBump n).continuousOn

theorem angularResolventProjection_idempotent {B : H →L[ℂ] H}
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) (n : ℕ) :
    IsIdempotentElem (angularResolventProjection B n) := by
  change cfc (angularReciprocalBump n) B * cfc (angularReciprocalBump n) B =
    cfc (angularReciprocalBump n) B
  rw [← cfc_mul _ _ _ (continuous_angularReciprocalBump n).continuousOn
    (continuous_angularReciprocalBump n).continuousOn]
  exact cfc_congr (fun x hx => angularReciprocalBump_idempotent n (hSpectrum hx))

end ContinuousFlexibility.Analysis
