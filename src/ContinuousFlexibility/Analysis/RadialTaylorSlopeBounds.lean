import ContinuousFlexibility.Analysis.AngularTaylorPolynomial
import ContinuousFlexibility.Analysis.PositiveAngularTaylorInterpolation

/-!
# Positive radial Taylor slopes and a fixed mass margin

The derivative of the existing Taylor polynomial is the shifted Taylor
polynomial, with actual differentiation and factorial cancellation.
Uniform finite endpoint jets therefore give a positive slope on one
collar chosen before the state. A separate elementary choice also makes
the endpoint mass smaller than the fixed reference exit mass.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_boundaryTaylorPolynomial_radial
    (n : ℕ) (c r θ : ℝ) (A : ℕ → ℝ → ℝ) :
    HasDerivAt (fun x => boundaryTaylorPolynomial (n + 1) c A (x, θ))
      (boundaryTaylorPolynomial n c (fun j => A (j + 1)) (r, θ)) r := by
  have hd : HasDerivAt
      (fun x => ∑ j ∈ Finset.range (n + 1),
        A (j + 1) θ / ((j + 1).factorial : ℝ) * (x - c) ^ (j + 1))
      (boundaryTaylorPolynomial n c (fun j => A (j + 1)) (r, θ)) r := by
    unfold boundaryTaylorPolynomial
    apply HasDerivAt.fun_sum
    intro j _
    have hj := (((hasDerivAt_id r).sub_const c).fun_pow (j + 1)).const_mul
      (A (j + 1) θ / ((j + 1).factorial : ℝ))
    apply hj.congr_deriv
    simp only [Nat.add_sub_cancel, mul_one]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfact : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hsucc : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hfact, hsucc]
    <;> ring
  have he : (fun x => boundaryTaylorPolynomial (n + 1) c A (x, θ)) =
      fun x => (∑ j ∈ Finset.range (n + 1),
        A (j + 1) θ / ((j + 1).factorial : ℝ) * (x - c) ^ (j + 1)) + A 0 θ := by
    funext x
    unfold boundaryTaylorPolynomial
    rw [Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
  rw [he]
  exact hd.add_const (A 0 θ)

/-- The actual Taylor slope stays positive using only the finite raw
boundary jet bounds. The upper bound is independent of the collar width. -/
theorem boundaryTaylorPolynomial_radial_slope_bounds
    {n : ℕ} {A : ℕ → ℝ → ℝ} {c r θ δ κ M : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hM : 0 ≤ M) (hr : |r - c| ≤ δ)
    (hpositive : κ ≤ A 1 θ)
    (hjets : ∀ j, 1 ≤ j → j ≤ n + 1 → |A j θ| ≤ M)
    (hsmall : ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2) :
    κ / 2 ≤ deriv (fun x => boundaryTaylorPolynomial (n + 1) c A (x, θ)) r ∧
      |deriv (fun x => boundaryTaylorPolynomial (n + 1) c A (x, θ)) r| ≤
        M + ((n + 1 : ℕ) : ℝ) * M := by
  rw [(hasDerivAt_boundaryTaylorPolynomial_radial n c r θ A).deriv]
  have he := abs_boundaryTaylorPolynomial_sub_zero_le
    (n := n) (A := fun j => A (j + 1)) hδ hδone hM hr
    (fun j _ hj => hjets (j + 1) (by omega) (by omega))
  have he' : |boundaryTaylorPolynomial n c (fun j => A (j + 1)) (r, θ) -
      A 1 θ| ≤ ((n + 1 : ℕ) : ℝ) * M * δ := he
  refine ⟨?_, ?_⟩
  · have hlo := (abs_le.mp he').1
    linarith
  · have hAone := hjets 1 le_rfl (by omega)
    have htriangle : |boundaryTaylorPolynomial n c (fun j => A (j + 1)) (r, θ)| ≤
        |boundaryTaylorPolynomial n c (fun j => A (j + 1)) (r, θ) - A 1 θ| +
          |A 1 θ| := by
      simpa only [sub_add_cancel] using
        abs_add_le (boundaryTaylorPolynomial n c (fun j => A (j + 1)) (r, θ) - A 1 θ)
          (A 1 θ)
    have hNM : 0 ≤ ((n + 1 : ℕ) : ℝ) * M :=
      mul_nonneg (Nat.cast_nonneg _) hM
    have hwidth := mul_le_mul_of_nonneg_left hδone hNM
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) * M * δ + M :=
        htriangle.trans (add_le_add he' hAone)
      _ ≤ M + ((n + 1 : ℕ) : ℝ) * M := by linarith

/-- Both numeric margins are selected from the fixed raw constants.
The forbidden closed set may encode the normalization support; the
same two endpoint cutoffs work for every member of an indexed family. -/
theorem exists_positiveEndpoint_mass_collar
    {F : Set ℝ} (hF : IsClosed F) {l r ρ κ Mjet Mslope m : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hMjet : 0 ≤ Mjet)
    (hMslope : 0 ≤ Mslope) (hm : 0 < m) (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧
      Disjoint (Metric.ball l δ) F ∧ Disjoint (Metric.ball r δ) F ∧
      ((n + 1 : ℕ) : ℝ) * Mjet * δ ≤ κ / 2 ∧
      2 * Mslope * δ ≤ m / 2 := by
  have hden : 0 < 4 * (Mslope + 1) := by positivity
  have hρ' : 0 < min ρ (m / (4 * (Mslope + 1))) :=
    lt_min hρ (div_pos hm hden)
  obtain ⟨δ, hδ, hδρ, hδone, hgap, hleft, hright, hsmall⟩ :=
    exists_positiveAngularTaylor_collar hF hl hr hlr hρ' hκ hMjet n
  have hρbound : δ < ρ := hδρ.trans_le (min_le_left _ _)
  have hmass : δ * (4 * (Mslope + 1)) < m :=
    (lt_div_iff₀ hden).mp (hδρ.trans_le (min_le_right _ _))
  refine ⟨δ, hδ, hρbound, hδone, hgap, hleft, hright, hsmall, ?_⟩
  nlinarith

end ContinuousFlexibility.Analysis

