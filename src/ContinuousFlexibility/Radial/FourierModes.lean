import ContinuousFlexibility.Radial.Gauge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual Fourier separation of the radial Jacobi operator

The two-dimensional operator and all partial derivatives below are actual
mathlib derivatives of functions. This implements the cosine sector at the
start of Section 4. Infinite Fourier reconstruction and endpoint domains
are separate obligations; no spectral or inverse statement is assumed here.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Filter
open scoped Topology BigOperators

/-- The normalized real cosine mode used in the manuscript. -/
def cosineMode (j : ℕ) (θ : ℝ) : ℝ := Real.sqrt 2 * Real.cos ((j : ℝ) * θ)

def cosineModeFirst (j : ℕ) (θ : ℝ) : ℝ :=
  -(j : ℝ) * Real.sqrt 2 * Real.sin ((j : ℝ) * θ)

/-- The actual radial two-dimensional Jacobi expression. -/
def radialPDE (w : ℝ → ℝ) (U : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  deriv (fun t => w t * deriv (fun z => U z θ) t) r +
    deriv w r / r * deriv (deriv (U r)) θ

theorem hasDerivAt_cosineMode (j : ℕ) (θ : ℝ) :
    HasDerivAt (cosineMode j) (cosineModeFirst j θ) θ := by
  have h := (((hasDerivAt_id θ).const_mul (j : ℝ)).cos).const_mul (Real.sqrt 2)
  unfold cosineMode cosineModeFirst
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

theorem hasDerivAt_cosineModeFirst (j : ℕ) (θ : ℝ) :
    HasDerivAt (cosineModeFirst j) (-(j : ℝ) ^ 2 * cosineMode j θ) θ := by
  have h := (((hasDerivAt_id θ).const_mul (j : ℝ)).sin).const_mul
    (-(j : ℝ) * Real.sqrt 2)
  unfold cosineModeFirst cosineMode
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

theorem deriv_cosineMode (j : ℕ) : deriv (cosineMode j) = cosineModeFirst j := by
  funext θ
  exact (hasDerivAt_cosineMode j θ).deriv

theorem deriv_deriv_cosineMode (j : ℕ) (θ : ℝ) :
    deriv (deriv (cosineMode j)) θ = -(j : ℝ) ^ 2 * cosineMode j θ := by
  rw [deriv_cosineMode]
  exact (hasDerivAt_cosineModeFirst j θ).deriv

theorem deriv_deriv_const_mul_cosineMode (c : ℝ) (j : ℕ) (θ : ℝ) :
    deriv (deriv (fun t => c * cosineMode j t)) θ =
      c * (-(j : ℝ) ^ 2 * cosineMode j θ) := by
  have heq : deriv (fun t => c * cosineMode j t) =
      (fun t => c * cosineModeFirst j t) := by
    funext t
    exact ((hasDerivAt_cosineMode j t).const_mul c).deriv
  rw [heq]
  exact ((hasDerivAt_cosineModeFirst j θ).const_mul c).deriv

/-- The scalar modal operator is genuinely the action of the 2D operator
on a separated cosine field. The flux differentiability is the usual
second-order radial regularity of the supplied function. -/
theorem radialPDE_cosine_lift {r θ : ℝ} {w u : ℝ → ℝ} (j : ℕ)
    (hu : ∀ᶠ t in 𝓝 r, DifferentiableAt ℝ u t)
    (hflux : DifferentiableAt ℝ (fun t => w t * deriv u t) r) :
    radialPDE w (fun t φ => u t * cosineMode j φ) r θ =
      radialJacobi ((j : ℝ) ^ 2) w u r * cosineMode j θ := by
  have heq : (fun t => w t * deriv (fun z => u z * cosineMode j θ) t) =ᶠ[𝓝 r]
      (fun t => (w t * deriv u t) * cosineMode j θ) := by
    filter_upwards [hu] with t ht
    rw [(ht.hasDerivAt.mul_const (cosineMode j θ)).deriv]
    ring
  have hd := (hflux.hasDerivAt.mul_const (cosineMode j θ)).congr_of_eventuallyEq heq
  unfold radialPDE
  rw [hd.deriv, deriv_deriv_const_mul_cosineMode]
  unfold radialJacobi
  ring

/-- The actual first angular derivative of a finite cosine expansion. -/
theorem deriv_finite_cosine_sum (J : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    deriv (fun t => ∑ j ∈ J, c j * cosineMode j t) θ =
      ∑ j ∈ J, c j * cosineModeFirst j θ :=
  (HasDerivAt.fun_sum (fun j _ => (hasDerivAt_cosineMode j θ).const_mul (c j))).deriv

theorem deriv_deriv_finite_cosine_sum (J : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    deriv (deriv (fun t => ∑ j ∈ J, c j * cosineMode j t)) θ =
      ∑ j ∈ J, c j * (-(j : ℝ) ^ 2 * cosineMode j θ) := by
  have heq : deriv (fun t => ∑ j ∈ J, c j * cosineMode j t) =
      (fun t => ∑ j ∈ J, c j * cosineModeFirst j t) := by
    funext t
    exact deriv_finite_cosine_sum J c t
  rw [heq]
  exact (HasDerivAt.fun_sum
    (fun j _ => (hasDerivAt_cosineModeFirst j θ).const_mul (c j))).deriv

/-- Finite modal separation, with actual derivatives throughout. This is
the algebraic/differential stage before infinite Fourier reconstruction. -/
theorem radialPDE_finite_cosine_sum (J : Finset ℕ) (u : ℕ → ℝ → ℝ)
    (w : ℝ → ℝ) (r θ : ℝ)
    (hu : ∀ j ∈ J, Differentiable ℝ (u j))
    (hflux : ∀ j ∈ J, DifferentiableAt ℝ (fun t => w t * deriv (u j) t) r) :
    radialPDE w (fun t φ => ∑ j ∈ J, u j t * cosineMode j φ) r θ =
      ∑ j ∈ J, radialJacobi ((j : ℝ) ^ 2) w (u j) r * cosineMode j θ := by
  have hd (t : ℝ) : deriv (fun z => ∑ j ∈ J, u j z * cosineMode j θ) t =
      ∑ j ∈ J, deriv (u j) t * cosineMode j θ :=
    (HasDerivAt.fun_sum
      (fun j hj => ((hu j hj t).hasDerivAt.mul_const (cosineMode j θ)))).deriv
  have heq : (fun t => w t * deriv (fun z => ∑ j ∈ J, u j z * cosineMode j θ) t) =ᶠ[𝓝 r]
      (fun t => ∑ j ∈ J, (w t * deriv (u j) t) * cosineMode j θ) := by
    filter_upwards [] with t
    rw [hd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hf := (HasDerivAt.fun_sum
    (fun j hj => (hflux j hj).hasDerivAt.mul_const (cosineMode j θ))).congr_of_eventuallyEq heq
  unfold radialPDE
  rw [hf.deriv, deriv_deriv_finite_cosine_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold radialJacobi
  ring

theorem cosineMode_even (j : ℕ) : Function.Even (cosineMode j) := by
  intro θ
  unfold cosineMode
  rw [mul_neg, Real.cos_neg]

/-- The half-turn symmetry is precisely the even-frequency sector. -/
theorem cosineMode_even_frequency_periodic (n : ℕ) :
    Function.Periodic (cosineMode (2 * n)) Real.pi := by
  intro θ
  unfold cosineMode
  have h : ((2 * n : ℕ) : ℝ) * (θ + Real.pi) =
      ((2 * n : ℕ) : ℝ) * θ + (n : ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [h, Real.cos_add_nat_mul_two_pi]

theorem finite_even_cosine_sum_even (J : Finset ℕ) (c : ℕ → ℝ) :
    Function.Even (fun θ => ∑ n ∈ J, c n * cosineMode (2 * n) θ) := by
  intro θ
  apply Finset.sum_congr rfl
  intro n _
  rw [cosineMode_even (2 * n) θ]

theorem finite_even_cosine_sum_periodic (J : Finset ℕ) (c : ℕ → ℝ) :
    Function.Periodic (fun θ => ∑ n ∈ J, c n * cosineMode (2 * n) θ) Real.pi := by
  intro θ
  apply Finset.sum_congr rfl
  intro n _
  rw [cosineMode_even_frequency_periodic n θ]

end

end ContinuousFlexibility.Radial
