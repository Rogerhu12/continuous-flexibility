import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An explicit finite-Fourier corrector for a nonresonant translation

The correction g solves g(θ+T)-g(θ)=-(a cos(2θ)+b sin(2θ)).
Its denominator is 4 sin(T)^2. Thus one Fourier mode needs only
sin(T) ≠ 0, and irrationality of T/π is more than sufficient.
Both the physical period π and its normalized period-one version are
given explicitly, with a uniform Lipschitz bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

def n04bSecondHarmonic (a b θ : ℝ) : ℝ :=
  a * Real.cos (2 * θ) + b * Real.sin (2 * θ)

def n04bFourierDet (T : ℝ) : ℝ :=
  (Real.cos (2 * T) - 1) ^ 2 + Real.sin (2 * T) ^ 2

def n04bFourierCosCoeff (T a b : ℝ) : ℝ :=
  (-a * (Real.cos (2 * T) - 1) + b * Real.sin (2 * T)) / n04bFourierDet T

def n04bFourierSinCoeff (T a b : ℝ) : ℝ :=
  (-a * Real.sin (2 * T) - b * (Real.cos (2 * T) - 1)) / n04bFourierDet T

def n04bFourierCorrector (T a b θ : ℝ) : ℝ :=
  n04bFourierCosCoeff T a b * Real.cos (2 * θ) +
    n04bFourierSinCoeff T a b * Real.sin (2 * θ)

def n04bFourierLipschitz (T a b : ℝ) : ℝ :=
  2 * (|n04bFourierCosCoeff T a b| + |n04bFourierSinCoeff T a b|)

theorem n04bFourierDet_eq (T : ℝ) :
    n04bFourierDet T = 4 * Real.sin T ^ 2 := by
  calc
    n04bFourierDet T = 2 - 2 * Real.cos (2 * T) := by
      dsimp only [n04bFourierDet]
      nlinarith [Real.sin_sq_add_cos_sq (2 * T)]
    _ = 4 * Real.sin T ^ 2 := by
      nlinarith [Real.cos_two_mul T, Real.sin_sq_add_cos_sq T]

theorem n04bFourierDet_pos {T : ℝ} (hT : Real.sin T ≠ 0) :
    0 < n04bFourierDet T := by
  rw [n04bFourierDet_eq]
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero hT)

theorem n04b_sin_ne_zero_of_irrational {T : ℝ}
    (hT : Irrational (T / Real.pi)) : Real.sin T ≠ 0 := by
  intro hsin
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  apply hT.ne_rational n 1
  rw [← hn]
  field_simp [Real.pi_ne_zero]
  simp

theorem n04bFourierCorrector_coefficients {T : ℝ} (hT : Real.sin T ≠ 0)
    (a b : ℝ) :
    n04bFourierCosCoeff T a b * (Real.cos (2 * T) - 1) +
        n04bFourierSinCoeff T a b * Real.sin (2 * T) = -a ∧
      -n04bFourierCosCoeff T a b * Real.sin (2 * T) +
        n04bFourierSinCoeff T a b * (Real.cos (2 * T) - 1) = -b := by
  have hd : n04bFourierDet T ≠ 0 := ne_of_gt (n04bFourierDet_pos hT)
  dsimp only [n04bFourierCosCoeff, n04bFourierSinCoeff]
  constructor <;> field_simp [hd] <;> dsimp only [n04bFourierDet] <;> ring

/-- The cohomological equation is solved by the displayed two Fourier
coefficients, without an assumed inverse or a convergence argument. -/
theorem n04bFourierCorrector_difference {T : ℝ} (hT : Real.sin T ≠ 0)
    (a b θ : ℝ) :
    n04bFourierCorrector T a b (θ + T) - n04bFourierCorrector T a b θ =
      -n04bSecondHarmonic a b θ := by
  obtain ⟨hc, hs⟩ := n04bFourierCorrector_coefficients hT a b
  dsimp only [n04bFourierCorrector, n04bSecondHarmonic]
  rw [show 2 * (θ + T) = 2 * θ + 2 * T by ring, Real.cos_add, Real.sin_add]
  linear_combination Real.cos (2 * θ) * hc + Real.sin (2 * θ) * hs

theorem n04bFourierCorrector_periodic (T a b : ℝ) :
    Function.Periodic (n04bFourierCorrector T a b) Real.pi := by
  intro θ
  dsimp only [n04bFourierCorrector]
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem n04bFourierCorrector_continuous (T a b : ℝ) :
    Continuous (n04bFourierCorrector T a b) := by
  exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul
    (n04bFourierCosCoeff T a b)).add
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul
      (n04bFourierSinCoeff T a b))

theorem n04bFourierLipschitz_nonneg (T a b : ℝ) :
    0 ≤ n04bFourierLipschitz T a b := by
  unfold n04bFourierLipschitz
  positivity

theorem n04bFourierCorrector_lipschitz (T a b x y : ℝ) :
    |n04bFourierCorrector T a b x - n04bFourierCorrector T a b y| ≤
      n04bFourierLipschitz T a b * |x - y| := by
  let A : ℝ := n04bFourierCosCoeff T a b
  let B : ℝ := n04bFourierSinCoeff T a b
  calc
    _ = |A * (Real.cos (2 * x) - Real.cos (2 * y)) +
        B * (Real.sin (2 * x) - Real.sin (2 * y))| := by
      congr 1
      dsimp only [n04bFourierCorrector, A, B]
      ring
    _ ≤ |A| * |Real.cos (2 * x) - Real.cos (2 * y)| +
        |B| * |Real.sin (2 * x) - Real.sin (2 * y)| := by
      simpa only [abs_mul] using
        (abs_add_le (A * (Real.cos (2 * x) - Real.cos (2 * y)))
          (B * (Real.sin (2 * x) - Real.sin (2 * y))))
    _ ≤ |A| * |2 * x - 2 * y| + |B| * |2 * x - 2 * y| :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le (2 * x) (2 * y))
          (abs_nonneg A))
        (mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le (2 * x) (2 * y))
          (abs_nonneg B))
    _ = _ := by
      rw [show 2 * x - 2 * y = 2 * (x - y) by ring, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      dsimp only [n04bFourierLipschitz, A, B]
      ring

theorem n04bSecondHarmonic_abs_le (a b θ : ℝ) :
    |n04bSecondHarmonic a b θ| ≤ |a| + |b| := by
  calc
    _ ≤ |a| * |Real.cos (2 * θ)| + |b| * |Real.sin (2 * θ)| := by
      simpa only [n04bSecondHarmonic, abs_mul] using
        abs_add_le (a * Real.cos (2 * θ)) (b * Real.sin (2 * θ))
    _ ≤ |a| * 1 + |b| * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg b))
    _ = _ := by ring

/-- The finite corrector is uniformly bounded, so its endpoint terms
vanish in the orbit-average definition of translation number. -/
theorem n04bFourierCorrector_abs_le (T a b θ : ℝ) :
    |n04bFourierCorrector T a b θ| ≤
      |n04bFourierCosCoeff T a b| + |n04bFourierSinCoeff T a b| :=
  n04bSecondHarmonic_abs_le (n04bFourierCosCoeff T a b)
    (n04bFourierSinCoeff T a b) θ

/-- The normalized corrector uses period one and the same Lipschitz constant. -/
def n04bUnitFourierCorrector (T a b x : ℝ) : ℝ :=
  n04bFourierCorrector T a b (Real.pi * x) / Real.pi

theorem n04bUnitFourierCorrector_periodic (T a b : ℝ) :
    Function.Periodic (n04bUnitFourierCorrector T a b) 1 := by
  intro x
  dsimp only [n04bUnitFourierCorrector]
  rw [mul_add, mul_one, n04bFourierCorrector_periodic T a b]

theorem n04bUnitFourierCorrector_continuous (T a b : ℝ) :
    Continuous (n04bUnitFourierCorrector T a b) :=
  ((n04bFourierCorrector_continuous T a b).comp
    (continuous_const.mul continuous_id)).div_const Real.pi

theorem n04bUnitFourierCorrector_lipschitz (T a b x y : ℝ) :
    |n04bUnitFourierCorrector T a b x - n04bUnitFourierCorrector T a b y| ≤
      n04bFourierLipschitz T a b * |x - y| := by
  dsimp only [n04bUnitFourierCorrector]
  rw [← sub_div, abs_div, abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ Real.pi_pos).mpr
  calc
    _ ≤ n04bFourierLipschitz T a b * |Real.pi * x - Real.pi * y| :=
      n04bFourierCorrector_lipschitz T a b (Real.pi * x) (Real.pi * y)
    _ = _ := by
      rw [show Real.pi * x - Real.pi * y = Real.pi * (x - y) by ring,
        abs_mul, abs_of_pos Real.pi_pos]
      ring

end ContinuousFlexibility.Analysis
