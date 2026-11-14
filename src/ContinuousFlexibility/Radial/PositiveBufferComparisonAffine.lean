module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Affine changes of the positive-buffer coordinate

One affine change handles translations, scalings, and the reflection
needed for the left endpoint.  The normalized potential carries the
square of the coordinate slope; the energy integral carries its
absolute value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff

theorem positiveBuffer_affine_hasDerivAt {a b x d : ℝ} {u : ℝ → ℝ}
    (hu : HasDerivAt u d (a + b * x)) :
    HasDerivAt (fun t : ℝ => u (a + b * t)) (b * d) x := by
  have h := hu.comp x (((hasDerivAt_id x).const_mul b).const_add a)
  convert h using 1 <;> simp only [Function.comp_def, id_eq, mul_one] <;> ring

theorem positiveBuffer_affine_contDiff {n : ℕ∞ω} {u : ℝ → ℝ}
    (hu : ContDiff ℝ n u) (a b : ℝ) :
    ContDiff ℝ n (fun t : ℝ => u (a + b * t)) :=
  hu.comp (contDiff_const.add (contDiff_const.mul contDiff_id))

theorem positiveBuffer_affine_contDiffOn {n : ℕ∞ω} {u : ℝ → ℝ} {J : Set ℝ}
    (hu : ContDiffOn ℝ n u J) (a b : ℝ) :
    ContDiffOn ℝ n (fun t : ℝ => u (a + b * t))
      ((fun t : ℝ => a + b * t) ⁻¹' J) := by
  apply hu.comp (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  intro x hx
  exact hx

theorem positiveBuffer_affine_contDiffAt {n : ℕ∞ω} {u : ℝ → ℝ} {a b x : ℝ}
    (hu : ContDiffAt ℝ n u (a + b * x)) :
    ContDiffAt ℝ n (fun t : ℝ => u (a + b * t)) x :=
  hu.comp x (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffAt

/-- Both derivatives of a homogeneous solution under the same affine
coordinate change. -/
theorem positiveBuffer_affine_homogeneous {J : Set ℝ} {u du q : ℝ → ℝ}
    (hu : ∀ x ∈ J, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ J, HasDerivAt du (q x * u x) x)
    (a b : ℝ) {t : ℝ} (ht : a + b * t ∈ J) :
    HasDerivAt (fun s : ℝ => u (a + b * s)) (b * du (a + b * t)) t ∧
      HasDerivAt (fun s : ℝ => b * du (a + b * s))
        ((b ^ 2 * q (a + b * t)) * u (a + b * t)) t := by
  refine ⟨positiveBuffer_affine_hasDerivAt (hu _ ht), ?_⟩
  have h := (positiveBuffer_affine_hasDerivAt (hdu _ ht)).const_mul b
  convert h using 1 <;> ring

/-- Ordinary derivatives of a reflection, with the sign in the first
derivative and no sign in the second derivative. -/
theorem positiveBuffer_reflection_deriv {u : ℝ → ℝ} {x : ℝ}
    (hu : DifferentiableAt ℝ u (-x)) :
    deriv (fun t : ℝ => u (-t)) x = -deriv u (-x) := by
  have hd : HasDerivAt u (deriv u (-x)) (-x) := hu.hasDerivAt
  have hd' : HasDerivAt u (deriv u (-x)) (0 + (-1) * x) := by
    simpa only [zero_add, neg_one_mul] using hd
  have h := positiveBuffer_affine_hasDerivAt (a := 0) (b := -1) (x := x)
    hd'
  simpa only [zero_add, neg_one_mul] using h.deriv

theorem positiveBuffer_reflection_contDiff {n : ℕ∞ω} {u : ℝ → ℝ}
    (hu : ContDiff ℝ n u) : ContDiff ℝ n (fun x : ℝ => u (-x)) := by
  simpa only [zero_add, neg_one_mul] using positiveBuffer_affine_contDiff hu 0 (-1)

theorem positiveBuffer_reflection_contDiffOn {n : ℕ∞ω} {u : ℝ → ℝ} {J : Set ℝ}
    (hu : ContDiffOn ℝ n u J) :
    ContDiffOn ℝ n (fun x : ℝ => u (-x)) ((fun x : ℝ => -x) ⁻¹' J) := by
  simpa only [zero_add, neg_one_mul] using positiveBuffer_affine_contDiffOn hu 0 (-1)

theorem positiveBuffer_reflection_homogeneous {J : Set ℝ} {u du q : ℝ → ℝ}
    (hu : ∀ x ∈ J, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ J, HasDerivAt du (q x * u x) x)
    {t : ℝ} (ht : -t ∈ J) :
    HasDerivAt (fun s : ℝ => u (-s)) (-du (-t)) t ∧
      HasDerivAt (fun s : ℝ => -du (-s)) (q (-t) * u (-t)) t := by
  simpa only [zero_add, neg_one_mul, neg_sq, one_pow, one_mul] using
    positiveBuffer_affine_homogeneous hu hdu 0 (-1) (by simpa using ht)

/-- Lebesgue change of variables on the preimage of an arbitrary
measurable set, retaining the absolute Jacobian. -/
theorem positiveBuffer_affine_setIntegral (f : ℝ → ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (a b : ℝ) :
    (∫ x in (fun t : ℝ => a + b * t) ⁻¹' s, f (a + b * x)) =
      |b|⁻¹ * ∫ y in s, f y := by
  have hmeas : Measurable (fun t : ℝ => a + b * t) :=
    measurable_const.add (measurable_const.mul measurable_id)
  rw [← integral_indicator (hs.preimage hmeas), ← integral_indicator hs]
  have heq : ((fun t : ℝ => a + b * t) ⁻¹' s).indicator
      (fun x => f (a + b * x)) = fun x => (s.indicator f) (a + b * x) := by
    funext x
    by_cases hx : a + b * x ∈ s
    · have hx' : x ∈ (fun t : ℝ => a + b * t) ⁻¹' s := hx
      rw [indicator_of_mem hx', indicator_of_mem hx]
    · have hx' : x ∉ (fun t : ℝ => a + b * t) ⁻¹' s := hx
      rw [indicator_of_notMem hx', indicator_of_notMem hx]
  rw [heq, Measure.integral_comp_mul_left (fun y => (s.indicator f) (a + y)) b,
    integral_add_left_eq_self, smul_eq_mul, abs_inv]

/-- The energy transforms by the absolute coordinate slope when the
potential transforms by its square. -/
theorem positiveBuffer_affine_energy_change {s : Set ℝ} (hs : MeasurableSet s)
    (u du V : ℝ → ℝ) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (∫ x in (fun t : ℝ => a + b * t) ⁻¹' s,
      (b * du (a + b * x)) ^ 2 + (b ^ 2 * V (a + b * x)) * u (a + b * x) ^ 2) =
      |b| * ∫ y in s, du y ^ 2 + V y * u y ^ 2 := by
  have heq : (fun x : ℝ => (b * du (a + b * x)) ^ 2 +
      (b ^ 2 * V (a + b * x)) * u (a + b * x) ^ 2) =
      fun x => b ^ 2 * (du (a + b * x) ^ 2 + V (a + b * x) * u (a + b * x) ^ 2) := by
    funext x
    ring
  rw [heq, integral_const_mul,
    positiveBuffer_affine_setIntegral (fun y => du y ^ 2 + V y * u y ^ 2) hs a b]
  have hcancel : b ^ 2 * |b|⁻¹ = |b| := by
    rw [← sq_abs b, pow_two, mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hb), mul_one]
  rw [← mul_assoc, hcancel]

/-- Reflection of the full exterior energy, with the open-halfline
convention at both endpoints. -/
theorem positiveBuffer_reflection_energy (u du V : ℝ → ℝ) (c : ℝ) :
    (∫ x in Ioi (-c), (-du (-x)) ^ 2 + V (-x) * u (-x) ^ 2) =
      ∫ y in Iio c, du y ^ 2 + V y * u y ^ 2 := by
  simpa only [neg_sq, neg_neg, integral_Iic_eq_integral_Iio] using
    (integral_comp_neg_Ioi (-c) (fun y => du y ^ 2 + V y * u y ^ 2))

/-- Reflection preserves the actual derivative energy, not merely an
independent derivative variable. -/
theorem positiveBuffer_reflection_deriv_energy {u V : ℝ → ℝ} (c : ℝ)
    (hu : ∀ y ∈ Iio c, DifferentiableAt ℝ u y) :
    (∫ x in Ioi (-c), deriv (fun t : ℝ => u (-t)) x ^ 2 + V (-x) * u (-x) ^ 2) =
      ∫ y in Iio c, deriv u y ^ 2 + V y * u y ^ 2 := by
  calc
    _ = ∫ x in Ioi (-c), (-deriv u (-x)) ^ 2 + V (-x) * u (-x) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change deriv (fun t : ℝ => u (-t)) x ^ 2 + V (-x) * u (-x) ^ 2 =
        (-deriv u (-x)) ^ 2 + V (-x) * u (-x) ^ 2
      have hx' : -c < x := hx
      have hneg : -x ∈ Iio c := by change -x < c; linarith
      rw [positiveBuffer_reflection_deriv (hu (-x) hneg)]
    _ = _ := positiveBuffer_reflection_energy u (deriv u) V c

end ContinuousFlexibility.Radial
