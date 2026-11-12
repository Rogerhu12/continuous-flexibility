import ContinuousFlexibility.Analysis.N07aAngularRealFourier
import ContinuousFlexibility.Analysis.SpacesTorusWaves

/-!
# Recovering one radial derivative from an actual second-order Fourier identity

The radial frequency is never truncated. A second derivative equal to a
first derivative plus an L² source controls one radial derivative at every
nonzero radial frequency; the zero radial frequency has derivative zero.
Conjugate symmetry reconstructs an actual real canonical L² class.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory ContinuousFlexibility.Statements
open scoped ComplexConjugate ENNReal

def n07aRadialSymbol (ω : ℝ) (j : SpacesTorusFrequency) : ℂ :=
  (ω : ℂ) * Complex.I * (j 0 : ℂ)

theorem n07aRadialSymbol_neg (ω : ℝ) (j : SpacesTorusFrequency) :
    n07aRadialSymbol ω (-j) = conj (n07aRadialSymbol ω j) := by
  simp only [n07aRadialSymbol, Pi.neg_apply, Int.cast_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

theorem n07aRadialSymbol_norm {ω : ℝ} (hω : 0 < ω) (j : SpacesTorusFrequency) :
    ‖n07aRadialSymbol ω j‖ = ω * ((j 0).natAbs : ℝ) := by
  simp only [n07aRadialSymbol, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hω, Complex.norm_I, mul_one,
    Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]

private theorem n07aRadialSymbol_derivative_bound {ω : ℝ} (hω : 0 < ω)
    (j : SpacesTorusFrequency) {u h g : ℂ}
    (heq : n07aRadialSymbol ω j ^ 2 * u = n07aRadialSymbol ω j * h + g) :
    ‖n07aRadialSymbol ω j * u‖ ≤ ‖h‖ + ω⁻¹ * ‖g‖ := by
  by_cases hj : j 0 = 0
  · have hz : n07aRadialSymbol ω j = 0 := by
      simp only [n07aRadialSymbol, hj, Int.cast_zero, mul_zero]
    rw [hz, zero_mul, norm_zero]
    exact add_nonneg (norm_nonneg h) (mul_nonneg (inv_nonneg.mpr hω.le) (norm_nonneg g))
  have hn : 1 ≤ (j 0).natAbs := Nat.succ_le_of_lt (Int.natAbs_pos.mpr hj)
  have hn' : (1 : ℝ) ≤ ((j 0).natAbs : ℝ) := by exact_mod_cast hn
  have hzbound : ω ≤ ‖n07aRadialSymbol ω j‖ := by
    rw [n07aRadialSymbol_norm hω]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn' hω.le
  have hzpos : 0 < ‖n07aRadialSymbol ω j‖ := hω.trans_le hzbound
  have hz : n07aRadialSymbol ω j ≠ 0 := norm_pos_iff.mp hzpos
  have hsolve : n07aRadialSymbol ω j * u = h +
      (n07aRadialSymbol ω j)⁻¹ * g := by
    apply (mul_left_cancel₀ hz)
    rw [mul_add, mul_inv_cancel_left₀ hz]
    simpa only [pow_two, mul_assoc] using heq
  rw [hsolve]
  calc
    ‖h + (n07aRadialSymbol ω j)⁻¹ * g‖ ≤
        ‖h‖ + ‖(n07aRadialSymbol ω j)⁻¹ * g‖ := norm_add_le _ _
    _ = ‖h‖ + ‖n07aRadialSymbol ω j‖⁻¹ * ‖g‖ := by rw [norm_mul, norm_inv]
    _ ≤ ‖h‖ + ω⁻¹ * ‖g‖ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hzpos hω).mpr hzbound) (norm_nonneg g))

/-- The true second-order identity places the first radial multiplier in
ℓ² without any assumption on the unknown first derivative. -/
theorem n07a_radialFirst_memℓp_of_second {ω : ℝ} (hω : 0 < ω)
    (u h g : SpacesTorusCoefficients)
    (heq : ∀ j, n07aRadialSymbol ω j ^ 2 * u j =
      n07aRadialSymbol ω j * h j + g j) :
    Memℓp (fun j => n07aRadialSymbol ω j * u j) 2 := by
  have hb := (lp.memℓp h).norm.add ((lp.memℓp g).norm.const_mul ω⁻¹)
  apply hb.mono
  intro j
  exact n07aRadialSymbol_derivative_bound hω j (heq j)

variable {S : PhysicalSpacesData} {K : CanonicalData S}

/-- The multiplier is realized in the original real canonical L² space. -/
theorem n07a_exists_radialFirst_fourier (m : ℕ) (hm : K.left m < K.right m)
    {ω : ℝ} (hω : 0 < ω) (u h g : CanonicalL2 S K m)
    (heq : ∀ j, n07aRadialSymbol ω j ^ 2 * n07aAngularFourier m hm u j =
      n07aRadialSymbol ω j * n07aAngularFourier m hm h j +
        n07aAngularFourier m hm g j) :
    ∃ d : CanonicalL2 S K m, ∀ j,
      n07aAngularFourier m hm d j =
        n07aRadialSymbol ω j * n07aAngularFourier m hm u j := by
  let v : SpacesTorusCoefficients :=
    ⟨fun j => n07aRadialSymbol ω j * n07aAngularFourier m hm u j,
      n07a_radialFirst_memℓp_of_second hω
        (n07aAngularFourier m hm u) (n07aAngularFourier m hm h)
        (n07aAngularFourier m hm g) heq⟩
  refine ⟨n07aAngularFourierInverse m hm v, ?_⟩
  have hv : ∀ j, v (-j) = conj (v j) := by
    intro j
    change n07aRadialSymbol ω (-j) * n07aAngularFourier m hm u (-j) =
      conj (n07aRadialSymbol ω j * n07aAngularFourier m hm u j)
    rw [n07aRadialSymbol_neg, n07aAngularFourier_neg, map_mul]
  intro j
  exact congrArg (fun c : SpacesTorusCoefficients => c j)
    (n07aAngularFourier_inverse m hm v hv)

end ContinuousFlexibility.Analysis
