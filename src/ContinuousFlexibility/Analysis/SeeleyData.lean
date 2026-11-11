import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coefficient data for a single extension operator at every derivative order

The signed moment identities match all derivatives across an endpoint. Absolute
summability at every order permits the same reflection series to be used at all
Sobolev levels. `SeeleyCoefficients` constructs these data without assuming an
extension theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Reflection coefficients with all signed moments equal to one. The index
type is left arbitrary so finite correction blocks need not be flattened. -/
structure SeeleyData (ι : Type*) where
  a : ι → ℝ
  b : ι → ℝ
  one_le_b : ∀ i, 1 ≤ b i
  summable_moment : ∀ m : ℕ, Summable (fun i => |a i| * b i ^ m)
  hasSum_moment : ∀ m : ℕ, HasSum (fun i => a i * (-b i) ^ m) 1

namespace SeeleyData

variable {ι : Type*} (S : SeeleyData ι)

theorem b_pos (i : ι) : 0 < S.b i := lt_of_lt_of_le zero_lt_one (S.one_le_b i)

theorem b_nonneg (i : ι) : 0 ≤ S.b i := (S.b_pos i).le

theorem norm_signed_moment (i : ι) (m : ℕ) :
    ‖S.a i * (-S.b i) ^ m‖ = |S.a i| * S.b i ^ m := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (S.b_nonneg i)]

theorem summable_signed_moment (m : ℕ) :
    Summable (fun i => S.a i * (-S.b i) ^ m) :=
  (S.hasSum_moment m).summable

theorem tsum_moment (m : ℕ) : (∑' i, S.a i * (-S.b i) ^ m) = 1 :=
  (S.hasSum_moment m).tsum_eq

theorem summable_abs : Summable (fun i => |S.a i|) := by
  simpa only [pow_zero, mul_one] using S.summable_moment 0

theorem hasSum_a : HasSum S.a 1 := by
  simpa only [pow_zero, mul_one] using S.hasSum_moment 0

theorem summable_a : Summable S.a := S.hasSum_a.summable

theorem tsum_a : (∑' i, S.a i) = 1 := S.hasSum_a.tsum_eq

end SeeleyData

end ContinuousFlexibility.Analysis
