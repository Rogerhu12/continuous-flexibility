import ContinuousFlexibility.Analysis.SeeleyFiniteBlocks
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Reflection coefficients with every moment prescribed

At stage `n` a finite block corrects the `n`th signed moment and changes none of
the preceding moments. Its lower absolute moments are at most `2⁻ⁿ`. For any
fixed derivative order only finitely many blocks precede this bound, so the
resulting single coefficient family is absolutely summable at every order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter Finset
open scoped Topology

private def seeleyCorrection (n : ℕ) (r ε : ℝ) (hε : 0 < ε) : SeeleyBlock n :=
  (exists_seeleyBlock n r ε hε).choose

private theorem seeleyCorrection_spec (n : ℕ) (r ε : ℝ) (hε : 0 < ε) :
    (∀ m < n, (seeleyCorrection n r ε hε).moment m = 0) ∧
      (seeleyCorrection n r ε hε).moment n = r ∧
      ∀ m < n, (seeleyCorrection n r ε hε).absMoment m ≤ ε :=
  (exists_seeleyBlock n r ε hε).choose_spec

private def seeleyBlocks : (n : ℕ) → SeeleyBlock n :=
  Nat.strongRec fun n previous =>
    seeleyCorrection n
      (1 - ∑ k : Fin n, (previous k k.isLt).moment n)
      ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n)

private theorem seeleyBlocks_eq (n : ℕ) :
    seeleyBlocks n = seeleyCorrection n
      (1 - ∑ k : Fin n, (seeleyBlocks k).moment n)
      ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n) := by
  unfold seeleyBlocks
  rw [Nat.strongRec_eq]

private theorem seeleyBlocks_moment_lt (n m : ℕ) (hmn : m < n) :
    (seeleyBlocks n).moment m = 0 := by
  rw [seeleyBlocks_eq]
  exact (seeleyCorrection_spec _ _ _ _).1 m hmn

private theorem seeleyBlocks_moment_self (n : ℕ) :
    (seeleyBlocks n).moment n =
      1 - ∑ k : Fin n, (seeleyBlocks k).moment n := by
  rw [seeleyBlocks_eq]
  exact (seeleyCorrection_spec _ _ _ _).2.1

private theorem seeleyBlocks_absMoment_le (n m : ℕ) (hmn : m < n) :
    (seeleyBlocks n).absMoment m ≤ (1 / 2 : ℝ) ^ n := by
  rw [seeleyBlocks_eq]
  exact (seeleyCorrection_spec _ _ _ _).2.2 m hmn

private theorem seeleyBlocks_summable_absMoment (m : ℕ) :
    Summable (fun n => (seeleyBlocks n).absMoment m) := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [eventually_gt_atTop m] with n hmn
  rw [Real.norm_eq_abs, abs_of_nonneg ((seeleyBlocks n).absMoment_nonneg m)]
  exact seeleyBlocks_absMoment_le n m hmn

private theorem seeleyBlocks_hasSum_moment (m : ℕ) :
    HasSum (fun n => (seeleyBlocks n).moment m) 1 := by
  have hfinite : (∑ n ∈ range (m + 1), (seeleyBlocks n).moment m) = 1 := by
    rw [Finset.sum_range_succ, seeleyBlocks_moment_self,
      Fin.sum_univ_eq_sum_range (fun k : ℕ => (seeleyBlocks k).moment m) m]
    ring
  have hzero : ∀ n ∉ range (m + 1), (seeleyBlocks n).moment m = 0 := by
    intro n hn
    have hmn : m < n := lt_of_lt_of_le (Nat.lt_succ_self m)
      (Nat.le_of_not_gt (fun hn' => hn (mem_range.mpr hn')))
    exact seeleyBlocks_moment_lt n m hmn
  simpa only [hfinite] using hasSum_sum_of_ne_finset_zero hzero

/-- The countable disjoint union of the finite moment-correction blocks. -/
abbrev SeeleyIndex : Type := Σ n : ℕ, Fin (n + 1)

/-- A single family of coefficients, independent of derivative order. -/
def seeleyCoefficient (i : SeeleyIndex) : ℝ := (seeleyBlocks i.1).a i.2

/-- The dilation associated to a coefficient. -/
def seeleyDilation (i : SeeleyIndex) : ℝ := (seeleyBlocks i.1).b i.2

theorem seeleyDilation_one_le (i : SeeleyIndex) : 1 ≤ seeleyDilation i :=
  (seeleyBlocks i.1).one_le_b i.2

theorem seeleyCoefficient_summable_moment (m : ℕ) :
    Summable (fun i : SeeleyIndex => |seeleyCoefficient i| * seeleyDilation i ^ m) := by
  have hnonneg (i : SeeleyIndex) : 0 ≤ |seeleyCoefficient i| * seeleyDilation i ^ m :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans (seeleyDilation_one_le i)) m)
  apply (summable_sigma_of_nonneg hnonneg).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, seeleyCoefficient, seeleyDilation, SeeleyBlock.absMoment]
    using seeleyBlocks_summable_absMoment m

theorem seeleyCoefficient_norm_moment (i : SeeleyIndex) (m : ℕ) :
    ‖seeleyCoefficient i * (-seeleyDilation i) ^ m‖ =
      |seeleyCoefficient i| * seeleyDilation i ^ m := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (zero_le_one.trans (seeleyDilation_one_le i))]

theorem seeleyCoefficient_hasSum_moment (m : ℕ) :
    HasSum (fun i : SeeleyIndex => seeleyCoefficient i * (-seeleyDilation i) ^ m) 1 := by
  have hsum : Summable
      (fun i : SeeleyIndex => seeleyCoefficient i * (-seeleyDilation i) ^ m) :=
    (seeleyCoefficient_summable_moment m).of_norm_bounded
      (fun i => (seeleyCoefficient_norm_moment i m).le)
  refine HasSum.sigma_of_hasSum (seeleyBlocks_hasSum_moment m) ?_ hsum
  intro n
  simpa only [seeleyCoefficient, seeleyDilation, SeeleyBlock.moment]
    using hasSum_fintype
      (fun i : Fin (n + 1) => (seeleyBlocks n).a i * (-(seeleyBlocks n).b i) ^ m)

/-- Unconditional coefficient data for the same reflection operator at every
nonnegative integer Sobolev order. -/
def seeleyData : SeeleyData SeeleyIndex where
  a := seeleyCoefficient
  b := seeleyDilation
  one_le_b := seeleyDilation_one_le
  summable_moment := seeleyCoefficient_summable_moment
  hasSum_moment := seeleyCoefficient_hasSum_moment

end ContinuousFlexibility.Analysis
