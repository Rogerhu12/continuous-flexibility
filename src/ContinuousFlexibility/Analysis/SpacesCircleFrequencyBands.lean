module

public import ContinuousFlexibility.Analysis.SpacesCircleSpectral
public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets

/-!
# Joint discrete-weight and angular-frequency bands

A band is defined by `max M (2 |n|)`. Its angular index set is finite, even
when infinitely many circle rows share the same discrete weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open Analysis

/-- Joint spectral size for one circle row. -/
def circleFrequencySize (M : ℝ) (n : ℤ) : ℝ := max M (2 * |(n : ℝ)|)

theorem circleFrequencySize_one_le {M : ℝ} (hM : 1 ≤ M) (n : ℤ) :
    1 ≤ circleFrequencySize M n := hM.trans (le_max_left _ _)

/-- A finite presentation of the full logarithmic frequency band. -/
def circleFrequencyBand (M : ℝ) (k : ℕ) : Finset ℤ :=
  (Finset.Icc (-⌈Real.exp ((k : ℝ) + 1)⌉) ⌈Real.exp ((k : ℝ) + 1)⌉).filter
    (fun n => spectralLogBand (circleFrequencySize M) n = k)

theorem circleFrequencyBand_mem {M : ℝ} (hM : 1 ≤ M) (k : ℕ) (n : ℤ) :
    n ∈ circleFrequencyBand M k ↔ spectralLogBand (circleFrequencySize M) n = k := by
  simp only [circleFrequencyBand, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact And.right
  · intro hn
    refine ⟨?_, hn⟩
    have hupper := spectralLogBand_upper (circleFrequencySize M)
      (circleFrequencySize_one_le hM) n
    rw [hn] at hupper
    have hfreq : |(n : ℝ)| ≤ circleFrequencySize M n := by
      have hpos := abs_nonneg (n : ℝ)
      exact (by linarith : |(n : ℝ)| ≤ 2 * |(n : ℝ)|).trans (le_max_right _ _)
    have hbound : |(n : ℝ)| ≤ (⌈Real.exp ((k : ℝ) + 1)⌉ : ℤ) :=
      hfreq.trans (hupper.le.trans (Int.le_ceil _))
    have hboundInt : |n| ≤ ⌈Real.exp ((k : ℝ) + 1)⌉ := by exact_mod_cast hbound
    exact abs_le.mp hboundInt

theorem circleFrequencyBand_neg {M : ℝ} (hM : 1 ≤ M) (k : ℕ) (n : ℤ) :
    -n ∈ circleFrequencyBand M k ↔ n ∈ circleFrequencyBand M k := by
  rw [circleFrequencyBand_mem hM, circleFrequencyBand_mem hM]
  simp only [spectralLogBand, circleFrequencySize, Int.cast_neg, abs_neg]

theorem circleFrequencyBand_upper {M : ℝ} (hM : 1 ≤ M) {k : ℕ} {n : ℤ}
    (hn : n ∈ circleFrequencyBand M k) :
    M < Real.exp ((k : ℝ) + 1) ∧ 2 * |(n : ℝ)| < Real.exp ((k : ℝ) + 1) := by
  have hupper := spectralLogBand_upper (circleFrequencySize M)
    (circleFrequencySize_one_le hM) n
  rw [(circleFrequencyBand_mem hM k n).mp hn] at hupper
  exact ⟨(le_max_left _ _).trans_lt hupper, (le_max_right _ _).trans_lt hupper⟩

/-- The two pure top-order jets control the analysis of each joint band. -/
theorem circleFrequencyBand_analysis_bound {M : ℝ} (hM : 1 ≤ M)
    {k : ℕ} {n : ℤ} (hn : n ∈ circleFrequencyBand M k) (s : ℕ) :
    Real.exp ((s : ℝ) * (k : ℝ)) ≤ M ^ s + (2 * |(n : ℝ)|) ^ s := by
  have h := spectralLogBand_exp_mul_le_pow (circleFrequencySize M)
    (circleFrequencySize_one_le hM) s n
  rw [(circleFrequencyBand_mem hM k n).mp hn] at h
  by_cases hMfreq : M ≤ 2 * |(n : ℝ)|
  · rw [circleFrequencySize, max_eq_right hMfreq] at h
    exact h.trans (le_add_of_nonneg_left (pow_nonneg (zero_le_one.trans hM) s))
  · rw [circleFrequencySize, max_eq_left (le_of_not_ge hMfreq)] at h
    exact h.trans (le_add_of_nonneg_right (pow_nonneg (by positivity) s))

/-- Every mixed discrete/angular jet of total order at most `s` has one
uniform exponential growth bound on the band. -/
theorem circleFrequencyBand_synthesis_bound {M : ℝ} (hM : 1 ≤ M)
    {k : ℕ} {n : ℤ} (hn : n ∈ circleFrequencyBand M k) (b c s : ℕ) (hbc : b + c ≤ s) :
    M ^ c * (2 * |(n : ℝ)|) ^ b ≤
      Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hfreq0 : 0 ≤ 2 * |(n : ℝ)| := by positivity
  calc
    M ^ c * (2 * |(n : ℝ)|) ^ b ≤
        circleFrequencySize M n ^ c * circleFrequencySize M n ^ b :=
      mul_le_mul (pow_le_pow_left₀ hM0 (le_max_left _ _) c)
        (pow_le_pow_left₀ hfreq0 (le_max_right _ _) b)
        (pow_nonneg hfreq0 b) (pow_nonneg (hM0.trans (le_max_left _ _)) c)
    _ = circleFrequencySize M n ^ (b + c) := by rw [← pow_add, Nat.add_comm]
    _ ≤ circleFrequencySize M n ^ s := pow_le_pow_right₀ (circleFrequencySize_one_le hM n) hbc
    _ ≤ Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) := by
      simpa only [(circleFrequencyBand_mem hM k n).mp hn] using
        spectralLogBand_pow_le (circleFrequencySize M) (circleFrequencySize_one_le hM) s n

end ContinuousFlexibility.Statements
