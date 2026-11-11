import ContinuousFlexibility.Analysis.SpacesTorusReal
import ContinuousFlexibility.Analysis.SpacesTorusWaves
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Joint material, radial and angular frequency bands

The spectral size records the actual physical differentiation symbols.
Every band is finite in the two Fourier indices. All three pure top jets
control its analysis, while every mixed jet has the same total-order
exponential growth bound for synthesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance spacesPhysicalFrequencyBandsDecidableFrequency : DecidableEq SpacesTorusFrequency := Classical.decEq _

def spacesPhysicalFrequencySize (M : ℝ) (j : SpacesTorusFrequency) : ℝ :=
  max M (max (Real.pi / 3 * |(j 0 : ℝ)|) (2 * |(j 1 : ℝ)|))

theorem spacesPhysicalFrequencySize_one_le {M : ℝ} (hM : 1 ≤ M) (j : SpacesTorusFrequency) :
    1 ≤ spacesPhysicalFrequencySize M j := hM.trans (le_max_left _ _)

theorem spacesPhysicalFrequencySize_weight_le (M : ℝ) (j : SpacesTorusFrequency) :
    M ≤ spacesPhysicalFrequencySize M j := le_max_left _ _

theorem spacesPhysicalFrequencySize_radial_le (M : ℝ) (j : SpacesTorusFrequency) :
    Real.pi / 3 * |(j 0 : ℝ)| ≤ spacesPhysicalFrequencySize M j :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem spacesPhysicalFrequencySize_angular_le (M : ℝ) (j : SpacesTorusFrequency) :
    2 * |(j 1 : ℝ)| ≤ spacesPhysicalFrequencySize M j :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem spacesPhysicalFrequencySize_frequency_le (M : ℝ) (j : SpacesTorusFrequency) (i : Fin 2) :
    |(j i : ℝ)| ≤ spacesPhysicalFrequencySize M j := by
  fin_cases i
  · have h := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi / 3)
      (abs_nonneg (j 0 : ℝ))
    have h' : |(j 0 : ℝ)| ≤ Real.pi / 3 * |(j 0 : ℝ)| := by simpa only [one_mul] using h
    exact h'.trans (spacesPhysicalFrequencySize_radial_le M j)
  · exact (by linarith [abs_nonneg (j 1 : ℝ)] : |(j 1 : ℝ)| ≤ 2 * |(j 1 : ℝ)|).trans
      (spacesPhysicalFrequencySize_angular_le M j)

theorem spacesPhysicalFrequencySize_neg (M : ℝ) (j : SpacesTorusFrequency) :
    spacesPhysicalFrequencySize M (-j) = spacesPhysicalFrequencySize M j := by
  simp only [spacesPhysicalFrequencySize, Pi.neg_apply, Int.cast_neg, abs_neg]

/-- The finite set representing the entire logarithmic band in one cell. -/
def spacesPhysicalFrequencyBand (M : ℝ) (k : ℕ) : Finset SpacesTorusFrequency :=
  (spacesTorusFrequencyBox ⌈Real.exp ((k : ℝ) + 1)⌉₊).filter
    (fun j => spectralLogBand (spacesPhysicalFrequencySize M) j = k)

theorem spacesPhysicalFrequencyBand_mem {M : ℝ} (hM : 1 ≤ M) (k : ℕ)
    (j : SpacesTorusFrequency) :
    j ∈ spacesPhysicalFrequencyBand M k ↔ spectralLogBand (spacesPhysicalFrequencySize M) j = k := by
  simp only [spacesPhysicalFrequencyBand, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hj
    exact ⟨spacesTorusLogBand_frequencyBox (spacesPhysicalFrequencySize M)
      (spacesPhysicalFrequencySize_one_le hM) (spacesPhysicalFrequencySize_frequency_le M) k j hj, hj⟩

theorem spacesPhysicalFrequencyBand_neg {M : ℝ} (hM : 1 ≤ M) (k : ℕ)
    (j : SpacesTorusFrequency) :
    -j ∈ spacesPhysicalFrequencyBand M k ↔ j ∈ spacesPhysicalFrequencyBand M k := by
  rw [spacesPhysicalFrequencyBand_mem hM, spacesPhysicalFrequencyBand_mem hM]
  simp only [spectralLogBand, spacesPhysicalFrequencySize_neg]

theorem spacesPhysicalFrequencyBand_analysis_bound {M : ℝ} (hM : 1 ≤ M)
    {k : ℕ} {j : SpacesTorusFrequency} (hj : j ∈ spacesPhysicalFrequencyBand M k) (s : ℕ) :
    Real.exp ((s : ℝ) * (k : ℝ)) ≤
      M ^ s + (Real.pi / 3 * |(j 0 : ℝ)|) ^ s + (2 * |(j 1 : ℝ)|) ^ s := by
  have h := spectralLogBand_exp_mul_le_pow (spacesPhysicalFrequencySize M)
    (spacesPhysicalFrequencySize_one_le hM) s j
  rw [(spacesPhysicalFrequencyBand_mem hM k j).mp hj] at h
  have hm : 0 ≤ M ^ s := pow_nonneg (zero_le_one.trans hM) s
  have hr : 0 ≤ (Real.pi / 3 * |(j 0 : ℝ)|) ^ s := by positivity
  have ht : 0 ≤ (2 * |(j 1 : ℝ)|) ^ s := by positivity
  by_cases hmr : M ≤ max (Real.pi / 3 * |(j 0 : ℝ)|) (2 * |(j 1 : ℝ)|)
  · rw [spacesPhysicalFrequencySize, max_eq_right hmr] at h
    by_cases hrt : Real.pi / 3 * |(j 0 : ℝ)| ≤ 2 * |(j 1 : ℝ)|
    · rw [max_eq_right hrt] at h
      linarith
    · rw [max_eq_left (le_of_not_ge hrt)] at h
      linarith
  · rw [spacesPhysicalFrequencySize, max_eq_left (le_of_not_ge hmr)] at h
    linarith

theorem spacesPhysicalFrequencyBand_synthesis_bound {M : ℝ} (hM : 1 ≤ M)
    {k : ℕ} {j : SpacesTorusFrequency} (hj : j ∈ spacesPhysicalFrequencyBand M k)
    (a b c s : ℕ) (hord : a + b + c ≤ s) :
    M ^ c * (Real.pi / 3 * |(j 0 : ℝ)|) ^ a * (2 * |(j 1 : ℝ)|) ^ b ≤
      Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) := by
  let w := spacesPhysicalFrequencySize M j
  have hw : 1 ≤ w := spacesPhysicalFrequencySize_one_le hM j
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hr0 : 0 ≤ Real.pi / 3 * |(j 0 : ℝ)| := by positivity
  have ht0 : 0 ≤ 2 * |(j 1 : ℝ)| := by positivity
  calc
    M ^ c * (Real.pi / 3 * |(j 0 : ℝ)|) ^ a * (2 * |(j 1 : ℝ)|) ^ b ≤
        w ^ c * w ^ a * w ^ b := by
      apply mul_le_mul
        (mul_le_mul (pow_le_pow_left₀ hM0 (spacesPhysicalFrequencySize_weight_le M j) c)
          (pow_le_pow_left₀ hr0 (spacesPhysicalFrequencySize_radial_le M j) a)
          (pow_nonneg hr0 a) (pow_nonneg (zero_le_one.trans hw) c))
        (pow_le_pow_left₀ ht0 (spacesPhysicalFrequencySize_angular_le M j) b)
        (pow_nonneg ht0 b) (mul_nonneg (pow_nonneg (zero_le_one.trans hw) c)
          (pow_nonneg (zero_le_one.trans hw) a))
    _ = w ^ (a + b + c) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ w ^ s := pow_le_pow_right₀ hw hord
    _ ≤ Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) := by
      simpa only [(spacesPhysicalFrequencyBand_mem hM k j).mp hj] using
        spectralLogBand_pow_le (spacesPhysicalFrequencySize M) (spacesPhysicalFrequencySize_one_le hM) s j

end ContinuousFlexibility.Statements
