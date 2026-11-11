import ContinuousFlexibility.Analysis.N07aAngularWeights

/-!
# Splitting the actual output jet weight across angular blocks

The two summands put the extra derivatives either on the input or on the
frequency difference.  Consequently a high input norm only requires a
fixed low coefficient order; the other summand has one high coefficient
norm and the original input norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

def n07aAngularGap (j l : ℕ) : ℝ := 1 + |(j : ℝ) - l|

theorem n07aAngularGap_one_le (j l : ℕ) : 1 ≤ n07aAngularGap j l :=
  le_add_of_nonneg_right (abs_nonneg _)

theorem n07aAngularGap_eq_int (j l : ℕ) :
    n07aAngularGap j l = 1 + |(((j : ℤ) - l : ℤ) : ℝ)| := by
  simp only [n07aAngularGap, Int.cast_sub, Int.cast_natCast]

theorem n07aAngularWeight_le_add_gap (j l : ℕ) :
    angularWeight l ≤ angularWeight j + n07aAngularGap j l := by
  have h := neg_le_abs ((j : ℝ) - l)
  have hj := natCast_le_angularWeight j
  have hl := angularWeight_le_one_add l
  dsimp only [n07aAngularGap]
  linarith

theorem n07aAngularWeight_le_mul_gap (j l : ℕ) :
    angularWeight l ≤ 2 * angularWeight j * n07aAngularGap j l := by
  have hj := one_le_angularWeight j
  have hg := n07aAngularGap_one_le j l
  have h₁ : angularWeight j ≤ angularWeight j * n07aAngularGap j l := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hg (angularWeight_nonneg j)
  have h₂ : n07aAngularGap j l ≤ angularWeight j * n07aAngularGap j l := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (zero_le_one.trans hg)
  exact (n07aAngularWeight_le_add_gap j l).trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem n07aAngularWeight_pow_split (p j l : ℕ) :
    angularWeight l ^ p ≤ 2 ^ p *
      (angularWeight j ^ p + n07aAngularGap j l ^ p) := by
  have hg : 0 ≤ n07aAngularGap j l := (zero_le_one.trans (n07aAngularGap_one_le j l))
  calc
    _ ≤ (angularWeight j + n07aAngularGap j l) ^ p :=
      pow_le_pow_left₀ (angularWeight_nonneg l) (n07aAngularWeight_le_add_gap j l) p
    _ ≤ 2 ^ (p - 1) * (angularWeight j ^ p + n07aAngularGap j l ^ p) :=
      add_pow_le (angularWeight_nonneg j) hg p
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le p 1))
      (add_nonneg (pow_nonneg (angularWeight_nonneg j) p) (pow_nonneg hg p))

theorem n07aAngularJetWeight_root_lower (s n : ℕ) :
    angularWeight n ^ s ≤ Real.sqrt (n07aAngularJetWeightSq s n) := by
  have h := n07aAngularJetWeightSq_lower_spectral 0 s n
  simp only [Nat.zero_add, n07aAngularJetWeightSq_zero_order, mul_one] at h
  apply (sq_le_sq₀ (pow_nonneg (angularWeight_nonneg n) s) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (n07aAngularJetWeightSq_nonneg s n), ← pow_mul, Nat.mul_comm s 2]
  exact h

theorem n07aAngularJetWeight_root_upper (s n : ℕ) :
    Real.sqrt (n07aAngularJetWeightSq s n) ≤
      Real.sqrt (2 * 4 ^ s) * angularWeight n ^ s := by
  have h := n07aAngularJetWeightSq_upper_spectral 0 s n
  simp only [Nat.zero_add, n07aAngularJetWeightSq_zero_order, mul_one] at h
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (angularWeight_nonneg n) s), ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm s 2]
  exact h

def n07aAngularBlockWeightConstant (b p : ℕ) : ℝ :=
  Real.sqrt (2 * 4 ^ (b + p)) * 2 ^ b * 2 ^ p

theorem n07aAngularBlockWeightConstant_nonneg (b p : ℕ) :
    0 ≤ n07aAngularBlockWeightConstant b p := by
  unfold n07aAngularBlockWeightConstant
  positivity

theorem n07aAngularJetWeight_root_block_split (b p j l : ℕ) :
    Real.sqrt (n07aAngularJetWeightSq (b + p) l) ≤
      n07aAngularBlockWeightConstant b p *
        (Real.sqrt (n07aAngularJetWeightSq (b + p) j) * n07aAngularGap j l ^ b +
          Real.sqrt (n07aAngularJetWeightSq b j) * n07aAngularGap j l ^ (b + p)) := by
  have hg : 0 ≤ n07aAngularGap j l := zero_le_one.trans (n07aAngularGap_one_le j l)
  have hb : angularWeight l ^ b ≤ 2 ^ b * angularWeight j ^ b * n07aAngularGap j l ^ b := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (angularWeight_nonneg l) (n07aAngularWeight_le_mul_gap j l) b
  have hp := n07aAngularWeight_pow_split p j l
  calc
    _ ≤ Real.sqrt (2 * 4 ^ (b + p)) * angularWeight l ^ (b + p) :=
      n07aAngularJetWeight_root_upper (b + p) l
    _ = Real.sqrt (2 * 4 ^ (b + p)) * (angularWeight l ^ b * angularWeight l ^ p) := by
      rw [pow_add (angularWeight l) b p]
    _ ≤ Real.sqrt (2 * 4 ^ (b + p)) *
        ((2 ^ b * angularWeight j ^ b * n07aAngularGap j l ^ b) *
          (2 ^ p * (angularWeight j ^ p + n07aAngularGap j l ^ p))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hb hp
        (pow_nonneg (angularWeight_nonneg l) p)
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) b)
          (pow_nonneg (angularWeight_nonneg j) b)) (pow_nonneg hg b)))
        (Real.sqrt_nonneg _)
    _ = n07aAngularBlockWeightConstant b p *
        (angularWeight j ^ (b + p) * n07aAngularGap j l ^ b +
          angularWeight j ^ b * n07aAngularGap j l ^ (b + p)) := by
      simp only [n07aAngularBlockWeightConstant, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right (n07aAngularJetWeight_root_lower (b + p) j) (pow_nonneg hg b))
      (mul_le_mul_of_nonneg_right (n07aAngularJetWeight_root_lower b j) (pow_nonneg hg (b + p))))
      (n07aAngularBlockWeightConstant_nonneg b p)

theorem n07aAngularBlock_weighted_split
    (b p j l : ℕ) {v X A C a : ℝ} (hv : 0 ≤ v) (hX : 0 ≤ X)
    (hbase : Real.sqrt (n07aAngularJetWeightSq b j) *
      (v * n07aAngularGap j l ^ b * X) ≤ A * a)
    (hhigh : Real.sqrt (n07aAngularJetWeightSq b j) *
      (v * n07aAngularGap j l ^ (b + p) * X) ≤ C * a) :
    v * Real.sqrt (n07aAngularJetWeightSq (b + p) l) * X ≤
      n07aAngularBlockWeightConstant b p *
        (A * (Real.sqrt (n07aAngularJetWeightSq (b + p) j) /
          Real.sqrt (n07aAngularJetWeightSq b j)) + C) * a := by
  let J : ℝ := Real.sqrt (n07aAngularJetWeightSq b j)
  let H : ℝ := Real.sqrt (n07aAngularJetWeightSq (b + p) j)
  have hJ : 0 < J := Real.sqrt_pos.2 (zero_lt_one.trans_le (n07aAngularJetWeightSq_one_le b j))
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hratio : 0 ≤ H / J := div_nonneg hH hJ.le
  calc
    _ ≤ v * (n07aAngularBlockWeightConstant b p *
        (H * n07aAngularGap j l ^ b + J * n07aAngularGap j l ^ (b + p))) * X :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (n07aAngularJetWeight_root_block_split b p j l) hv) hX
    _ = n07aAngularBlockWeightConstant b p *
        ((H / J) * (J * (v * n07aAngularGap j l ^ b * X)) +
          J * (v * n07aAngularGap j l ^ (b + p) * X)) := by
      field_simp
    _ ≤ n07aAngularBlockWeightConstant b p * ((H / J) * (A * a) + C * a) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hbase hratio) hhigh)
        (n07aAngularBlockWeightConstant_nonneg b p)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
