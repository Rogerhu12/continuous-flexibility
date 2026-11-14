module

public import ContinuousFlexibility.Analysis.N06AiryAverage
public import ContinuousFlexibility.Analysis.N06FractionalJetBounds

/-!
# The controlled two-sided reference Airy coordinate and height

The coordinate is the explicit integral germ on both sides. Its derivative
is identified from the actual integral identity, so positivity and all
finite slope bounds concern the true coordinate. The height is the original
square-root normalization using this same derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n06AiryRadialCoordinate (c : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * n06AiryAverage c x ^ (2 / 3 : ℝ)

def n06AiryRadialSlope (c : ℝ → ℝ) (x : ℝ) : ℝ :=
  c x * n06AiryAverage c x ^ (-1 / 3 : ℝ)

def n06AiryRadialHeight (c W : ℝ → ℝ) (x : ℝ) : ℝ :=
  (W x * n06AiryRadialSlope c x) ^ (-1 / 2 : ℝ)

@[simp] theorem n06_airyRadialCoordinate_zero (c : ℝ → ℝ) :
    n06AiryRadialCoordinate c 0 = 0 := zero_mul _

theorem n06_contDiff_airyRadialCoordinate {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hp : ∀ x : ℝ, 0 < n06AiryAverage c x) :
    ContDiff ℝ ∞ (n06AiryRadialCoordinate c) := by
  have hpow : ContDiff ℝ ∞ (fun x => n06AiryAverage c x ^ (2 / 3 : ℝ)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (Real.contDiffAt_rpow_const_of_ne (hp x).ne').comp x
      (n06_contDiff_airyAverage hc).contDiffAt
  exact contDiff_id.mul hpow

theorem n06_contDiff_airyRadialSlope {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hp : ∀ x : ℝ, 0 < n06AiryAverage c x) :
    ContDiff ℝ ∞ (n06AiryRadialSlope c) := by
  have hpow : ContDiff ℝ ∞ (fun x => n06AiryAverage c x ^ (-1 / 3 : ℝ)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (Real.contDiffAt_rpow_const_of_ne (hp x).ne').comp x
      (n06_contDiff_airyAverage hc).contDiffAt
  exact hc.mul hpow

/-- The displayed positive slope is the actual ordinary derivative of
the new reference coordinate, on either side of zero. -/
theorem n06_hasDerivAt_airyRadialCoordinate {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (x : ℝ) (hp : 0 < n06AiryAverage c x) :
    HasDerivAt (n06AiryRadialCoordinate c) (n06AiryRadialSlope c x) x := by
  have hpder := ((n06_contDiff_airyAverage hc).differentiable (by simp) x).hasDerivAt
  have hpow := hpder.rpow_const (p := (2 / 3 : ℝ)) (Or.inl hp.ne')
  have hd : HasDerivAt (n06AiryRadialCoordinate c)
      (n06AiryAverage c x ^ (2 / 3 : ℝ) +
        x * (deriv (n06AiryAverage c) x * (2 / 3 : ℝ) *
          n06AiryAverage c x ^ ((2 / 3 : ℝ) - 1))) x := by
    have hfun : (id * fun y : ℝ => n06AiryAverage c y ^ (2 / 3 : ℝ)) =
        n06AiryRadialCoordinate c := rfl
    have hd' := (hasDerivAt_id x).mul hpow
    rw [hfun] at hd'
    simpa only [id_eq, one_mul] using hd'
  apply hd.congr_deriv
  have hfac : n06AiryAverage c x ^ (2 / 3 : ℝ) =
      n06AiryAverage c x * n06AiryAverage c x ^ (-1 / 3 : ℝ) := by
    rw [show (2 / 3 : ℝ) = 1 + (-1 / 3 : ℝ) by norm_num,
      Real.rpow_add hp, Real.rpow_one]
  rw [hfac, show (2 / 3 : ℝ) - 1 = -1 / 3 by norm_num]
  calc
    _ = (n06AiryAverage c x + (2 / 3 : ℝ) * x * deriv (n06AiryAverage c) x) *
        n06AiryAverage c x ^ (-1 / 3 : ℝ) := by ring
    _ = n06AiryRadialSlope c x := by rw [n06_airyAverage_euler hc]; rfl

theorem n06_deriv_airyRadialCoordinate {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x) :
    deriv (n06AiryRadialCoordinate c) = n06AiryRadialSlope c :=
  funext fun x => (n06_hasDerivAt_airyRadialCoordinate hc x (hp x)).deriv

/-- Uniform input speed bounds give global positive slope bounds through
two ordinary derivatives, with no third input derivative. -/
theorem n06_airyRadialSlope_bounds {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    {B : ℝ} (hB : 1 ≤ B) (hjet : ∀ x, N06ScalarJetTwoBound c x B)
    (hpos : ∀ x, 0 < c x) (hinv : ∀ x, (c x)⁻¹ ≤ B) :
    ContDiff ℝ ∞ (n06AiryRadialCoordinate c) ∧
      ContDiff ℝ ∞ (n06AiryRadialSlope c) ∧
      deriv (n06AiryRadialCoordinate c) = n06AiryRadialSlope c ∧
      ∀ x : ℝ, 0 < n06AiryRadialSlope c x ∧
        N06ScalarJetTwoBound (n06AiryRadialSlope c) x (384 * B ^ 6) ∧
        (n06AiryRadialSlope c x)⁻¹ ≤ 2 * B ^ 2 := by
  have hmean (x : ℝ) := n06_airyAverage_twoJet_bound hc hB hjet hpos hinv x
  have hp : ∀ x, 0 < n06AiryAverage c x := fun x => (hmean x).1
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have h2B : 1 ≤ 2 * B := by linarith
  have hB2B : B ≤ 2 * B := by linarith
  refine ⟨n06_contDiff_airyRadialCoordinate hc hp,
    n06_contDiff_airyRadialSlope hc hp, n06_deriv_airyRadialCoordinate hc hp, ?_⟩
  intro x
  have hpowSm : ContDiffAt ℝ ∞ (fun t => n06AiryAverage c t ^ (-1 / 3 : ℝ)) x :=
    (Real.contDiffAt_rpow_const_of_ne (hp x).ne').comp x
      (n06_contDiff_airyAverage hc).contDiffAt
  obtain ⟨hpow, hpowInv⟩ := (hmean x).2.1.rpow_unit_at
    (n06_contDiff_airyAverage hc).contDiffAt (hp x) h2B
    ((hmean x).2.2.trans hB2B) (by norm_num : |(-1 / 3 : ℝ)| ≤ 1)
  have hprod := (hjet x).mul_at hc.contDiffAt hpowSm hB0 (by positivity) hpow
  have hbound : N06ScalarJetTwoBound (n06AiryRadialSlope c) x (384 * B ^ 6) := by
    convert hprod using 1
    · rfl
    · ring
  have hsp : 0 < n06AiryRadialSlope c x :=
    mul_pos (hpos x) (Real.rpow_pos_of_pos (hp x) _)
  refine ⟨hsp, hbound, ?_⟩
  rw [n06AiryRadialSlope, mul_inv_rev]
  calc
    _ ≤ (2 * B) * B := mul_le_mul hpowInv (hinv x)
      (inv_nonneg.mpr (hpos x).le) (by positivity)
    _ = 2 * B ^ 2 := by ring

/-- The actual coordinate itself has controlled ordinary two-jets on
the unit collar; its first derivative has the stronger global bound above. -/
theorem n06_airyRadialCoordinate_twoJet_bound {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) {B : ℝ} (hB : 1 ≤ B)
    (hjet : ∀ x, N06ScalarJetTwoBound c x B)
    (hpos : ∀ x, 0 < c x) (hinv : ∀ x, (c x)⁻¹ ≤ B)
    {x : ℝ} (hx : |x| ≤ 1) :
    N06ScalarJetTwoBound (n06AiryRadialCoordinate c) x (384 * B ^ 5) := by
  have hmean := n06_airyAverage_twoJet_bound hc hB hjet hpos hinv x
  have h2B : 1 ≤ 2 * B := by linarith
  have hB2B : B ≤ 2 * B := by linarith
  have hpowSm : ContDiffAt ℝ ∞ (fun t => n06AiryAverage c t ^ (2 / 3 : ℝ)) x :=
    (Real.contDiffAt_rpow_const_of_ne hmean.1.ne').comp x
      (n06_contDiff_airyAverage hc).contDiffAt
  have hpow := (hmean.2.1.rpow_unit_at (n06_contDiff_airyAverage hc).contDiffAt
    hmean.1 h2B (hmean.2.2.trans hB2B) (by norm_num : |(2 / 3 : ℝ)| ≤ 1)).1
  have hid : N06ScalarJetTwoBound (fun t : ℝ => t) x 1 := by
    exact ⟨hx, by simp, by simp⟩
  have hprod := hid.mul_at contDiffAt_id hpowSm (by norm_num) (by positivity) hpow
  convert hprod using 1
  · rfl
  · ring

/-- This height is exactly the physical square-root normalization of
the same coordinate derivative. -/
theorem n06_airyRadialHeight_eq_actual {c W : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hp : ∀ x : ℝ, 0 < n06AiryAverage c x)
    (x : ℝ) (hW : 0 < W x) (hs : 0 < n06AiryRadialSlope c x) :
    n06AiryRadialHeight c W x =
      (Real.sqrt (W x * deriv (n06AiryRadialCoordinate c) x))⁻¹ := by
  rw [n06_deriv_airyRadialCoordinate hc hp]
  change (W x * n06AiryRadialSlope c x) ^ (-1 / 2 : ℝ) = _
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (mul_pos hW hs).le, ← Real.sqrt_eq_rpow]

/-- The actual normalized height has polynomial local jets from the
original physical height and the controlled integral coordinate. -/
theorem n06_airyRadialHeight_twoJet_bound {c W : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) {B : ℝ} (hB : 1 ≤ B)
    (hjet : ∀ x, N06ScalarJetTwoBound c x B)
    (hpos : ∀ x, 0 < c x) (hinv : ∀ x, (c x)⁻¹ ≤ B)
    {x : ℝ} (hW : ContDiffAt ℝ ∞ W x) (hWp : 0 < W x)
    (hWjet : N06ScalarJetTwoBound W x B) (hWinv : (W x)⁻¹ ≤ B) :
    ContDiffAt ℝ ∞ (n06AiryRadialHeight c W) x ∧
      0 < n06AiryRadialHeight c W x ∧
      N06ScalarJetTwoBound (n06AiryRadialHeight c W) x
        ((3 * (1536 : ℝ) ^ 5) * B ^ 35) ∧
      (n06AiryRadialHeight c W x)⁻¹ ≤ (3 * (1536 : ℝ) ^ 5) * B ^ 35 := by
  obtain ⟨_, hssm, _, hs⟩ := n06_airyRadialSlope_bounds hc hB hjet hpos hinv
  let F : ℝ → ℝ := fun t => W t * n06AiryRadialSlope c t
  let P : ℝ := 1536 * B ^ 7
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hFp : 0 < F x := mul_pos hWp (hs x).1
  have hFsm : ContDiffAt ℝ ∞ F x := hW.mul hssm.contDiffAt
  have hFjet : N06ScalarJetTwoBound F x P := by
    have hh := hWjet.mul_at hW hssm.contDiffAt hB0 (by positivity) (hs x).2.1
    convert hh using 1 <;> dsimp only [P] <;> ring
  have hP : 1 ≤ P := by
    have hpow := one_le_pow₀ hB (n := 7)
    dsimp only [P]
    linarith
  have hFinv : (F x)⁻¹ ≤ P := by
    rw [show F x = W x * n06AiryRadialSlope c x from rfl, mul_inv_rev]
    have hh := mul_le_mul (hs x).2.2 hWinv (inv_nonneg.mpr hWp.le) (by positivity)
    have h37 : B ^ 3 ≤ B ^ 7 := pow_le_pow_right₀ hB (by norm_num)
    calc
      _ ≤ (2 * B ^ 2) * B := hh
      _ = 2 * B ^ 3 := by ring
      _ ≤ 2 * B ^ 7 := mul_le_mul_of_nonneg_left h37 (by norm_num)
      _ ≤ P := by dsimp only [P]; nlinarith [pow_nonneg hB0 7]
  obtain ⟨hj, hi⟩ := hFjet.rpow_unit_at hFsm hFp hP hFinv
    (by norm_num : |(-1 / 2 : ℝ)| ≤ 1)
  have hheightSm : ContDiffAt ℝ ∞ (n06AiryRadialHeight c W) x :=
    (Real.contDiffAt_rpow_const_of_ne hFp.ne').comp x hFsm
  have hheightPos : 0 < n06AiryRadialHeight c W x := Real.rpow_pos_of_pos hFp _
  refine ⟨hheightSm, hheightPos, ?_, ?_⟩
  · convert hj using 1
    · rfl
    · dsimp only [P]
      ring
  · have hP35 : B ^ 7 ≤ B ^ 35 := pow_le_pow_right₀ hB (by norm_num)
    calc
      _ ≤ P := hi
      _ ≤ 1536 * B ^ 35 := mul_le_mul_of_nonneg_left hP35 (by norm_num)
      _ ≤ (3 * (1536 : ℝ) ^ 5) * B ^ 35 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hB0 35)

end ContinuousFlexibility.Analysis
