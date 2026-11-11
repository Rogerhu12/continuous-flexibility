import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative Jacobi smallness from the actual edge estimates

The two deep mass-resistance inequalities control both the continued
fraction coefficient and the ratio in the mass-weighted node norm.
Only the lower diagonal bound and upper off-diagonal bound are needed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

theorem tailMassResistance_geometric_bound {Λ μ ν R K : ℝ}
    (hΛ : 0 < Λ) (hμ : 0 < μ) (hν : 0 < ν) (hR : 0 < R) (hK : 0 ≤ K)
    (hleft : K ≤ Λ * μ * R) (hright : K ≤ Λ * ν * R) :
    K ≤ (Λ * R) * (sqrt μ * sqrt ν) := by
  have hprod : K ^ 2 ≤ (Λ * R) ^ 2 * (μ * ν) := by
    calc
      K ^ 2 = K * K := sq K
      _ ≤ (Λ * μ * R) * (Λ * ν * R) :=
        mul_le_mul hleft hright hK (mul_nonneg (mul_nonneg hΛ.le hμ.le) hR.le)
      _ = _ := by ring
  have hh := sqrt_le_sqrt hprod
  rw [sqrt_sq hK, sqrt_mul (sq_nonneg _), sqrt_sq (mul_pos hΛ hR).le,
    sqrt_mul hμ.le] at hh
  exact hh

/-- For a deep edge, the continued-fraction coefficient lies in the
same fixed contraction interval used by `tailFractionLimit`. -/
theorem tailJacobi_epsilon_small {Λ μ ν R K b₀ b₁ c : ℝ}
    (hΛ : 0 < Λ) (hμ : 0 < μ) (hν : 0 < ν) (hR : 0 < R)
    (hb₀ : Λ * μ / 4 ≤ b₀) (hb₁ : Λ * ν / 4 ≤ b₁)
    (hc₀ : 0 ≤ c) (hc : c ≤ 2 / R)
    (hleft : K ≤ Λ * μ * R) (hright : K ≤ Λ * ν * R) (hK : 64 ≤ K) :
    c ^ 2 / (b₀ * b₁) ∈ Icc 0 (1 / 8 : ℝ) := by
  have hb₀pos : 0 < b₀ := (div_pos (mul_pos hΛ hμ) (by norm_num)).trans_le hb₀
  have hb₁pos : 0 < b₁ := (div_pos (mul_pos hΛ hν) (by norm_num)).trans_le hb₁
  have hK₀ : 0 ≤ K := by linarith
  have hKsq : (4096 : ℝ) ≤ K ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hK 2
    norm_num at hh
    exact hh
  have hdeep : K ^ 2 ≤ (Λ * R) ^ 2 * (μ * ν) := by
    calc
      K ^ 2 = K * K := sq K
      _ ≤ (Λ * μ * R) * (Λ * ν * R) :=
        mul_le_mul hleft hright hK₀ (mul_nonneg (mul_nonneg hΛ.le hμ.le) hR.le)
      _ = _ := by ring
  have hbprod : (Λ * μ / 4) * (Λ * ν / 4) ≤ b₀ * b₁ :=
    mul_le_mul hb₀ hb₁ (div_nonneg (mul_nonneg hΛ.le hν.le) (by norm_num)) hb₀pos.le
  have hbscaled := mul_le_mul_of_nonneg_right hbprod (sq_nonneg R)
  have hden : (64 : ℝ) ≤ (b₀ * b₁) * R ^ 2 := by
    nlinarith only [hbscaled, hdeep, hKsq]
  have hcR : c * R ≤ 2 := (le_div_iff₀ hR).mp hc
  have hcsq : c ^ 2 * R ^ 2 ≤ 4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hc₀ hR.le) hcR 2
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  refine ⟨div_nonneg (sq_nonneg c) (mul_pos hb₀pos hb₁pos).le, ?_⟩
  apply (div_le_iff₀ (mul_pos hb₀pos hb₁pos)).mpr
  have hh : c ^ 2 * R ^ 2 ≤ ((1 / 8 : ℝ) * (b₀ * b₁)) * R ^ 2 := by
    nlinarith only [hden, hcsq]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hR)).mp hh

/-- The same hypotheses give the mass-weighted ratio bound needed for
square summability of the natural node sequence. -/
theorem tailJacobi_weightedRatio_small {Λ μ ν R K b c : ℝ}
    (hΛ : 0 < Λ) (hμ : 0 < μ) (hν : 0 < ν) (hR : 0 < R)
    (hb : Λ * ν / 4 ≤ b) (hc : c ≤ 2 / R)
    (hleft : K ≤ Λ * μ * R) (hright : K ≤ Λ * ν * R) (hK : 64 ≤ K) :
    sqrt ν * (c / b) ≤ (1 / 4 : ℝ) * sqrt μ := by
  have hbpos : 0 < b := (div_pos (mul_pos hΛ hν) (by norm_num)).trans_le hb
  have hgeom : (32 : ℝ) ≤ (Λ * R) * (sqrt μ * sqrt ν) :=
    (show (32 : ℝ) ≤ K by linarith).trans
      (tailMassResistance_geometric_bound hΛ hμ hν hR (by linarith) hleft hright)
  have hg : 32 * sqrt ν ≤ sqrt μ * (Λ * ν * R) := by
    calc
      32 * sqrt ν ≤ ((Λ * R) * (sqrt μ * sqrt ν)) * sqrt ν :=
        mul_le_mul_of_nonneg_right hgeom (sqrt_nonneg _)
      _ = sqrt μ * (Λ * R) * (sqrt ν) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt hν.le]; ring
  have hcR : c * R ≤ 2 := (le_div_iff₀ hR).mp hc
  have hbR := mul_le_mul_of_nonneg_right hb hR.le
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hbpos).mpr
  apply (mul_le_mul_iff_left₀ hR).mp
  calc
    (sqrt ν * c) * R = sqrt ν * (c * R) := by ring
    _ ≤ 2 * sqrt ν := by
      simpa only [mul_comm (sqrt ν) 2] using
        mul_le_mul_of_nonneg_left hcR (sqrt_nonneg ν)
    _ ≤ sqrt μ * (Λ * ν * R) / 16 := by linarith only [hg]
    _ ≤ ((1 / 4 : ℝ) * sqrt μ * b) * R := by
      have hh := mul_le_mul_of_nonneg_left hbR
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (sqrt_nonneg μ))
      convert hh using 1 <;> ring

/-- Sequence form of the two numerical bounds used by the exact natural
node construction. -/
theorem tailJacobi_smallness {Λ K : ℝ} {μ R b c : ℕ → ℝ}
    (hΛ : 0 < Λ) (hμ : ∀ n, 0 < μ n) (hR : ∀ n, 0 < R n)
    (hb : ∀ n, Λ * μ n / 4 ≤ b n) (hc₀ : ∀ n, 0 ≤ c n)
    (hc : ∀ n, c n ≤ 2 / R n)
    (hleft : ∀ n, K ≤ Λ * μ n * R n)
    (hright : ∀ n, K ≤ Λ * μ (n + 1) * R n) (hK : 64 ≤ K) :
    (∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8 : ℝ)) ∧
      (∀ n, sqrt (μ (n + 1)) * (c n / b (n + 1)) ≤ (1 / 4 : ℝ) * sqrt (μ n)) := by
  constructor
  · intro n
    exact tailJacobi_epsilon_small hΛ (hμ n) (hμ (n + 1)) (hR n) (hb n) (hb (n + 1))
      (hc₀ n) (hc n) (hleft n) (hright n) hK
  · intro n
    exact tailJacobi_weightedRatio_small hΛ (hμ n) (hμ (n + 1)) (hR n) (hb (n + 1))
      (hc n) (hleft n) (hright n) hK

end ContinuousFlexibility.Radial
