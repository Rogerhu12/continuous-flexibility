module

public import ContinuousFlexibility.Analysis.N07aAngularBandLift

/-!
# Exact fixed-band source norms and uniform angular-order comparison

The finite derivative sum is the norm prescribed by `VolumeModelData`.
Comparing its exact band weights with the generic angular Sobolev weight
gives constants independent of the base derivative order and of the
number or geometry of radial components.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

theorem n07aAngularLevelLift_norm_sq (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b t n : ℕ) (u : V.level γ w b) :
    ‖n07aAngularLevelLift hV γ w hK b t n u‖ ^ 2 =
      n07aAngularJetWeightSq t n *
        ∑' m, ‖n07aAngularBand m (hK m) n (u.val m 0)‖ ^ 2 := by
  rw [← Submodule.norm_coe, n07aAngularLevelLift_val, ← angular_tsum_norm_sq,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [n07aAngularJetsLift_piece, n07aAngularBandPieceLift_norm_sq]

theorem n07aAngularLevelLift_self (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b n : ℕ) (u : V.level γ w b) :
    n07aAngularLevelLift hV γ w hK b b n u = n07aAngularLevelBand hV γ w hK b n u := by
  have h := n07aAngularLevelLift_truncate hV γ w hK (le_refl b) n u
  simpa only [n07aAngularLevelTruncate_refl] using h

/-- An exact equality, before any comparison of Sobolev conventions. -/
theorem n07aAngularLevelLift_norm_ratio (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b t n : ℕ) (u : V.level γ w b) :
    n07aAngularJetWeightSq b n * ‖n07aAngularLevelLift hV γ w hK b t n u‖ ^ 2 =
      n07aAngularJetWeightSq t n * ‖n07aAngularLevelBand hV γ w hK b n u‖ ^ 2 := by
  rw [← n07aAngularLevelLift_self hV γ w hK b n u,
    n07aAngularLevelLift_norm_sq, n07aAngularLevelLift_norm_sq]
  ring

theorem n07aAngularLevelLift_norm_lower (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b p n : ℕ) (u : V.level γ w b) :
    angularWeight n ^ p * ‖n07aAngularLevelBand hV γ w hK b n u‖ ≤
      ‖n07aAngularLevelLift hV γ w hK b (b + p) n u‖ := by
  have hq : 0 < n07aAngularJetWeightSq b n :=
    zero_lt_one.trans_le (n07aAngularJetWeightSq_one_le b n)
  apply (sq_le_sq₀ (mul_nonneg (pow_nonneg (angularWeight_nonneg n) p) (norm_nonneg _))
    (norm_nonneg _)).mp
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    n07aAngularJetWeightSq b n *
        (angularWeight n ^ p * ‖n07aAngularLevelBand hV γ w hK b n u‖) ^ 2 =
        (angularWeight n ^ (2 * p) * n07aAngularJetWeightSq b n) *
          ‖n07aAngularLevelBand hV γ w hK b n u‖ ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm p 2]
      ring
    _ ≤ n07aAngularJetWeightSq (b + p) n *
        ‖n07aAngularLevelBand hV γ w hK b n u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (n07aAngularJetWeightSq_lower_spectral b p n) (sq_nonneg _)
    _ = _ := (n07aAngularLevelLift_norm_ratio hV γ w hK b (b + p) n u).symm

def n07aAngularLiftConstant (p : ℕ) : ℝ := Real.sqrt (2 * 4 ^ p)

theorem n07aAngularLiftConstant_nonneg (p : ℕ) : 0 ≤ n07aAngularLiftConstant p :=
  Real.sqrt_nonneg _

theorem n07aAngularLiftConstant_sq (p : ℕ) : n07aAngularLiftConstant p ^ 2 = 2 * 4 ^ p :=
  Real.sq_sqrt (by positivity)

theorem n07aAngularLevelLift_norm_upper (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b p n : ℕ) (u : V.level γ w b) :
    ‖n07aAngularLevelLift hV γ w hK b (b + p) n u‖ ≤
      n07aAngularLiftConstant p * angularWeight n ^ p *
        ‖n07aAngularLevelBand hV γ w hK b n u‖ := by
  have hq : 0 < n07aAngularJetWeightSq b n :=
    zero_lt_one.trans_le (n07aAngularJetWeightSq_one_le b n)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg (n07aAngularLiftConstant_nonneg p) (pow_nonneg (angularWeight_nonneg n) p))
    (norm_nonneg _))).mp
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    n07aAngularJetWeightSq b n *
        ‖n07aAngularLevelLift hV γ w hK b (b + p) n u‖ ^ 2 =
        n07aAngularJetWeightSq (b + p) n *
          ‖n07aAngularLevelBand hV γ w hK b n u‖ ^ 2 :=
      n07aAngularLevelLift_norm_ratio hV γ w hK b (b + p) n u
    _ ≤ (2 * 4 ^ p * angularWeight n ^ (2 * p) * n07aAngularJetWeightSq b n) *
        ‖n07aAngularLevelBand hV γ w hK b n u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (n07aAngularJetWeightSq_upper_spectral b p n) (sq_nonneg _)
    _ = _ := by
      rw [mul_pow, mul_pow, n07aAngularLiftConstant_sq, ← pow_mul, Nat.mul_comm p 2]
      ring

end ContinuousFlexibility.Statements
