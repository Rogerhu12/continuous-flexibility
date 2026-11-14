module

public import ContinuousFlexibility.Analysis.ScalarInverseJetBounds

/-!
# Inverse jets with their exact scale exponents

Conjugating a scalar diffeomorphism by a dilation turns a bound of order
`R^(k-1)` into an ordinary uniform bound. The finite-order inverse theorem
then gives the same exponent for the actual inverse. Only forward jets
through the requested order are used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

def scalarInverseScale (R : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => R * f (R⁻¹ * x)

theorem scalarInverseScale_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    ContDiff ℝ ∞ (scalarInverseScale R f) :=
  contDiff_const.mul (hf.comp (contDiff_const.mul contDiff_id))

theorem scalarInverseScale_iteratedDeriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : R ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    iteratedDeriv n (scalarInverseScale R f) x =
      (R ^ (n - 1))⁻¹ * iteratedDeriv n f (R⁻¹ * x) := by
  have hpow : (R⁻¹) ^ n = (R⁻¹) ^ (n - 1) * R⁻¹ := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hfactor : R * (R⁻¹) ^ n = (R ^ (n - 1))⁻¹ := by
    calc
      R * (R⁻¹) ^ n = (R * R⁻¹) * (R⁻¹) ^ (n - 1) := by
        rw [hpow]
        ring
      _ = (R ^ (n - 1))⁻¹ := by rw [mul_inv_cancel₀ hR, one_mul, inv_pow]
  change iteratedDeriv n (fun y : ℝ => R * f (R⁻¹ * y)) x = _
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (hf.of_le (by simp)) R⁻¹]
  exact (mul_assoc R ((R⁻¹) ^ n) _).symm.trans
    (congrArg (fun a : ℝ => a * iteratedDeriv n f (R⁻¹ * x)) hfactor)

theorem scalarInverseScale_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : R ≠ 0) (x : ℝ) :
    deriv (scalarInverseScale R f) x = deriv f (R⁻¹ * x) := by
  simpa only [iteratedDeriv_one, Nat.sub_self, pow_zero, inv_one, one_mul] using
    scalarInverseScale_iteratedDeriv hf hR 1 le_rfl x

theorem scalarInverseScale_leftInverse {f g : ℝ → ℝ}
    (hleft : Function.LeftInverse g f) {R : ℝ} (hR : R ≠ 0) :
    Function.LeftInverse (scalarInverseScale R g) (scalarInverseScale R f) := by
  intro x
  change R * g (R⁻¹ * (R * f (R⁻¹ * x))) = x
  rw [inv_mul_cancel_left₀ hR, hleft, mul_inv_cancel_left₀ hR]

theorem inverse_iteratedDeriv_scale_bound_finite
    {ι : Type*} (f g : ι → ℝ → ℝ) (R : ι → ℝ)
    (hR : ∀ i, 0 < R i) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {a : ℝ} (ha : 0 < a) (hlower : ∀ i x, a ≤ deriv (f i) x)
    (hleft : ∀ i x, g i (f i x) = x) (hright : ∀ i x, f i (g i x) = x)
    (N : ℕ)
    (hfbound : ∀ n : ℕ, 1 ≤ n → n ≤ N → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i x, |iteratedDeriv n (f i) x| ≤ A * R i ^ (n - 1)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, |iteratedDeriv n (g i) x| ≤ K * R i ^ (n - 1) := by
  let F (i : ι) : ℝ → ℝ := scalarInverseScale (R i) (f i)
  let G (i : ι) : ℝ → ℝ := scalarInverseScale (R i) (g i)
  have hF (i : ι) : ContDiff ℝ ∞ (F i) := scalarInverseScale_contDiff (hf i) (R i)
  have hlow (i : ι) (x : ℝ) : a ≤ deriv (F i) x := by
    rw [show deriv (F i) x = deriv (f i) ((R i)⁻¹ * x) from
      scalarInverseScale_deriv (hf i) (hR i).ne' x]
    exact hlower i _
  have hleftF (i : ι) : Function.LeftInverse (G i) (F i) :=
    scalarInverseScale_leftInverse (hleft i) (hR i).ne'
  have hrightF (i : ι) : Function.LeftInverse (F i) (G i) :=
    scalarInverseScale_leftInverse (hright i) (hR i).ne'
  have hFb (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ i x, |iteratedDeriv n (F i) x| ≤ A := by
    obtain ⟨A, hA, hb⟩ := hfbound n hn hnN
    refine ⟨A, hA, fun i x => ?_⟩
    have hp : 0 < R i ^ (n - 1) := pow_pos (hR i) _
    rw [show iteratedDeriv n (F i) x =
      (R i ^ (n - 1))⁻¹ * iteratedDeriv n (f i) ((R i)⁻¹ * x) from
      scalarInverseScale_iteratedDeriv (hf i) (hR i).ne' n hn x,
      abs_mul, abs_of_pos (inv_pos.mpr hp)]
    calc
      _ ≤ (R i ^ (n - 1))⁻¹ * (A * R i ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left (hb i _) (inv_nonneg.mpr hp.le)
      _ = A := by
        rw [mul_left_comm, inv_mul_cancel₀ hp.ne', mul_one]
  have hgb (i : ι) : ContDiff ℝ ∞ (g i) :=
    ContinuousFlexibility.Statements.returnChart_inverse_contDiff
      (f i) (g i) (hf i) (fun x => ha.trans_le (hlower i x)) (hleft i) (hright i)
  have hGb := inverse_iteratedDeriv_uniform_bound_finite F G hF ha hlow
    hleftF hrightF N hFb
  intro n hn hnN
  obtain ⟨K, hK, hb⟩ := hGb n hn hnN
  refine ⟨K, hK, fun i x => ?_⟩
  have hp : 0 < R i ^ (n - 1) := pow_pos (hR i) _
  have hscaled := hb i (R i * x)
  rw [show iteratedDeriv n (G i) (R i * x) =
      (R i ^ (n - 1))⁻¹ * iteratedDeriv n (g i) ((R i)⁻¹ * (R i * x)) from
      scalarInverseScale_iteratedDeriv (hgb i) (hR i).ne' n hn (R i * x),
    inv_mul_cancel_left₀ (hR i).ne', abs_mul, abs_of_pos (inv_pos.mpr hp)] at hscaled
  calc
    |iteratedDeriv n (g i) x| =
        R i ^ (n - 1) * ((R i ^ (n - 1))⁻¹ * |iteratedDeriv n (g i) x|) :=
      (mul_inv_cancel_left₀ hp.ne' _).symm
    _ ≤ R i ^ (n - 1) * K := mul_le_mul_of_nonneg_left hscaled hp.le
    _ = K * R i ^ (n - 1) := mul_comm _ _

end ContinuousFlexibility.Analysis
