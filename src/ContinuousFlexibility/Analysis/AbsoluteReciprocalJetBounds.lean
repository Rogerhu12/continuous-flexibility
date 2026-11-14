module

public import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual reciprocal jets from an absolute lower bound

The exact scalar derivative formula gives a factorial bound on the
whole set |t| ≥ κ. No upper bound on t is used. The positive and negative
sign germs identify |t|⁻¹ with ±(1/t), so these are bounds on genuine
Fréchet derivatives of the absolute reciprocal.

Composition with an actual scalar field then has one common low order
and fixed loss. Applied to the actual plane Jacobian, this supplies the
reciprocal primitive without assuming its higher jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def absoluteReciprocalJetBound (κ : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * (κ ^ (n + 1))⁻¹

theorem absoluteReciprocalJetBound_nonneg {κ : ℝ}
    (hκ : 0 < κ) (n : ℕ) : 0 ≤ absoluteReciprocalJetBound κ n :=
  mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (pow_nonneg hκ.le _))

/-- The exact reciprocal formula also controls arbitrarily large
denominators, using only their absolute lower bound. -/
theorem norm_iteratedFDeriv_one_div_le
    {κ x : ℝ} (hκ : 0 < κ) (hx : κ ≤ |x|) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => 1 / t) x‖ ≤
      absoluteReciprocalJetBound κ n := by
  have hp := iteratedDerivWithin_one_div (𝕜 := ℝ) n isOpen_univ (mem_univ x)
  have hexp : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  have hformula : iteratedDeriv n (fun t : ℝ => 1 / t) x =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * (x ^ (n + 1))⁻¹ := by
    simpa only [iteratedDerivWithin_univ, hexp, zpow_neg, zpow_natCast] using hp
  have hinv : (|x| ^ (n + 1))⁻¹ ≤ (κ ^ (n + 1))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (pow_pos hκ _) (pow_le_pow_left₀ hκ.le hx (n + 1))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hformula]
  calc
    ‖(-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * (x ^ (n + 1))⁻¹‖ =
        (Nat.factorial n : ℝ) * (|x| ^ (n + 1))⁻¹ := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_of_nonneg (Nat.cast_nonneg n.factorial), norm_inv, Real.norm_eq_abs]
    _ ≤ absoluteReciprocalJetBound κ n :=
      mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)

theorem contDiffAt_absoluteReciprocal {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ => |t|⁻¹) x := by
  have ha : ContDiffAt ℝ ∞ (fun t : ℝ => |t|) x := contDiffAt_abs hx
  exact ha.fun_inv (abs_ne_zero.mpr hx)

/-- Sign is constant on a neighborhood of every nonzero denominator.
The absolute reciprocal therefore has the same jet norms as 1/t. -/
theorem norm_iteratedFDeriv_absoluteReciprocal_le
    {κ x : ℝ} (hκ : 0 < κ) (hx : κ ≤ |x|) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => |t|⁻¹) x‖ ≤
      absoluteReciprocalJetBound κ n := by
  have hx0 : x ≠ 0 := abs_pos.mp (hκ.trans_le hx)
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have he : (fun t : ℝ => |t|⁻¹) =ᶠ[𝓝 x] -(fun t : ℝ => 1 / t) := by
      filter_upwards [eventually_lt_nhds hneg] with t ht
      simp only [abs_of_neg ht, inv_neg, Pi.neg_apply, one_div]
    rw [(he.iteratedFDeriv ℝ n).self_of_nhds, iteratedFDeriv_neg_apply, norm_neg]
    exact norm_iteratedFDeriv_one_div_le hκ hx n
  · have he : (fun t : ℝ => |t|⁻¹) =ᶠ[𝓝 x] (fun t : ℝ => 1 / t) := by
      filter_upwards [eventually_gt_nhds hpos] with t ht
      simp only [abs_of_pos ht, one_div]
    rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
    exact norm_iteratedFDeriv_one_div_le hκ hx n

/-- The low order and loss precede the lower bound κ as well as every
output order. Only genuine positive-order jets of J are inputs. -/
theorem absoluteReciprocal_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∀ κ : ℝ, 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ J : PolarPoint → ℝ, ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ J x → κ ≤ |J x| →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k J x‖ ≤
          C k * W ^ (C k) * (1 + p (k + inputLoss) z)) →
      ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun q => |J q|⁻¹) x‖ ≤
        B n * W ^ (B n) * (1 + p (n + loss) z) := by
  classical
  obtain ⟨base, loss, hcomposition⟩ :=
    coordinateComposition_fixed_loss_material_bound
      (X := PolarPoint) (Y := ℝ) (Z := ℝ) hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro C hC κ hκ
  let R : ℕ → ℝ := fun k => max 1 (max (C k) (absoluteReciprocalJetBound κ k))
  have hR (k : ℕ) : 1 ≤ R k := le_max_left _ _
  have hCR (k : ℕ) : C k ≤ R k :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hKR (k : ℕ) : absoluteReciprocalJetBound κ k ≤ R k :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Q, hQ, hQb⟩ := hcomposition R hR
  let B : ℕ → ℝ := fun n => 1 + max (absoluteReciprocalJetBound κ 0) (Q (n - 1))
  have hB (n : ℕ) : 0 < B n := by
    have hm := le_max_right (absoluteReciprocalJetBound κ 0) (Q (n - 1))
    dsimp only [B]
    linarith [hQ (n - 1)]
  have hKB : absoluteReciprocalJetBound κ 0 ≤ B 0 := by
    have hm := le_max_left (absoluteReciprocalJetBound κ 0) (Q (0 - 1))
    dsimp only [B]
    linarith
  have hQB (n : ℕ) : Q n ≤ B (n + 1) := by
    have hi : n + 1 - 1 = n := by omega
    have hm := le_max_right (absoluteReciprocalJetBound κ 0) (Q n)
    dsimp only [B]
    rw [hi]
    linarith
  refine ⟨B, hB, ?_⟩
  intro z hz W hW J x hJ hlower hraw n
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hself (D : ℝ) (hD : 0 ≤ D) (s : ℕ) :
      D ≤ D * W ^ D * (1 + p s z) := by
    have hpow : 1 ≤ W ^ D := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hW hD)
    have hstate : 1 ≤ 1 + p s z := le_add_of_nonneg_right (apply_nonneg _ _)
    have h₁ : D ≤ D * W ^ D := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hD
    have h₂ : D * W ^ D ≤ D * W ^ D * (1 + p s z) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hstate
        (mul_nonneg hD (Real.rpow_nonneg hW0 _))
    exact h₁.trans h₂
  have houter (k : ℕ) (_ : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k (fun t : ℝ => |t|⁻¹) (J x)‖ ≤
        R k * W ^ (R k) * (1 + p (k + inputLoss) z) :=
    ((norm_iteratedFDeriv_absoluteReciprocal_le hκ hlower k).trans (hKR k)).trans
      (hself (R k) (zero_le_one.trans (hR k)) (k + inputLoss))
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k J x‖ ≤
        R k * W ^ (R k) * (1 + p (k + inputLoss) z) :=
    (hraw k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (hCR k) (Real.rpow_le_rpow_of_exponent_le hW (hCR k))
        (Real.rpow_nonneg hW0 _) (zero_le_one.trans (hR k)))
      (add_nonneg zero_le_one (apply_nonneg _ _)))
  cases n with
  | zero =>
    have hv : ‖|J x|⁻¹‖ ≤ absoluteReciprocalJetBound κ 0 := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_absoluteReciprocal_le hκ hlower 0
    simpa only [norm_iteratedFDeriv_zero] using
      (hv.trans hKB).trans (hself (B 0) (hB 0).le (0 + loss))
  | succ n =>
    have hx : J x ≠ 0 := abs_pos.mp (hκ.trans_le hlower)
    have hb := hQb z hz W hW (fun t : ℝ => |t|⁻¹) J x
      (contDiffAt_absoluteReciprocal hx) hJ houter hinner n
    have hpack : Q n * W ^ (Q n) ≤ B (n + 1) * W ^ (B (n + 1)) :=
      mul_le_mul (hQB n) (Real.rpow_le_rpow_of_exponent_le hW (hQB n))
        (Real.rpow_nonneg hW0 _) (hB (n + 1)).le
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hpack
      (add_nonneg zero_le_one (apply_nonneg _ _)))
    simpa only [Function.comp_def] using hb'

end ContinuousFlexibility.Analysis
