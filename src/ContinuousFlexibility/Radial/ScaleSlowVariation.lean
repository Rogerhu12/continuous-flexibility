module

public import ContinuousFlexibility.Radial.MorseChainScales

/-!
# Slow variation of the coefficient exponent against the attenuation exponent

The coefficient exponent `radialQ n = n^{5/2} log (e + n)` varies slowly compared with the
attenuation exponent `radialS n = (2/3) n^3`: for every `ε > 0` one has
`|q k - q m| ≤ ε |S k - S m| + C`.  The same holds for the enlarged weight
`logM m = 1 + m^{5/2} log (e + m)^2`, and `q` is dominated by `logM` up to a constant.
These are the scalar facts behind the absorption of fixed coefficient powers in the block Schur
summation (Section 6 of the manuscript).  No analytic operator statement is proved here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

/-! ### The attenuation exponent -/

theorem radialS_succ_sub_eq (m : ℕ) :
    radialS (m + 1) - radialS m = 2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 2 / 3 := by
  unfold radialS
  push_cast
  ring

theorem radialS_succ_sub (m : ℕ) : 2 * (m : ℝ) ^ 2 ≤ radialS (m + 1) - radialS m := by
  rw [radialS_succ_sub_eq]
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem radialS_strictMono : StrictMono radialS := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h := radialS_succ_sub_eq m
  have h1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := sq_nonneg _
  linarith

theorem radialS_monotone : Monotone radialS := radialS_strictMono.monotone

/-! ### Generic telescoping -/

theorem ssv_abs_sub_le_of_step (f S : ℕ → ℝ) (hS : Monotone S) {ε : ℝ} (hε : 0 ≤ ε) (m₀ : ℕ)
    (h : ∀ i, m₀ ≤ i → |f (i + 1) - f i| ≤ ε * (S (i + 1) - S i)) :
    ∃ C : ℝ, ∀ k m : ℕ, |f k - f m| ≤ ε * |S k - S m| + C := by
  obtain ⟨B, hB0, hBn⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, n ≤ m₀ → |f n| ≤ B :=
    ⟨∑ i ∈ Finset.range (m₀ + 1), |f i|,
      Finset.sum_nonneg (fun i _ => abs_nonneg _),
      fun n hn => Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))⟩
  have hd : ∀ a b, a ≤ m₀ → b ≤ m₀ → |f a - f b| ≤ 2 * B := by
    intro a b ha hb
    rw [abs_le]
    have h1 := abs_le.mp (hBn a ha)
    have h2 := abs_le.mp (hBn b hb)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have tail : ∀ m, m₀ ≤ m → ∀ k, m ≤ k → |f k - f m| ≤ ε * (S k - S m) := by
    intro m hm k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hstep := h k (hm.trans hk)
      calc |f (k + 1) - f m| = |(f (k + 1) - f k) + (f k - f m)| := by congr 1; ring
        _ ≤ |f (k + 1) - f k| + |f k - f m| := abs_add_le _ _
        _ ≤ ε * (S (k + 1) - S k) + ε * (S k - S m) := add_le_add hstep ih
        _ = ε * (S (k + 1) - S m) := by ring
  have ord : ∀ m k, m ≤ k → |f k - f m| ≤ ε * |S k - S m| + 2 * B := by
    intro m k hmk
    have hSk : |S k - S m| = S k - S m := abs_of_nonneg (sub_nonneg.mpr (hS hmk))
    rw [hSk]
    have hnn : 0 ≤ ε * (S k - S m) := mul_nonneg hε (sub_nonneg.mpr (hS hmk))
    rcases le_total m₀ m with hm | hm
    · have := tail m hm k hmk
      linarith
    · rcases le_total m₀ k with hk | hk
      · have h1 := tail m₀ le_rfl k hk
        have h2 := hd m₀ m le_rfl hm
        have h3 : ε * (S m) ≤ ε * S m₀ := mul_le_mul_of_nonneg_left (hS hm) hε
        calc |f k - f m| ≤ |f k - f m₀| + |f m₀ - f m| := abs_sub_le _ _ _
          _ ≤ ε * (S k - S m₀) + 2 * B := add_le_add h1 h2
          _ ≤ ε * (S k - S m) + 2 * B := by nlinarith
      · have := hd k m hk (hm)
        linarith
  refine ⟨2 * B, fun k m => ?_⟩
  rcases le_total m k with hmk | hkm
  · exact ord m k hmk
  · rw [abs_sub_comm (f k), abs_sub_comm (S k)]
    exact ord k m hkm

/-! ### Elementary facts about the building blocks -/

theorem ssv_rpow_five_half {x : ℝ} (hx : 0 ≤ x) : x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  have h : (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 := by norm_num
  rw [h, Real.rpow_add' hx (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow]

theorem ssv_rpow_three_half {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  have h : (3 / 2 : ℝ) = ((1 : ℕ) : ℝ) + 1 / 2 := by norm_num
  rw [h, Real.rpow_add' hx (by norm_num), Real.rpow_natCast, pow_one, Real.sqrt_eq_rpow]

theorem ssv_aux_P (x a b : ℝ) (hx : 0 ≤ x) (hb0 : 0 ≤ b) (hba : b ≤ a) (haa : a * a = x + 1)
    (hbb : b * b = x) :
    (x + 1) ^ 2 * a - x ^ 2 * b ≤ 3 * ((x + 1) * a) := by
  have hpos : 0 < a * a := by rw [haa]; linarith
  have ha0 : 0 < a := lt_of_le_of_ne (hb0.trans hba) (Ne.symm (mul_self_pos.mp hpos))
  have h1 : (a - b) * a ≤ 1 := by
    have : b * b ≤ a * b := mul_le_mul_of_nonneg_right hba hb0
    nlinarith
  have h2 : x ^ 2 * (a - b) ≤ x * a := by
    refine le_of_mul_le_mul_right ?_ ha0
    have h3 : x ^ 2 * ((a - b) * a) ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg x)
    have h4 : x * a * a = x * (x + 1) := by rw [mul_assoc, haa]
    nlinarith
  nlinarith

theorem ssv_P_inc {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ (5 / 2 : ℝ) - x ^ (5 / 2 : ℝ) ≤ 3 * ((x + 1) * Real.sqrt (x + 1)) := by
  rw [ssv_rpow_five_half (x := x + 1) (by linarith), ssv_rpow_five_half hx]
  exact ssv_aux_P x _ _ hx (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith))
    (Real.mul_self_sqrt (by linarith)) (Real.mul_self_sqrt hx)

theorem ssv_P_le {x : ℝ} (hx : 0 ≤ x) : x ^ (5 / 2 : ℝ) ≤ (x + 1) ^ (5 / 2 : ℝ) :=
  Real.rpow_le_rpow hx (by linarith) (by norm_num)

theorem ssv_P_div {x : ℝ} (hx : 0 ≤ x) :
    x ^ (5 / 2 : ℝ) * (1 / (Real.exp 1 + x)) ≤ (x + 1) * Real.sqrt (x + 1) := by
  have hp : 0 < Real.exp 1 + x := by positivity
  have hba : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have ha0 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
  rw [ssv_rpow_five_half hx, mul_one_div, div_le_iff₀ hp]
  have h1 : x ^ 2 * Real.sqrt x ≤ x ^ 2 * Real.sqrt (x + 1) :=
    mul_le_mul_of_nonneg_left hba (sq_nonneg x)
  have h2 : x ^ 2 ≤ (x + 1) * (Real.exp 1 + x) := by nlinarith [Real.exp_pos 1]
  have h3 : x ^ 2 * Real.sqrt (x + 1) ≤ ((x + 1) * (Real.exp 1 + x)) * Real.sqrt (x + 1) :=
    mul_le_mul_of_nonneg_right h2 ha0
  nlinarith

theorem ssv_one_le_log {x : ℝ} (hx : 0 ≤ x) : 1 ≤ log (Real.exp 1 + x) := by
  calc (1 : ℝ) = log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hx)

theorem ssv_log_le_succ {x : ℝ} (hx : 0 ≤ x) :
    log (Real.exp 1 + x) ≤ log (Real.exp 1 + (x + 1)) :=
  Real.log_le_log (by positivity) (by linarith)

theorem ssv_log_succ_sub_le {x : ℝ} (hx : 0 ≤ x) :
    log (Real.exp 1 + (x + 1)) - log (Real.exp 1 + x) ≤ 1 / (Real.exp 1 + x) := by
  have hp : 0 < Real.exp 1 + x := by positivity
  have hq : 0 < Real.exp 1 + (x + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at h
  have h2 : (Real.exp 1 + (x + 1)) / (Real.exp 1 + x) - 1 = 1 / (Real.exp 1 + x) := by
    rw [div_sub_one hp.ne']
    congr 1
    ring
  linarith

/-! ### Increments of `radialQ` -/

theorem radialQ_nonneg (m : ℕ) : 0 ≤ radialQ m := by
  unfold radialQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact mul_nonneg (Real.rpow_nonneg hm _) ((zero_le_one).trans (ssv_one_le_log hm))

theorem radialQ_monotone : Monotone radialQ := by
  apply monotone_nat_of_le_succ
  intro m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  unfold radialQ
  rw [hc]
  exact mul_le_mul (ssv_P_le hm) (ssv_log_le_succ hm)
    ((zero_le_one).trans (ssv_one_le_log hm)) (Real.rpow_nonneg (by linarith) _)

theorem ssv_radialQ_succ_sub_le (m : ℕ) :
    radialQ (m + 1) - radialQ m ≤
      4 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) * log (Real.exp 1 + ((m : ℝ) + 1)) := by
  have hx : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  unfold radialQ
  rw [hc]
  have hP := ssv_P_inc hx
  have hP0 : 0 ≤ (m : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hL := ssv_log_succ_sub_le hx
  have hL1 := ssv_one_le_log (show (0 : ℝ) ≤ (m : ℝ) + 1 by linarith)
  have hdiv := ssv_P_div hx
  have hW : 0 ≤ ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) := by positivity
  have hinv : 0 ≤ 1 / (Real.exp 1 + (m : ℝ)) := by positivity
  have e1 := mul_le_mul_of_nonneg_right hP (zero_le_one.trans hL1)
  have e2 := mul_le_mul_of_nonneg_left hL hP0
  have e4 : ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) ≤
      ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) * log (Real.exp 1 + ((m : ℝ) + 1)) :=
    le_mul_of_one_le_right hW hL1
  nlinarith

theorem radialQ_succ_sub_le (m : ℕ) :
    radialQ (m + 1) - radialQ m ≤
      4 * ((m : ℝ) + 1) ^ (3 / 2 : ℝ) * log (Real.exp 1 + m + 1) := by
  have hx : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [ssv_rpow_three_half (x := (m : ℝ) + 1) (by linarith), add_assoc (Real.exp 1) (m : ℝ) 1]
  exact ssv_radialQ_succ_sub_le m

/-! ### The enlarged weight -/

/-- The exponent of the enlarged weight `M_m = exp (1 + m^{5/2} log (e + m)^2)`. -/
def logM (m : ℕ) : ℝ := 1 + (m : ℝ) ^ (5 / 2 : ℝ) * log (Real.exp 1 + m) ^ 2

theorem logM_monotone : Monotone logM := by
  apply monotone_nat_of_le_succ
  intro m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  unfold logM
  rw [hc]
  have h := mul_le_mul (ssv_P_le hm)
    (pow_le_pow_left₀ ((zero_le_one).trans (ssv_one_le_log hm)) (ssv_log_le_succ hm) 2)
    (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)
  linarith

theorem ssv_logM_succ_sub_le (m : ℕ) :
    logM (m + 1) - logM m ≤
      5 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) *
        log (Real.exp 1 + ((m : ℝ) + 1)) ^ 2 := by
  have hx : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  unfold logM
  rw [hc]
  have hP := ssv_P_inc hx
  have hP0 : 0 ≤ (m : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hL := ssv_log_succ_sub_le hx
  have hL0 := ssv_one_le_log hx
  have hL1 := ssv_one_le_log (show (0 : ℝ) ≤ (m : ℝ) + 1 by linarith)
  have hLm := ssv_log_le_succ hx
  have hdiv := ssv_P_div hx
  have hW : 0 ≤ ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) := by positivity
  have hinv : 0 ≤ 1 / (Real.exp 1 + (m : ℝ)) := by positivity
  have e1 := mul_le_mul_of_nonneg_right hP (sq_nonneg (log (Real.exp 1 + ((m : ℝ) + 1))))
  have e2 : log (Real.exp 1 + ((m : ℝ) + 1)) ^ 2 - log (Real.exp 1 + (m : ℝ)) ^ 2 ≤
      1 / (Real.exp 1 + (m : ℝ)) * (2 * log (Real.exp 1 + ((m : ℝ) + 1))) := by
    have hfac : log (Real.exp 1 + ((m : ℝ) + 1)) ^ 2 - log (Real.exp 1 + (m : ℝ)) ^ 2 =
        (log (Real.exp 1 + ((m : ℝ) + 1)) - log (Real.exp 1 + (m : ℝ))) *
          (log (Real.exp 1 + ((m : ℝ) + 1)) + log (Real.exp 1 + (m : ℝ))) := by ring
    rw [hfac]
    calc _ ≤ 1 / (Real.exp 1 + (m : ℝ)) *
          (log (Real.exp 1 + ((m : ℝ) + 1)) + log (Real.exp 1 + (m : ℝ))) :=
          mul_le_mul hL le_rfl (by linarith) hinv
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hinv
  have e3 := mul_le_mul_of_nonneg_left e2 hP0
  have e5 := mul_le_mul_of_nonneg_right hdiv
    (show 0 ≤ 2 * log (Real.exp 1 + ((m : ℝ) + 1)) by linarith)
  have e6 : log (Real.exp 1 + ((m : ℝ) + 1)) ≤ log (Real.exp 1 + ((m : ℝ) + 1)) ^ 2 := by
    nlinarith
  have e7 := mul_le_mul_of_nonneg_left e6 hW
  nlinarith

/-! ### The asymptotic estimate -/

theorem ssv_W_log_sq_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ i : ℕ, T ≤ i →
      ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1) * log (Real.exp 1 + ((i : ℝ) + 1)) ^ 2 ≤
        δ * (i : ℝ) ^ 2 := by
  set K : ℝ := Real.exp 1 + 2 with hK
  have hK1 : 1 ≤ K := by
    have := Real.exp_pos 1
    rw [hK]; linarith
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 64 * K ^ 2 / δ ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop _
  have hev' : ∀ᶠ n : ℕ in Filter.atTop, 64 * K ^ 2 / δ ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hev
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hev'.and (Filter.eventually_ge_atTop 1))
  refine ⟨T, fun i hi => ?_⟩
  obtain ⟨hi1, hi2⟩ := hT i hi
  have hx1 : (1 : ℝ) ≤ (i : ℝ) := Nat.one_le_cast.mpr hi2
  set x : ℝ := (i : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have he := Real.exp_pos 1
  set t : ℝ := Real.exp 1 + (x + 1) with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hKx : 0 < K * x := mul_pos (by linarith) hx0
  have htK : t ≤ K * x := by
    rw [ht, hK]
    nlinarith [mul_le_mul_of_nonneg_left hx1 he.le]
  have hxK : x + 1 ≤ K * x := by
    rw [hK]
    nlinarith [mul_le_mul_of_nonneg_left hx1 he.le]
  have hlog := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 8 by norm_num)
  have hL0 : 0 ≤ log t := Real.log_nonneg ht1
  have h8 : log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
    calc log t ≤ t ^ (1 / 8 : ℝ) / (1 / 8) := hlog
      _ = 8 * t ^ (1 / 8 : ℝ) := by ring
  have h88 : (t ^ (1 / 8 : ℝ)) ^ 2 = t ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hsq : log t ^ 2 ≤ 64 * t ^ (1 / 4 : ℝ) := by
    calc log t ^ 2 ≤ (8 * t ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hL0 h8 2
      _ = 64 * t ^ (1 / 4 : ℝ) := by rw [mul_pow, h88]; norm_num
  have h2 : t ^ (1 / 4 : ℝ) ≤ (K * x) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow ht0.le htK (by norm_num)
  have h1 : (x + 1) ^ (3 / 2 : ℝ) ≤ (K * x) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hxK (by norm_num)
  have hw : (x + 1) * Real.sqrt (x + 1) = (x + 1) ^ (3 / 2 : ℝ) :=
    (ssv_rpow_three_half (by linarith)).symm
  have hstep1 : (x + 1) * Real.sqrt (x + 1) * log t ^ 2 ≤
      (K * x) ^ (3 / 2 : ℝ) * (64 * (K * x) ^ (1 / 4 : ℝ)) := by
    rw [hw]
    exact mul_le_mul h1 (hsq.trans (by linarith)) (sq_nonneg _) (Real.rpow_nonneg hKx.le _)
  have hstep2 : (K * x) ^ (3 / 2 : ℝ) * (64 * (K * x) ^ (1 / 4 : ℝ)) =
      64 * (K * x) ^ (7 / 4 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hKx]
    norm_num
  have hstep3 : (K * x) ^ (7 / 4 : ℝ) = K ^ (7 / 4 : ℝ) * x ^ (7 / 4 : ℝ) :=
    Real.mul_rpow (by linarith) hx0.le
  have hK74 : K ^ (7 / 4 : ℝ) ≤ K ^ 2 := by
    calc K ^ (7 / 4 : ℝ) ≤ K ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
      _ = K ^ 2 := Real.rpow_two K
  have hx74 : 0 ≤ x ^ (7 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hsum : x ^ (7 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ 2 := by
    have h : (7 / 4 : ℝ) + 1 / 4 = ((2 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_add hx0, h, Real.rpow_natCast]
  have hbig : 64 * K ^ 2 ≤ x ^ (1 / 4 : ℝ) * δ := (div_le_iff₀ hδ).mp hi1
  have hfin : 64 * K ^ 2 * x ^ (7 / 4 : ℝ) ≤ δ * x ^ 2 := by
    have := mul_le_mul_of_nonneg_right hbig hx74
    rw [← hsum]
    nlinarith
  calc (x + 1) * Real.sqrt (x + 1) * log t ^ 2
      ≤ 64 * (K * x) ^ (7 / 4 : ℝ) := hstep1.trans hstep2.le
    _ = 64 * (K ^ (7 / 4 : ℝ) * x ^ (7 / 4 : ℝ)) := by rw [hstep3]
    _ ≤ 64 * (K ^ 2 * x ^ (7 / 4 : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hK74 hx74
        linarith
    _ = 64 * K ^ 2 * x ^ (7 / 4 : ℝ) := by ring
    _ ≤ δ * x ^ 2 := hfin

/-! ### The main slow-variation statements -/

theorem radialQ_sub_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k m : ℕ, |radialQ k - radialQ m| ≤ ε * |radialS k - radialS m| + C := by
  obtain ⟨T, hT⟩ := ssv_W_log_sq_eventually (δ := ε / 3) (by positivity)
  refine ssv_abs_sub_le_of_step radialQ radialS radialS_monotone hε.le T ?_
  intro i hi
  rw [abs_of_nonneg (sub_nonneg.mpr (radialQ_monotone (Nat.le_add_right i 1)))]
  have h1 := ssv_radialQ_succ_sub_le i
  have h2 := hT i hi
  have h3 := radialS_succ_sub i
  have hx : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hL := ssv_one_le_log (show (0 : ℝ) ≤ (i : ℝ) + 1 by linarith)
  have hW : 0 ≤ ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1) := by positivity
  have h4 : ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1) * log (Real.exp 1 + ((i : ℝ) + 1)) ≤
      ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1) * log (Real.exp 1 + ((i : ℝ) + 1)) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hW
  have h5 : 0 ≤ ε * (i : ℝ) ^ 2 := by positivity
  have h6 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith

theorem logM_sub_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k m : ℕ, |logM k - logM m| ≤ ε * |radialS k - radialS m| + C := by
  obtain ⟨T, hT⟩ := ssv_W_log_sq_eventually (δ := ε / 3) (by positivity)
  refine ssv_abs_sub_le_of_step logM radialS radialS_monotone hε.le T ?_
  intro i hi
  rw [abs_of_nonneg (sub_nonneg.mpr (logM_monotone (Nat.le_add_right i 1)))]
  have h1 := ssv_logM_succ_sub_le i
  have h2 := hT i hi
  have h3 := radialS_succ_sub i
  have hx : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h5 : 0 ≤ ε * (i : ℝ) ^ 2 := by positivity
  have h6 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith

theorem ssv_P_le_cube {x : ℝ} (hx : 0 ≤ x) : x ^ (5 / 2 : ℝ) ≤ (Real.exp 1 + x) ^ 3 := by
  have he := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  rw [ssv_rpow_five_half hx]
  have h1 : x ^ 2 ≤ (Real.exp 1 + x) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
  have h2 : Real.sqrt x ≤ Real.exp 1 + x := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith [mul_nonneg he.le hx]
  calc x ^ 2 * Real.sqrt x ≤ (Real.exp 1 + x) ^ 2 * (Real.exp 1 + x) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (sq_nonneg _)
    _ = (Real.exp 1 + x) ^ 3 := by ring

theorem radialQ_le_logM_add (c : ℝ) : ∃ C : ℝ, ∀ m : ℕ, c * radialQ m ≤ logM m + C := by
  refine ⟨c ^ 2 * Real.exp |c| ^ 3, fun m => ?_⟩
  have hx : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP0 : 0 ≤ (m : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hL1 := ssv_one_le_log hx
  have hCnn : 0 ≤ c ^ 2 * Real.exp |c| ^ 3 := by positivity
  unfold radialQ logM
  by_cases h : |c| ≤ log (Real.exp 1 + m)
  · have h1 : c * log (Real.exp 1 + m) ≤ log (Real.exp 1 + m) ^ 2 := by
      have := mul_le_mul_of_nonneg_right ((le_abs_self c).trans h) (zero_le_one.trans hL1)
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hP0
    nlinarith
  · have hlt : log (Real.exp 1 + m) ≤ |c| := le_of_lt (lt_of_not_ge h)
    have hpos : 0 < Real.exp 1 + (m : ℝ) := by positivity
    have hexp : Real.exp 1 + (m : ℝ) ≤ Real.exp |c| := by
      calc Real.exp 1 + (m : ℝ) = Real.exp (log (Real.exp 1 + m)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp |c| := Real.exp_le_exp.mpr hlt
    have hP : (m : ℝ) ^ (5 / 2 : ℝ) ≤ Real.exp |c| ^ 3 :=
      (ssv_P_le_cube hx).trans (pow_le_pow_left₀ hpos.le hexp 3)
    have h3 : (m : ℝ) ^ (5 / 2 : ℝ) * log (Real.exp 1 + m) ≤ Real.exp |c| ^ 3 * |c| :=
      mul_le_mul hP hlt (zero_le_one.trans hL1) (by positivity)
    have h4 : c * ((m : ℝ) ^ (5 / 2 : ℝ) * log (Real.exp 1 + m)) ≤
        |c| * (Real.exp |c| ^ 3 * |c|) :=
      (mul_le_mul_of_nonneg_right (le_abs_self c)
        (mul_nonneg hP0 (zero_le_one.trans hL1))).trans
        (mul_le_mul_of_nonneg_left h3 (abs_nonneg c))
    have h5 : |c| * (Real.exp |c| ^ 3 * |c|) = c ^ 2 * Real.exp |c| ^ 3 := by
      calc |c| * (Real.exp |c| ^ 3 * |c|) = |c| ^ 2 * Real.exp |c| ^ 3 := by ring
        _ = c ^ 2 * Real.exp |c| ^ 3 := by rw [sq_abs]
    have h6 : 0 ≤ (m : ℝ) ^ (5 / 2 : ℝ) * log (Real.exp 1 + m) ^ 2 :=
      mul_nonneg hP0 (sq_nonneg _)
    linarith

theorem radialQ_shift_le (i₀ : ℕ) :
    ∃ c C : ℝ, ∀ k : ℕ, radialQ (k + i₀) ≤ c * radialQ k + C := by
  refine ⟨(1 + (i₀ : ℝ)) ^ (5 / 2 : ℝ) * (1 + log (1 + (i₀ : ℝ))), radialQ i₀, fun k => ?_⟩
  have hy : (0 : ℝ) ≤ i₀ := Nat.cast_nonneg i₀
  have hQ0 := radialQ_nonneg i₀
  by_cases hk : k = 0
  · subst hk
    have h0 : radialQ 0 = 0 := by
      unfold radialQ
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), zero_mul]
    rw [zero_add, h0, mul_zero, zero_add]
  · have hx1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hk)
    have hc : ((k + i₀ : ℕ) : ℝ) = (k : ℝ) + i₀ := by push_cast; ring
    have hQy := radialQ_nonneg i₀
    unfold radialQ at hQy ⊢
    rw [hc]
    clear hc hQ0
    generalize (k : ℝ) = x at hx1 ⊢
    generalize (i₀ : ℝ) = y at hy hQy ⊢
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hx0 : 0 ≤ x := by linarith
    have hA : 0 < 1 + y := by linarith
    have hxy : x + y ≤ (1 + y) * x := by nlinarith [mul_le_mul_of_nonneg_left hx1 hy]
    have hlogA : 0 ≤ log (1 + y) := Real.log_nonneg (by linarith)
    have hL0 := ssv_one_le_log hx0
    have hP : (x + y) ^ (5 / 2 : ℝ) ≤ (1 + y) ^ (5 / 2 : ℝ) * x ^ (5 / 2 : ℝ) := by
      calc (x + y) ^ (5 / 2 : ℝ) ≤ ((1 + y) * x) ^ (5 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) hxy (by norm_num)
        _ = _ := Real.mul_rpow hA.le hx0
    have hL : log (Real.exp 1 + (x + y)) ≤ (1 + log (1 + y)) * log (Real.exp 1 + x) := by
      have hle : Real.exp 1 + (x + y) ≤ (1 + y) * (Real.exp 1 + x) := by
        nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ Real.exp 1 + x by linarith) hy]
      calc log (Real.exp 1 + (x + y)) ≤ log ((1 + y) * (Real.exp 1 + x)) :=
            Real.log_le_log (by positivity) hle
        _ = log (1 + y) + log (Real.exp 1 + x) :=
            Real.log_mul hA.ne' (by positivity)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL0 hlogA]
    have hprod := mul_le_mul hP hL (zero_le_one.trans (ssv_one_le_log (by linarith : 0 ≤ x + y)))
      (by positivity)
    have hxx : (0 : ℝ) ≤ x ^ (5 / 2 : ℝ) * log (Real.exp 1 + x) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (zero_le_one.trans hL0)
    nlinarith

end ContinuousFlexibility.Radial

end
