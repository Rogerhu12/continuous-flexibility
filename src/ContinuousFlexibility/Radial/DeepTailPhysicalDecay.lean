import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Physical attenuation of the natural node values

The mass-resistance lower bound and the genuine natural-line recurrence
give the cubic attenuation exponent in the frozen physical conclusion.
The accumulated errors are absorbed by a fixed power of `radialE`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

/-- The increment of the five-halves power absorbs the complete local
mass-resistance error, including the small indices. -/
theorem physicalDecay_fiveHalf_step (n : ℕ) :
    (n : ℝ) ^ (3 / 2 : ℝ) + n + 1 ≤
      ((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsqrt : 1 ≤ sqrt (n : ℝ) := by
    simpa only [sqrt_one] using sqrt_le_sqrt hn1
  have hsqrt' : sqrt (n : ℝ) ≤ sqrt ((n : ℝ) + 1) :=
    sqrt_le_sqrt (by linarith)
  rw [ssv_rpow_three_half hn0, ssv_rpow_five_half (Nat.cast_nonneg (n + 1)),
    ssv_rpow_five_half hn0, Nat.cast_add, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hnext := mul_le_mul_of_nonneg_left hsqrt' (sq_nonneg ((n : ℝ) + 1))
  nlinarith

theorem physicalDecay_exponent_step {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (n : ℕ) :
    log A - 2 * (n : ℝ) ^ 2 + B * ((n : ℝ) ^ (3 / 2 : ℝ) + n) ≤
      -(radialS (n + 1) - radialS n) +
        (max 0 (log A) + B + 3) *
          (((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ)) := by
  let H : ℝ := (n : ℝ) ^ (3 / 2 : ℝ) + n + 1
  let K : ℝ := max 0 (log A) + B + 3
  have hP : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := rpow_nonneg (Nat.cast_nonneg n) _
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlog : log A ≤ max 0 (log A) := le_max_right _ _
  have hlogH : max 0 (log A) ≤ max 0 (log A) * H :=
    le_mul_of_one_le_right (le_max_left _ _) hH
  have hstep := mul_le_mul_of_nonneg_left (physicalDecay_fiveHalf_step n) hK
  rw [radialS_succ_sub_eq]
  change _ ≤ -(2 * (n : ℝ) ^ 2 + 2 * n + 2 / 3) + K * _
  have herr : log A + B * ((n : ℝ) ^ (3 / 2 : ℝ) + n) + 2 * n + 2 / 3 ≤ K * H := by
    dsimp [K, H] at *
    nlinarith
  linarith

/-- Any sequence with the physical one-step attenuation has the exact
coefficient-weight/cubic-exponential bound used by the radial target. -/
theorem physical_nodes_decay_of_step (a : ℕ → ℝ) (start : ℕ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (ha : ∀ n, |a (n + 1)| ≤ A *
      exp (-2 * ((start + n : ℕ) : ℝ) ^ 2 +
        B * (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) * |a n|) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      |a n| ≤ C * radialE (start + n) ^ C * exp (-radialS (start + n)) := by
  let K : ℝ := max 0 (log A) + B + 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let e : ℕ → ℝ := fun n => exp (K * (n : ℝ) ^ (5 / 2 : ℝ) - radialS n)
  have he (n : ℕ) : 0 < e n := exp_pos _
  let M : ℝ := |a 0| / e start
  have hM : 0 ≤ M := div_nonneg (abs_nonneg _) (he start).le
  have hstep (n : ℕ) : A *
      exp (-2 * (n : ℝ) ^ 2 + B * ((n : ℝ) ^ (3 / 2 : ℝ) + n)) * e n ≤ e (n + 1) := by
    dsimp only [e]
    calc
      _ = exp (log A + (-2 * (n : ℝ) ^ 2 + B * ((n : ℝ) ^ (3 / 2 : ℝ) + n)) +
          (K * (n : ℝ) ^ (5 / 2 : ℝ) - radialS n)) := by
        simp only [exp_add, exp_log hA, mul_assoc]
      _ ≤ _ := exp_le_exp.mpr (by
        have hh := physicalDecay_exponent_step hA hB n
        change log A - 2 * (n : ℝ) ^ 2 + B * ((n : ℝ) ^ (3 / 2 : ℝ) + n) ≤
          -(radialS (n + 1) - radialS n) + K * _ at hh
        linarith)
  have hbound (n : ℕ) : |a n| ≤ M * e (start + n) := by
    induction n with
    | zero =>
        dsimp only [M]
        rw [Nat.add_zero, div_mul_cancel₀ _ (he start).ne']
    | succ n ih =>
        calc
          _ ≤ A * exp (-2 * ((start + n : ℕ) : ℝ) ^ 2 +
              B * (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) *
                (M * e (start + n)) :=
            (ha n).trans (mul_le_mul_of_nonneg_left ih (mul_nonneg hA.le (exp_pos _).le))
          _ = M * (A * exp (-2 * ((start + n : ℕ) : ℝ) ^ 2 +
              B * (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) *
                e (start + n)) := by ring
          _ ≤ M * e (start + n + 1) := mul_le_mul_of_nonneg_left (hstep (start + n)) hM
          _ = _ := by rw [Nat.add_assoc]
  let C : ℝ := M + K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; linarith
  have hKC : K ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n => (hbound n).trans ?_⟩
  have hQ : ((start + n : ℕ) : ℝ) ^ (5 / 2 : ℝ) ≤ radialQ (start + n) := by
    unfold radialQ
    exact le_mul_of_one_le_right (rpow_nonneg (Nat.cast_nonneg _) _)
      (ssv_one_le_log (Nat.cast_nonneg _))
  have hE : e (start + n) ≤ radialE (start + n) ^ C * exp (-radialS (start + n)) := by
    rw [radialE, ← exp_mul, ← exp_add]
    apply exp_le_exp.mpr
    have hKQ := mul_le_mul_of_nonneg_left hQ hK
    have hCQ := mul_le_mul_of_nonneg_right hKC (radialQ_nonneg (start + n))
    linarith
  calc
    _ ≤ C * (radialE (start + n) ^ C * exp (-radialS (start + n))) :=
      mul_le_mul hMC hE (he (start + n)).le hC.le
    _ = _ := by ring

/-- Apply the scalar attenuation lemma directly to the existing natural
node recurrence and the physical mass-resistance lower bound. -/
theorem exists_tailNatural_nodes_decay {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ}
    (hline : TailNaturalLineAndKernel T)
    (hphysical : TailPhysicalRelation D T right j start) :
    ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧
      (∃ x ∈ Set.Ioo T.entrance T.endpoint, u x ≠ 0) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n,
        |u (T.node n)| ≤ C * radialE (start + n) ^ C * exp (-radialS (start + n)) := by
  obtain ⟨u, hu, hnonzero, _, A, hA, hstep⟩ := hline
  obtain ⟨_, _, _, _, B, hB, hden⟩ := hphysical
  refine ⟨u, hu, hnonzero, ?_⟩
  apply physical_nodes_decay_of_step (fun n => u (T.node n)) start hA hB.le
  intro n
  apply (hstep n).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    A / (T.Λ * tailMass T (n + 1) * tailResistance T n) ≤
        A / exp (2 * ((start + n : ℕ) : ℝ) ^ 2 -
          B * (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) :=
      div_le_div_of_nonneg_left hA.le (exp_pos _) (hden n)
    _ = _ := by rw [div_eq_mul_inv, ← exp_neg]; congr 2 <;> ring

end ContinuousFlexibility.Radial
