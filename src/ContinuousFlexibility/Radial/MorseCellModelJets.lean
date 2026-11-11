import ContinuousFlexibility.Radial.MorseCellJoinCollars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fixed-order derivatives on the actual Morse model

The model derivative bounds follow from the true second-order radius
equation. They are uniform over the Morse parameters, after factoring
out the indicated powers of the small parameter when converting to
ordinary physical-radius derivatives.
-/

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped BigOperators ContDiff Topology

private theorem iteratedDeriv_morseRho_expansion (A B : ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (morseRho A B) x =
      A * ((-1 : ℝ) ^ k * exp (-x) - (-2 : ℝ) ^ k * exp (-2 * x)) -
        (if k = 0 then B else 0) := by
  have h₁ : ContDiff ℝ k (fun t : ℝ => exp (-t)) := contDiff_exp.comp contDiff_id.neg
  have h₂ : ContDiff ℝ k (fun t : ℝ => exp (-2 * t)) :=
    contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have h₃ : ContDiff ℝ k (fun t : ℝ => A * (exp (-t) - exp (-2 * t))) :=
    contDiff_const.mul (h₁.sub h₂)
  have he₁ : (fun t : ℝ => exp (-t)) = (fun t : ℝ => exp ((-1 : ℝ) * t)) := by
    funext t
    simp
  unfold morseRho
  rw [iteratedDeriv_fun_sub h₃.contDiffAt
    (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ => B) x),
    iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub h₁.contDiffAt h₂.contDiffAt,
    he₁, iteratedDeriv_exp_const_mul, iteratedDeriv_exp_const_mul, iteratedDeriv_const]
  simp only [neg_one_mul]

/-- The actual coefficient and all its fixed model derivatives have size A
throughout any retained model interval and its fixed left and right collars. -/
theorem morseRho_iteratedDeriv_abs_le {A B x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) (hx : exp (-x) ≤ 3) (k : ℕ) :
    |iteratedDeriv k (morseRho A B) x| ≤ (4 + 9 * (2 : ℝ) ^ k) * A := by
  have htwo : exp (-2 * x) = exp (-x) ^ 2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hx₂ : exp (-2 * x) ≤ 9 := by
    rw [htwo]
    have h := pow_le_pow_left₀ (exp_pos (-x)).le hx 2
    norm_num at h
    exact h
  have h₁ : |(-1 : ℝ) ^ k * exp (-x)| ≤ 3 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (exp_pos (-x))]
      using hx
  have h₂ : |(-2 : ℝ) ^ k * exp (-2 * x)| ≤ (2 : ℝ) ^ k * 9 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos (exp_pos (-2 * x))] using
        mul_le_mul_of_nonneg_left hx₂ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
  have h₀ : |(if k = 0 then B else 0)| ≤ A := by
    split <;> simp_all only [abs_of_nonneg hB, abs_zero]
  rw [iteratedDeriv_morseRho_expansion]
  calc
    _ ≤ |A * ((-1 : ℝ) ^ k * exp (-x) - (-2 : ℝ) ^ k * exp (-2 * x))| +
        |(if k = 0 then B else 0)| := abs_sub _ _
    _ ≤ A * (3 + (2 : ℝ) ^ k * 9) + A := by
      rw [abs_mul, abs_of_nonneg hA]
      exact add_le_add (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h₁ h₂)) hA) h₀
    _ = _ := by ring

private theorem morseRadius_iteratedDeriv_ode {A B a b x : ℝ} {r : ℝ → ℝ}
    (hab : a < b) (hr : ContDiff ℝ ∞ r) (hx : x ∈ Icc a b)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y)
    (k : ℕ) :
    iteratedDeriv (k + 2) r x = iteratedDeriv k (-(morseRho A B) * r) x := by
  have hv := (contDiff_infty_iff_deriv.mp hr).2
  have hrr := (contDiff_infty_iff_deriv.mp hv).2
  have hP : ContDiff ℝ ∞ (-(morseRho A B) * r) := (contDiff_morseRho A B).neg.mul hr
  have he : EqOn (deriv (deriv r)) (-(morseRho A B) * r) (Icc a b) := hEq
  have hE := iteratedDerivWithin_congr (n := k) he hx
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (hrr.contDiffAt.of_le (by simp)) hx,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (hP.contDiffAt.of_le (by simp)) hx] at hE
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  exact hE

private def UniformMorseRadiusJet (k : ℕ) (C : ℝ) : Prop :=
  ∀ {A B a b : ℝ} {r : ℝ → ℝ}, 0 ≤ A → A ≤ 1 → 0 ≤ B → B ≤ A →
    a < b → ContDiff ℝ ∞ r →
    (∀ x ∈ Icc a b, exp (-x) ≤ 3) →
    (∀ x ∈ Icc a b, |r x| ≤ 2 ∧ |deriv r x| ≤ 8) →
    (∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x) →
    ∀ x ∈ Icc a b, |iteratedDeriv k r x| ≤ C

/-- All fixed-order model-coordinate derivatives of the actual radius are
uniformly bounded. The constants precede the choice of cell and solution. -/
theorem exists_morseRadius_modelJet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A B a b : ℝ} {r : ℝ → ℝ}, 0 ≤ A → A ≤ 1 → 0 ≤ B → B ≤ A →
        a < b → ContDiff ℝ ∞ r →
        (∀ x ∈ Icc a b, exp (-x) ≤ 3) →
        (∀ x ∈ Icc a b, |r x| ≤ 2 ∧ |deriv r x| ≤ 8) →
        (∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x) →
        ∀ x ∈ Icc a b, |iteratedDeriv k r x| ≤ C := by
  change ∃ C : ℝ, 0 ≤ C ∧ UniformMorseRadiusJet k C
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · refine ⟨2, by norm_num, ?_⟩
      intro A B a b r hA hA₁ hB hBA hab hr hexp hru hEq x hx
      simpa only [iteratedDeriv_zero] using (hru x hx).1
    rcases k with _ | k
    · refine ⟨8, by norm_num, ?_⟩
      intro A B a b r hA hA₁ hB hBA hab hr hexp hru hEq x hx
      change |iteratedDeriv 1 r x| ≤ 8
      simpa only [iteratedDeriv_one] using (hru x hx).2
    have hPrev (i : Fin (k + 1)) : ∃ C : ℝ, 0 ≤ C ∧ UniformMorseRadiusJet (k - i.val) C :=
      ih (k - i.val) (by omega)
    choose C hC hCb using hPrev
    let term (i : Fin (k + 1)) : ℝ := (k.choose i.val : ℝ) * (4 + 9 * (2 : ℝ) ^ i.val) * C i
    have hterm (i : Fin (k + 1)) : 0 ≤ term i := by
      dsimp only [term]
      have := hC i
      positivity
    refine ⟨∑ i : Fin (k + 1), term i, Finset.sum_nonneg (fun i _ => hterm i), ?_⟩
    intro A B a b r hA hA₁ hB hBA hab hr hexp hru hEq x hx
    change |iteratedDeriv (k + 2) r x| ≤ _
    rw [morseRadius_iteratedDeriv_ode hab hr hx hEq]
    have hρ : ContDiff ℝ ∞ (-(morseRho A B)) := (contDiff_morseRho A B).neg
    rw [iteratedDeriv_mul (f := -(morseRho A B)) (g := r)
      (hρ.contDiffAt.of_le (by simp)) (hr.contDiffAt.of_le (by simp)),
      ← Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ i : Fin (k + 1),
          |(k.choose i.val : ℝ) * iteratedDeriv i.val (-(morseRho A B)) x *
            iteratedDeriv (k - i.val) r x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        dsimp only [term]
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), iteratedDeriv_neg, abs_neg]
        have hρi : |iteratedDeriv i.val (morseRho A B) x| ≤ 4 + 9 * (2 : ℝ) ^ i.val := calc
          _ ≤ (4 + 9 * (2 : ℝ) ^ i.val) * A :=
            morseRho_iteratedDeriv_abs_le hA hB hBA (hexp x hx) i.val
          _ ≤ (4 + 9 * (2 : ℝ) ^ i.val) * 1 :=
            mul_le_mul_of_nonneg_left hA₁ (by positivity)
          _ = _ := mul_one _
        exact mul_le_mul (mul_le_mul_of_nonneg_left hρi (Nat.cast_nonneg _))
          (hCb i hA hA₁ hB hBA hab hr hexp hru hEq x hx)
          (abs_nonneg _) (by positivity)

/-- The uniform constants apply to one true enlarged Morse solution, with
strictly positive speed and the same normalizing data at the right root. -/
theorem exists_morseRadius_with_modelJets :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ {A B : ℝ}, 0 < B → 4 * B < A → A ≤ 1 / 1000 →
        A ^ 9 / (9 : ℝ) ^ 9 ≤ B → B ≤ A ^ 9 →
        let a := morseCellLeftCut - morseJoinCollarWidth
        let b := morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth
        ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r (morseRightTurn A B) = 1 ∧
          deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 ∧
          (∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x) ∧
          (∀ x ∈ Icc a b, exp (-x) ≤ 3 ∧ |r x| ≤ 2 ∧
            A ^ 5 / 200 ≤ deriv r x ∧ |deriv r x| ≤ 8) ∧
          ∀ k x, x ∈ Icc a b → |iteratedDeriv k r x| ≤ C k := by
  choose C hC hBound using exists_morseRadius_modelJet_bound
  refine ⟨C, hC, ?_⟩
  intro A B hB hAB hA₀ hBAlo hBAhi
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  let h := morseJoinCollarWidth
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA₁ : A ≤ 1 := hA₀.trans (by norm_num)
  have hBA : B ≤ A := by linarith only [hB, hAB]
  have hA₅ : A ^ 5 ≤ A := calc
    _ = A * A ^ 4 := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [one_pow] using pow_le_pow_left₀ hA.le hA₁ 4) hA.le
    _ = _ := mul_one _
  have hA₅₀ : 0 ≤ A ^ 5 := pow_nonneg hA.le _
  have hh : 0 < h := by norm_num [h, morseJoinCollarWidth]
  have hab : a < b := morseCellLeftCut_lt_rightTurn hB hAB
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hWide : a - h < e + h := by linarith only [hab, hbe, hh]
  obtain ⟨r, hr, hr₀, hv₀, hEq, hL, hR, hLc, hRc, hvPos, _, _, _⟩ :=
    exists_morseRadius_with_joinCollars hB hAB hA₀ hBAlo hBAhi
  have hexp (x : ℝ) (hx : x ∈ Icc (a - h) (e + h)) : exp (-x) ≤ 3 := by
    have hlog : h ≤ log 2 := calc
      _ ≤ 1 - (2 : ℝ)⁻¹ := by norm_num [h, morseJoinCollarWidth]
      _ ≤ _ := one_sub_inv_le_log_of_pos (by norm_num)
    calc
      _ ≤ exp (-a + log 2) := exp_le_exp.mpr (by linarith only [hlog, hx.1])
      _ = _ := by
        rw [exp_add, exp_neg_morseCellLeftCut, exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hbnd (x : ℝ) (hx : x ∈ Icc (a - h) (e + h)) :
      |r x| ≤ 2 ∧ A ^ 5 / 200 ≤ deriv r x ∧ |deriv r x| ≤ 8 := by
    rw [abs_of_pos (hvPos x hx)]
    by_cases hxa : x ≤ a
    · obtain ⟨hrlo, hrhi, hvlo, hvhi, _, _⟩ := hLc x ⟨hx.1, hxa⟩
      have hrp : 0 ≤ r x := by linarith only [hrlo]
      exact ⟨by rwa [abs_of_nonneg hrp],
        by linarith only [hvlo, hA₅, hA], by linarith only [hvhi, hA₁]⟩
    · have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
      by_cases hxb : x ≤ b
      · obtain ⟨_, hrp, hrhi, hvlo, hvhi⟩ := hL x ⟨hax, hxb⟩
        exact ⟨by rwa [abs_of_pos hrp], by linarith only [hvlo, hA₅₀],
          by linarith only [hvhi, hA₁]⟩
      · have hbx : b ≤ x := le_of_lt (lt_of_not_ge hxb)
        by_cases hxe : x ≤ e
        · obtain ⟨_, hrp, hrhi, hvlo, hvhi⟩ := hR x ⟨hbx, hxe⟩
          exact ⟨by rwa [abs_of_pos hrp], by linarith only [hvlo, hA₅₀],
            by linarith only [hvhi, hA₅, hA₁]⟩
        · obtain ⟨hrlo, hrhi, hvlo, hvhi, _, _⟩ := hRc x ⟨le_of_lt (lt_of_not_ge hxe), hx.2⟩
          have hrp : 0 ≤ r x := by linarith only [hrlo]
          exact ⟨by rwa [abs_of_nonneg hrp], hvlo, by linarith only [hvhi, hA₅, hA₁]⟩
  refine ⟨r, hr, hr₀, hv₀, hEq, fun x hx => ⟨hexp x hx, hbnd x hx⟩, ?_⟩
  intro k x hx
  exact hBound k hA.le hA₁ hB.le hBA hWide hr hexp
    (fun y hy => ⟨(hbnd y hy).1, (hbnd y hy).2.2⟩) hEq x hx

end ContinuousFlexibility.Radial
