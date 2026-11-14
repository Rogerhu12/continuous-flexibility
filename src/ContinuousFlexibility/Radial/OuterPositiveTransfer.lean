module

public import ContinuousFlexibility.Radial.TransitionTransfer

/-!
# Positive transfer without a lower bound on the interval length

A small regularization of the two coefficient integrals gives a balanced
weight with a controlled condition number even when one integral tends
to zero.  This is needed on the physical joins, whose hypotheses impose
an upper width bound but no quantitative lower width bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory

/-- The balancing weight has polynomial conditioning and the same square-root
action as the unregularized optimum, up to a fixed additive constant. -/
theorem exists_regularized_positive_weight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ μ : ℝ, 0 < μ ∧ μ ^ 2 ≤ (1 + a + b) ^ 2 ∧
      1 ≤ (1 + a + b) ^ 2 * μ ^ 2 ∧
      a / μ + μ * b ≤ 2 * sqrt (a * b) + 2 := by
  let M := 1 + a + b
  let ε := 1 / M
  have hM : 0 < M := by dsimp only [M]; linarith only [ha, hb]
  have hM1 : 1 ≤ M := by dsimp only [M]; linarith only [ha, hb]
  have hε : 0 < ε := div_pos zero_lt_one hM
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hM1
  have hεM : ε * M = 1 := by dsimp only [ε]; exact div_mul_cancel₀ _ hM.ne'
  have hεsq : ε ^ 2 ≤ ε := by
    have h := mul_le_mul_of_nonneg_left hε1 hε.le
    nlinarith only [h]
  have haε : 0 < a + ε := add_pos_of_nonneg_of_pos ha hε
  have hbε : 0 < b + ε := add_pos_of_nonneg_of_pos hb hε
  let μ := sqrt ((a + ε) / (b + ε))
  obtain ⟨hμ, hbalance⟩ := optimal_weight_alg (a + ε) (b + ε) μ haε hbε rfl
  have hμsq : μ ^ 2 = (a + ε) / (b + ε) := sq_sqrt (div_pos haε hbε).le
  have haM : a + ε ≤ M := by dsimp only [M]; linarith only [hε1, hb]
  have hbM : b + ε ≤ M := by dsimp only [M]; linarith only [hε1, ha]
  have hεb : ε ≤ b + ε := le_add_of_nonneg_left hb
  have hεa : ε ≤ a + ε := le_add_of_nonneg_left ha
  have hMε : M ^ 2 * ε = M := by
    calc
      _ = M * (ε * M) := by ring
      _ = M := by rw [hεM, mul_one]
  have hupper : μ ^ 2 ≤ M ^ 2 := by
    rw [hμsq]
    calc
      _ ≤ M / (b + ε) := div_le_div_of_nonneg_right haM hbε.le
      _ ≤ M / ε := div_le_div_of_nonneg_left hM.le hε hεb
      _ = M ^ 2 := by dsimp only [ε]; field_simp [hM.ne']
  have hlower : 1 ≤ M ^ 2 * μ ^ 2 := by
    rw [hμsq, ← mul_div_assoc]
    apply (le_div_iff₀ hbε).mpr
    calc
      1 * (b + ε) = b + ε := one_mul _
      _ ≤ M := hbM
      _ = M ^ 2 * ε := hMε.symm
      _ ≤ M ^ 2 * (a + ε) := mul_le_mul_of_nonneg_left hεa (sq_nonneg M)
  have hproduct : (a + ε) * (b + ε) ≤ a * b + 1 := by
    dsimp only [M] at hεM
    nlinarith only [hεM, hεsq]
  have hroot : sqrt (a * b + 1) ≤ sqrt (a * b) + 1 := by
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    have h1 := sq_sqrt (show 0 ≤ a * b + 1 by linarith only [hab])
    have h0 := sq_sqrt hab
    nlinarith only [h1, h0, sqrt_nonneg (a * b), sqrt_nonneg (a * b + 1)]
  refine ⟨μ, hμ, hupper, hlower, ?_⟩
  calc
    a / μ + μ * b ≤ (a + ε) / μ + μ * (b + ε) :=
      add_le_add (div_le_div_of_nonneg_right (le_add_of_nonneg_right hε.le) hμ.le)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hε.le) hμ.le)
    _ = 2 * sqrt ((a + ε) * (b + ε)) := hbalance
    _ ≤ 2 * sqrt (a * b + 1) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hproduct) (by norm_num)
    _ ≤ 2 * (sqrt (a * b) + 1) := mul_le_mul_of_nonneg_left hroot (by norm_num)
    _ = _ := by ring

private theorem positive_energy_remove_weight {u₀ z₀ u₁ z₁ μ M H : ℝ}
    (hM : 1 ≤ M) (hμhi : μ ^ 2 ≤ M ^ 2) (hμlo : 1 ≤ M ^ 2 * μ ^ 2)
    (h : u₁ ^ 2 + μ ^ 2 * z₁ ^ 2 ≤ (u₀ ^ 2 + μ ^ 2 * z₀ ^ 2) * exp H) :
    u₁ ^ 2 + z₁ ^ 2 ≤ (u₀ ^ 2 + z₀ ^ 2) * M ^ 4 * exp H := by
  have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM, sq_nonneg (M - 1)]
  have hupper : u₀ ^ 2 + μ ^ 2 * z₀ ^ 2 ≤ M ^ 2 * (u₀ ^ 2 + z₀ ^ 2) := by
    have hu := mul_le_mul_of_nonneg_right hM2 (sq_nonneg u₀)
    have hz := mul_le_mul_of_nonneg_right hμhi (sq_nonneg z₀)
    nlinarith only [hu, hz]
  have hlower : u₁ ^ 2 + z₁ ^ 2 ≤ M ^ 2 * (u₁ ^ 2 + μ ^ 2 * z₁ ^ 2) := by
    have hu := mul_le_mul_of_nonneg_right hM2 (sq_nonneg u₁)
    have hz := mul_le_mul_of_nonneg_right hμlo (sq_nonneg z₁)
    nlinarith only [hu, hz]
  calc
    _ ≤ M ^ 2 * (u₁ ^ 2 + μ ^ 2 * z₁ ^ 2) := hlower
    _ ≤ M ^ 2 * ((u₀ ^ 2 + μ ^ 2 * z₀ ^ 2) * exp H) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg M)
    _ ≤ M ^ 2 * ((M ^ 2 * (u₀ ^ 2 + z₀ ^ 2)) * exp H) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hupper (exp_pos H).le) (sq_nonneg M)
    _ = _ := by ring

/-- Both endpoint directions have a polynomial prefactor and the balanced
action.  No positive lower bound on either coefficient integral is needed. -/
theorem transfer_positive_piece_regularized {u z α β : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hα : ContinuousOn α (Icc l r)) (hβ : ContinuousOn β (Icc l r))
    (hα₀ : ∀ x ∈ Icc l r, 0 ≤ α x) (hβ₀ : ∀ x ∈ Icc l r, 0 ≤ β x)
    (hd : ∀ x ∈ Icc l r,
      HasDerivAt u (α x * z x) x ∧ HasDerivAt z (β x * u x) x) :
    let a := ∫ x in l..r, α x
    let b := ∫ x in l..r, β x
    let K := (1 + a + b) ^ 4 * exp (2 * sqrt (a * b) + 2)
    (u r ^ 2 + z r ^ 2 ≤ (u l ^ 2 + z l ^ 2) * K) ∧
      (u l ^ 2 + z l ^ 2 ≤ (u r ^ 2 + z r ^ 2) * K) := by
  let a := ∫ x in l..r, α x
  let b := ∫ x in l..r, β x
  let M := 1 + a + b
  have ha : 0 ≤ a := intervalIntegral.integral_nonneg hlr hα₀
  have hb : 0 ≤ b := intervalIntegral.integral_nonneg hlr hβ₀
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [ha, hb]
  obtain ⟨μ, hμ, hμhi, hμlo, hbound⟩ := exists_regularized_positive_weight ha hb
  have hαi : IntervalIntegrable (fun x => α x / μ) volume l r :=
    (hα.div_const μ).intervalIntegrable_of_Icc hlr
  have hβi : IntervalIntegrable (fun x => μ * β x) volume l r :=
    (continuousOn_const.mul hβ).intervalIntegrable_of_Icc hlr
  have hI : (∫ x in l..r, α x / μ + μ * β x) = a / μ + μ * b := by
    rw [intervalIntegral.integral_add hαi hβi, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
  have hκ : 0 ≤ a / μ + μ * b := add_nonneg (div_nonneg ha hμ.le) (mul_nonneg hμ.le hb)
  have hforward := transfer_positive_piece hlr hμ hα hβ hα₀ hβ₀ hd
    (s := l) (t := r) ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩
  have hbackward := transfer_positive_piece hlr hμ hα hβ hα₀ hβ₀ hd
    (s := r) (t := l) ⟨hlr, le_rfl⟩ ⟨le_rfl, hlr⟩
  rw [hI, abs_of_nonneg hκ] at hforward
  rw [intervalIntegral.integral_symm l r, abs_neg, hI, abs_of_nonneg hκ] at hbackward
  have hforward' := positive_energy_remove_weight hM hμhi hμlo hforward
  have hbackward' := positive_energy_remove_weight hM hμhi hμlo hbackward
  constructor
  · calc
      _ ≤ (u l ^ 2 + z l ^ 2) * M ^ 4 * exp (a / μ + μ * b) := hforward'
      _ ≤ (u l ^ 2 + z l ^ 2) * M ^ 4 * exp (2 * sqrt (a * b) + 2) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hbound) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (u r ^ 2 + z r ^ 2) * M ^ 4 * exp (a / μ + μ * b) := hbackward'
      _ ≤ (u r ^ 2 + z r ^ 2) * M ^ 4 * exp (2 * sqrt (a * b) + 2) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hbound) (by positivity)
      _ = _ := by ring

end ContinuousFlexibility.Radial
