import ContinuousFlexibility.Radial.R11bFiniteTransfer

/-!
# Compatible finite sources from the angular derivative

Negative sine coefficients synthesize a positive even-frequency cosine
field. Its weighted cell norm contracts the derivative source norm. Its
angular mean is identically zero, so all original source conditions hold.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_angularPairing_neg_right (f g : ℝ → ℝ) :
    angularPairing f (fun θ => -g θ) = -angularPairing f g := by
  simp only [angularPairing, angularAverage, mul_neg, intervalIntegral.integral_neg]

theorem r11b_angularPairing_neg_neg (f g : ℝ → ℝ) :
    angularPairing (fun θ => -f θ) (fun θ => -g θ) = angularPairing f g := by
  simp only [angularPairing, neg_mul_neg]

theorem r11b_radialAngularMean_finite_even_cosine_sum
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) (c : ℕ → ℝ) :
    radialAngularMean (fun θ => ∑ n ∈ J, c n * cosineMode (2 * n) θ) = 0 := by
  have hc (n : ℕ) : Continuous (fun θ => c n * cosineMode (2 * n) θ) := by
    unfold cosineMode
    exact continuous_const.mul (continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  unfold radialAngularMean
  rw [intervalIntegral.integral_finsetSum (fun n _ => (hc n).intervalIntegrable _ _)]
  have hz : (∑ n ∈ J, ∫ θ in (0 : ℝ)..2 * Real.pi,
      c n * cosineMode (2 * n) θ) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [intervalIntegral.integral_const_mul,
      integral_cosineMode (2 * n) (Nat.mul_pos (by decide) (hJ n hn)), mul_zero]
  rw [hz, mul_zero]

def r11bSineCosineSource (J : Finset ℕ) (f : PolarPoint → ℝ) : PolarPoint → ℝ :=
  r11bFiniteTransfer J (fun n θ => -sineMode (2 * n) θ)
    (fun n => cosineMode (2 * n)) f

theorem r11bSineCosineSource_apply (J : Finset ℕ) (f : PolarPoint → ℝ)
    (x : PolarPoint) :
    r11bSineCosineSource J f x =
      ∑ n ∈ J, -angularPairing (fun θ => f (x.1, θ)) (sineMode (2 * n)) *
        cosineMode (2 * n) x.2 := by
  simp only [r11bSineCosineSource, r11bFiniteTransfer, r11b_angularPairing_neg_right]

theorem r11b_sineCosineSource_cell_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    RadialCellIntegrable D (r11bSineCosineSource J f) ∧
      ∀ m, referenceCellSquare D m (r11bSineCosineSource J f) ≤
        referenceCellSquare D m f := by
  have hsin (n : ℕ) :
      MemLp (fun θ => -sineMode (2 * n) θ) 2
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    MemLp.ae_eq (Filter.Eventually.of_forall fun θ => rfl)
      (sineMode_memLp_angularInterval (2 * n)).neg
  have hfreq (i j : ℕ) : (2 * i = 2 * j) ↔ i = j := by omega
  apply r11b_finiteTransfer_cell_bound hab J
    (fun n θ => -sineMode (2 * n) θ) (fun n => cosineMode (2 * n)) hf
    (fun n _ => hsin n) (fun n _ => cosineMode_memLp_angularInterval (2 * n))
  · intro i hi j hj
    rw [r11b_angularPairing_neg_neg]
    simpa only [hfreq] using angularPairing_sineMode (2 * i) (2 * j)
      (Nat.mul_pos (by decide) (hJ i hi)) (Nat.mul_pos (by decide) (hJ j hj))
  · intro i hi j hj
    simpa only [hfreq] using angularPairing_cosineMode (2 * i) (2 * j)
      (Nat.mul_pos (by decide) (hJ i hi)) (Nat.mul_pos (by decide) (hJ j hj))

theorem r11b_sineCosineSource_member {D : ReferenceData} (hab : D.a ≤ D.b)
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) {γ M : ℝ}
    {f : PolarPoint → ℝ} (hf : SourceDerivativeMember D γ M f) :
    SourceMember D γ M (r11bSineCosineSource J f, 0) ∧
      sourceNormSquare D γ M (r11bSineCosineSource J f, 0) ≤
        sourceNormSquare D γ M (f, 0) := by
  obtain ⟨hp, hcell⟩ := r11b_sineCosineSource_cell_bound hab J hJ hf.1
  have hnn (m : ℕ) : 0 ≤ sourceCellSquare D γ M (r11bSineCosineSource J f) m :=
    mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab m _)
  have hle (m : ℕ) :
      sourceCellSquare D γ M (r11bSineCosineSource J f) m ≤
        sourceCellSquare D γ M f m :=
    mul_le_mul_of_nonneg_left (hcell m) (exp_pos _).le
  have hs : Summable (sourceCellSquare D γ M (r11bSineCosineSource J f)) :=
    Summable.of_nonneg_of_le hnn hle hf.2
  have hper : Function.Periodic (r11bSineCosineSource J f) (0, Real.pi) := by
    rintro ⟨r, θ⟩
    change (∑ n ∈ J, angularPairing (fun φ => f (r + 0, φ))
      (fun φ => -sineMode (2 * n) φ) * cosineMode (2 * n) (θ + Real.pi)) =
        ∑ n ∈ J, angularPairing (fun φ => f (r, φ))
          (fun φ => -sineMode (2 * n) φ) * cosineMode (2 * n) θ
    simp only [add_zero]
    exact finite_even_cosine_sum_periodic J
      (fun n => angularPairing (fun φ => f (r, φ)) (fun φ => -sineMode (2 * n) φ)) θ
  have heven (r θ : ℝ) :
      r11bSineCosineSource J f (r, -θ) = r11bSineCosineSource J f (r, θ) :=
    finite_even_cosine_sum_even J
      (fun n => angularPairing (fun φ => f (r, φ)) (fun φ => -sineMode (2 * n) φ)) θ
  have hmean : (fun r => radialAngularMean
      (fun θ => r11bSineCosineSource J f (r, θ))) = fun _ => 0 := by
    funext r
    exact r11b_radialAngularMean_finite_even_cosine_sum J hJ
      (fun n => angularPairing (fun φ => f (r, φ)) (fun φ => -sineMode (2 * n) φ))
  refine ⟨⟨hp, hs, hper, heven, ?_, ?_⟩, ?_⟩
  · rw [hmean]
    exact intervalIntegrable_const
  · rw [hmean]
    simp
  · have hbound := Summable.tsum_le_tsum hle hs hf.2
    change 0 ^ 2 + (∑' m, sourceCellSquare D γ M (r11bSineCosineSource J f) m) ≤
      0 ^ 2 + ∑' m, sourceCellSquare D γ M f m
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hbound

end ContinuousFlexibility.Radial
