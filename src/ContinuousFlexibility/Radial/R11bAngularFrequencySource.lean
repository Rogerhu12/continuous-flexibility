module

public import ContinuousFlexibility.Radial.R11bFiniteSourceScalar
public import ContinuousFlexibility.Radial.R11bFiniteSourceModes
public import ContinuousFlexibility.Radial.R11bAngularDerivativeModes
public import ContinuousFlexibility.Radial.R11bGlobalL2

/-!
# Actual compatible sources for finite angular frequency estimates

The field is synthesized from negative sine coefficients of the supplied
weak angular derivative. The critical scalar row is scaled by two exactly
when the frequency-two channel is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

def r11bAngularFrequencySource (J : Finset ℕ) (F : RadialSource)
    (d : PolarPoint → ℝ) : RadialSource :=
  (r11bSineCosineSource J d, if 1 ∈ J then 2 * F.2 else 0)

theorem r11b_sourceNormSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (F : RadialSource) : 0 ≤ sourceNormSquare D γ M F := by
  change 0 ≤ F.2 ^ 2 + ∑' m, sourceCellSquare D γ M F.1 m
  exact add_nonneg (sq_nonneg _) (tsum_nonneg fun m =>
    mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab m F.1))

theorem r11b_source_scalar_sq_le_norm {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (F : RadialSource) : F.2 ^ 2 ≤ sourceNormSquare D γ M F := by
  change F.2 ^ 2 ≤ F.2 ^ 2 + ∑' m, sourceCellSquare D γ M F.1 m
  exact le_add_of_nonneg_right (tsum_nonneg fun m =>
    mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab m F.1))

theorem r11b_angularFrequencySource_member_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n)
    (F : RadialSource) {γ M : ℝ} {d : PolarPoint → ℝ}
    (hd : SourceDerivativeMember D γ M d) :
    SourceMember D γ M (r11bAngularFrequencySource J F d) ∧
      sourceNormSquare D γ M (r11bAngularFrequencySource J F d) ≤
        4 * (sourceNormSquare D γ M F + sourceNormSquare D γ M (d, 0)) := by
  let c : ℝ := if 1 ∈ J then 2 * F.2 else 0
  obtain ⟨hm, hb⟩ := r11b_sineCosineSource_member_scalar hab J hJ hd c
  have hc : c ^ 2 ≤ 4 * F.2 ^ 2 := by
    dsimp only [c]
    split_ifs <;> nlinarith only [sq_nonneg F.2]
  have hscalar := r11b_source_scalar_sq_le_norm hab γ M F
  have hd0 := r11b_sourceNormSquare_nonneg hab γ M (d, 0)
  refine ⟨hm, ?_⟩
  change sourceNormSquare D γ M (r11bSineCosineSource J d, c) ≤ _
  nlinarith only [hb, hc, hscalar, hd0]

theorem r11b_angularFrequencySource_referenceMode {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : RadialSource} {d : PolarPoint → ℝ}
    (hF : SourceMember D γ M F) (hder : WeakAngularDerivative D F.1 d)
    (hd : SourceDerivativeMember D γ M d)
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) (n : ℕ) (hn : n ∈ J) :
    referenceMode (r11bAngularFrequencySource J F d).1 (2 * n)
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => ((2 * n : ℕ) : ℝ) * referenceMode F.1 (2 * n) r) := by
  have hpos : 0 < 2 * n := Nat.mul_pos (by decide) (hJ n hn)
  have h := r11b_weakAngular_referenceMode_ae hD.choose_spec.1.2.1.le
    (r11b_source_memLp hD hγ hF) (r11b_sourceDerivative_memLp hD hγ hd)
    hder (2 * n) hpos
  filter_upwards [h] with r hr
  change ((2 * n : ℕ) : ℝ) * referenceMode F.1 (2 * n) r =
    -referenceSineMode d (2 * n) r at hr
  change referenceMode (r11bSineCosineSource J d) (2 * n) r =
    ((2 * n : ℕ) : ℝ) * referenceMode F.1 (2 * n) r
  rw [r11bSineCosineSource_referenceMode J hJ d n hn r]
  have hsine : referenceSineMode d (2 * n) r =
      angularPairing (fun θ => d (r, θ)) (sineMode (2 * n)) := by
    simp only [referenceSineMode, radialAngularMean, angularPairing, angularAverage, one_div]
  rw [hsine] at hr
  exact hr.symm

theorem r11b_angularFrequencySource_row
    (J : Finset ℕ) (F : RadialSource) (d : PolarPoint → ℝ)
    (n : ℕ) (hn : n ∈ J) (hj : 2 * n = 2) :
    (r11bAngularFrequencySource J F d).2 = ((2 * n : ℕ) : ℝ) * F.2 := by
  have hn1 : n = 1 := by omega
  have h1 : 1 ∈ J := by simpa only [hn1] using hn
  simp only [r11bAngularFrequencySource, if_pos h1, hj, Nat.cast_ofNat]

end ContinuousFlexibility.Radial
