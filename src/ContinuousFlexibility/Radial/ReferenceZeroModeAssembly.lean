import ContinuousFlexibility.Radial.ReferenceModeAssembly
import ContinuousFlexibility.Radial.ZeroModeWeightedSolution

/-!
# Supplying the zero channel in the full weighted assembly

The mean-zero condition in SourceMember is used directly by the actual
two-primitive zero-mode solution. Its coefficient threshold and energy
constant are chosen before all three attenuation exponents and before
the source. Only the positive-mode construction remains to be supplied.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

theorem exists_referenceZeroMode_assembly {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) :
    ∃ Mstar Kzero : ℝ, 0 < Mstar ∧ 0 < Kzero ∧
      ∀ M₀ M₁ γ : ℝ, Mstar ≤ M₀ → 0 ≤ M₁ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ F : RadialSource, ∀ hF : SourceMember D γ M₀ F,
      ∀ K ν : ℝ, 0 ≤ K →
      ∀ u : ℕ → Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁)),
      (∀ n : ℕ, ‖u n‖ ^ 2 + (if n = 0 then ν ^ 2 else 0) ≤
        K * (‖referenceSourceCosineAnalysis
          (Radial.matchingProfileGeometry hD).2.1.le hD.choose_spec.2.1 hF (n + 1)‖ ^ 2 +
          if n = 0 then F.2 ^ 2 else 0)) →
      ((∫ r in D.a..D.b, referenceColumn D r * u 0 r) = F.2) →
      (∀ (n : ℕ) (φ : ℝ → ℝ),
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u n r *
          Radial.radialJacobi (((2 * (n + 1) : ℕ) : ℝ) ^ 2) D.w φ r) +
          (if n = 0 then ν else 0) *
            (∫ r in D.a..D.b, referenceColumn D r * φ r) =
        ∫ r in D.a..D.b, referenceCosineCoefficient F.1 (n + 1) r * φ r) →
      ∃ U : RadialUnknown, ∃ aL : ℝ,
        ReferenceGraph D γ M₀ M₁ U F ∧ OutputRealization D γ M₁ aL U ∧
          outputNormSquare D γ M₁ aL U ≤
            (3 * max Kzero K) * sourceNormSquare D γ M₀ F := by
  obtain ⟨Mstar, Kzero, hMstar, hKzero, hzero⟩ :=
    Radial.zeroMode_weighted_solution hD hB
  refine ⟨Mstar, Kzero, hMstar, hKzero, ?_⟩
  intro M₀ M₁ γ hM₀ hM₁ hγ F hF K ν hK u hubound hrow hpositive
  have hab : D.a ≤ D.b := (Radial.matchingProfileGeometry hD).2.1.le
  have hP : RadialPartition D := hD.choose_spec.2.1
  let f : ℝ → ℝ := referenceCosineCoefficient F.1 0
  have hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M₀) :=
    hF.cosineCoefficient_memLp hab hP 0
  have hfi : IntervalIntegrable f volume D.a D.b := by
    dsimp only [f]
    rw [referenceCosineCoefficient_zero_eq_mean]
    exact hF.2.2.2.2.1
  have hmean : (∫ r in D.a..D.b, f r) = 0 := by
    dsimp only [f]
    rw [referenceCosineCoefficient_zero_eq_mean]
    exact hF.2.2.2.2.2
  obtain ⟨_, hz, hzbound, _, _, hzeq⟩ :=
    hzero M₀ M₁ γ hM₀ hM₁ hγ f hf hfi hmean
  let z : ℝ → ℝ := Radial.zeroModeHeight D.a D.b D.w f
  let aL : ℝ := z D.a
  have he : (∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) =
      ‖referenceSourceCosineAnalysis hab hP hF 0‖ ^ 2 :=
    (referenceSourceCosineAnalysis_energy hab hP hF 0).symm
  have hzbound' : aL ^ 2 +
      (∫ r, (z r - aL * D.chiLeft r) ^ 2
        ∂referenceRadialWeightedMeasure D γ (-M₁)) ≤
      max Kzero K * ‖referenceSourceCosineAnalysis hab hP hF 0‖ ^ 2 := by
    calc
      _ ≤ Kzero * (∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) := hzbound
      _ = Kzero * ‖referenceSourceCosineAnalysis hab hP hF 0‖ ^ 2 := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hubound' (n : ℕ) : ‖u n‖ ^ 2 + (if n = 0 then ν ^ 2 else 0) ≤
      max Kzero K * (‖referenceSourceCosineAnalysis hab hP hF (n + 1)‖ ^ 2 +
        if n = 0 then F.2 ^ 2 else 0) := by
    apply (hubound n).trans
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    exact add_nonneg (sq_nonneg _) (by split_ifs <;> positivity)
  have hzweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
      (∫ r in D.a..D.b, z r * Radial.radialJacobi 0 D.w φ r) =
        ∫ r in D.a..D.b, referenceCosineCoefficient F.1 0 r * φ r := by
    intro φ hφ _ hsφ
    exact hzeq φ hφ hsφ
  obtain ⟨U, hG, hreal, hnorm⟩ :=
    referenceSolution_of_radial_modes hD hB hF
      (hKzero.le.trans (le_max_left _ _)) z hz u hzbound' hubound' hrow hzweak hpositive
  exact ⟨U, aL, hG, hreal, hnorm⟩

end ContinuousFlexibility.Statements
