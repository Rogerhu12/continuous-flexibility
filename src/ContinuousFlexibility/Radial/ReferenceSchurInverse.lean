module

public import ContinuousFlexibility.Radial.ReferencePositiveSchurAssembly
public import ContinuousFlexibility.Radial.ReferenceZeroModeAssembly
public import ContinuousFlexibility.Radial.ReferenceInverseCompletion
public import ContinuousFlexibility.Radial.ReferenceCommonInverse

/-!
# One actual reference inverse from uniform raw Schur bounds

The actual positive-mode inverses supply the nonzero Fourier channels;
the integral primitive supplies the zero channel. Maximal-graph
uniqueness identifies the assembled solution and forces linearity.
Choosing the lowest attenuation then gives one function valid at all
three exponents on the same reference data and with the same losses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Radial

theorem exists_referenceSchur_common_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (hG : ∀ n : ℕ, ModeInverseProperties D (2 * (n + 1)) (G n))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ Mmin : ℝ, 0 < Mmin ∧
      ∀ M₀ M₁ : ℝ, Mmin ≤ M₀ → 0 ≤ M₁ →
      (∀ γ : ℝ,
        γ = referenceBeta - 1 / 8 ∨ γ = referenceBeta ∨ γ = referenceBeta + 1 / 8 →
        ∃ K : ℕ → ℕ → ℕ → ℝ,
          (∀ n k m, 0 ≤ K n k m) ∧
          (∀ n k, Summable (K n k) ∧ ∑' m, K n k m ≤ A) ∧
          (∀ n m, Summable (fun k => K n k m) ∧ ∑' k, K n k m ≤ B) ∧
          (∀ n k m,
            matchedPhysicalChannelWeight D γ (-M₁) k *
                matchedPhysicalRawKernel D hD hD.choose_spec.2.1
                  (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
              K n k m * matchedPhysicalChannelWeight D γ M₀ m)) →
      ∃ H : RadialSource → RadialUnknown, ∀ γ : ℝ,
        γ = referenceBeta - 1 / 8 ∨ γ = referenceBeta ∨ γ = referenceBeta + 1 / 8 →
        ReferenceInverseProperties D γ M₀ M₁ H := by
  have hmode : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j H := by
    intro j hj he
    obtain ⟨k, hk⟩ := he
    have hkpos : 0 < k := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    have hjn : j = 2 * (n + 1) := by omega
    rw [hjn]
    exact ⟨G n, hG n⟩
  obtain ⟨Ms, Cs, hMs, _, hpositive⟩ :=
    exists_referencePositiveSchurAssembly hD hA hB
  obtain ⟨Mz, Kz, hMz, hKz, hzero⟩ := exists_referenceZeroMode_assembly hD hborder
  obtain ⟨Mu, _, hinverse⟩ := exists_referenceInverse_solvability_threshold hD hborder hmode
  let Mmin : ℝ := max Ms (max Mz Mu)
  have hMsMin : Ms ≤ Mmin := le_max_left _ _
  have hMzMin : Mz ≤ Mmin := (le_max_left _ _).trans (le_max_right _ _)
  have hMuMin : Mu ≤ Mmin := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Mmin, hMs.trans_le hMsMin, ?_⟩
  intro M₀ M₁ hM₀ hM₁ hraw
  apply exists_common_three_reference_inverse (matchingProfileGeometry hD).2.1.le
    (ε := (1 / 8 : ℝ)) (by norm_num)
  intro γ hγ
  have hγpos : 0 < γ := by
    rcases hγ with rfl | rfl | rfl <;> norm_num [referenceBeta]
  have hγband : γ ∈ Icc (0 : ℝ) 1 := by
    rcases hγ with rfl | rfl | rfl <;> norm_num [referenceBeta]
  obtain ⟨K, hK, hrow, hcol, hmajor⟩ := hraw γ hγ
  apply hinverse γ hγpos M₀ (hMuMin.trans hM₀) M₁
  let L : ℝ := max Kz (Cs ^ 2)
  let C : ℝ := 3 * L + 1
  have hL : 0 ≤ L := (sq_nonneg Cs).trans (le_max_right _ _)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hcost : 3 * L ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith only [hL, sq_nonneg (3 * L)]
  refine ⟨C, hC, ?_⟩
  intro F hF
  obtain ⟨u, ν, hubound, hrowF, hweak⟩ :=
    hpositive G γ M₀ M₁ K hG hγpos.le (hMsMin.trans hM₀)
      hK hrow hcol hmajor F hF
  obtain ⟨U, aL, hgraph, hreal, hnorm⟩ :=
    hzero M₀ M₁ γ (hMzMin.trans hM₀) hM₁ hγband F hF
      (Cs ^ 2) ν (sq_nonneg Cs) u hubound hrowF hweak
  refine ⟨U, aL, hgraph, hreal, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hcost
    (sourceNormSquare_nonneg (matchingProfileGeometry hD).2.1.le hF)

/-- Increasing the source coefficient exponent increases every physical
input-channel weight, including the unchanged scalar channel. -/
theorem matchedPhysicalChannelWeight_mono_coefficient (D : ReferenceData) (γ : ℝ)
    {M N : ℝ} (hMN : M ≤ N) (k : ℕ) :
    matchedPhysicalChannelWeight D γ M k ≤ matchedPhysicalChannelWeight D γ N k := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
      change Real.exp (M * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k)) ≤
        Real.exp (N * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k))
      exact Real.exp_le_exp.mpr
        (add_le_add (mul_le_mul_of_nonneg_right hMN (radialQ_nonneg _)) le_rfl)

/-- A raw kernel estimate at one source loss automatically supplies the
larger common source loss needed for Hilbert embedding, the zero mode,
and uniqueness. The output loss and the geometry stay fixed. -/
theorem referenceSchur_common_inverse_of_raw_bounds {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (hG : ∀ n : ℕ, ModeInverseProperties D (2 * (n + 1)) (G n))
    {A B Mraw M₁ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁)
    (hraw : ∀ γ : ℝ,
      γ = referenceBeta - 1 / 8 ∨ γ = referenceBeta ∨ γ = referenceBeta + 1 / 8 →
      ∃ K : ℕ → ℕ → ℕ → ℝ,
        (∀ n k m, 0 ≤ K n k m) ∧
        (∀ n k, Summable (K n k) ∧ ∑' m, K n k m ≤ A) ∧
        (∀ n m, Summable (fun k => K n k m) ∧ ∑' k, K n k m ≤ B) ∧
        (∀ n k m,
          matchedPhysicalChannelWeight D γ (-M₁) k *
              matchedPhysicalRawKernel D hD hD.choose_spec.2.1
                (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
            K n k m * matchedPhysicalChannelWeight D γ Mraw m)) :
    ∃ M₀ : ℝ, ∃ H : RadialSource → RadialUnknown, ∀ γ : ℝ,
      γ = referenceBeta - 1 / 8 ∨ γ = referenceBeta ∨ γ = referenceBeta + 1 / 8 →
      ReferenceInverseProperties D γ M₀ M₁ H := by
  obtain ⟨Mmin, _, hcommon⟩ := exists_referenceSchur_common_inverse hD hborder G hG hA hB
  let M₀ : ℝ := max Mmin Mraw
  refine ⟨M₀, hcommon M₀ M₁ (le_max_left _ _) hM₁ ?_⟩
  intro γ hγ
  obtain ⟨K, hK, hrow, hcol, hmajor⟩ := hraw γ hγ
  refine ⟨K, hK, hrow, hcol, ?_⟩
  intro n k m
  exact (hmajor n k m).trans
    (mul_le_mul_of_nonneg_left
      (matchedPhysicalChannelWeight_mono_coefficient D γ (le_max_right Mmin Mraw) m)
      (hK n k m))

end ContinuousFlexibility.Statements
