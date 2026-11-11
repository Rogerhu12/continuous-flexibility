import ContinuousFlexibility.Radial.MatchedOuterSelectedScale
import ContinuousFlexibility.Radial.MatchedOuterWholeModalBounds
import ContinuousFlexibility.Radial.MatchedOuterNaturalColumn

/-!
# Uniform whole-tail bounds at the actual selected matching scale

The original kernel and natural-column estimates are instantiated with
the actual j² w(p)/p normalization. Their constants precede the height
sequence, frequency, tail pair and supplied inverse. The only operator
input is its all-source Green identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem exists_matchedMorse_uniform_selected_whole_bounds
    {T : MorseChainData} {C : ℕ → ℝ}
    {family : (ℕ → ℝ) → ReferenceData} {Cstar η K : ℝ}
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization T σ (family σ) C ∧
        MorseMassResistanceBounds T σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    (hCstar : 0 < Cstar) (hη0 : 0 < η) (hη : η ≤ 1 / 16)
    (hK : 32 ≤ K) (minimum : ℕ) :
    ∃ C₁ A : ℝ, 0 < C₁ ∧ 0 < A ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ T.index + 3 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n →
      ∀ σ (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2),
      ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold T Cstar n →
      ∀ entry : ℝ, entry ∈ morseInitialMiddle T →
      ∀ right : Bool,
        let D := family σ
        let p := r07PreviousCellJoin T right (n - 1)
        let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
        let μ := outerWholeMeasure D right (morseTransitionPhysicalEntry T entry right n)
        let hP := (hfamily σ hσ).1.accumulating.2.1
        ∀ (F : MorsePhysicalTailBasis T D right j (n + 1)
            (morseOuterDeepEntrance T right n) η K)
          (H : OuterFundamentalStatePair
            (fun x => lam / outerTailOutwardWeight D right x)
            (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
            F.P (F.ZP lam) F.Q (F.ZQ lam)
            (morseTransitionOutwardLeft T entry right n)
            (morseTransitionOutwardRight T entry right n)
            (outerOutwardRadius right (tailPhysicalEndpoint D right))),
        ∀ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
          (∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
            fun x => ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂μ) →
        ∀ U : Lp ℝ 2 μ, (U : ℝ → ℝ) =ᵐ[μ] fun x => H.V x / sqrt lam →
        ∀ k m : ℕ,
          ‖(matchedOuterCell D hP right μ k).comp
            (R.comp (matchedOuterCell D hP right μ m))‖ ≤
              C₁ * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
                |radialS (D.cellIndex k) - radialS (D.cellIndex m)|) ∧
          ‖matchedOuterCell D hP right μ m U‖ ≤
            C₁ * exp (A * (radialQ (D.cellIndex m) + radialQ n) -
              |radialS (D.cellIndex m) - radialS n|) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have h₀ := (hfamily σ₀ (fun _ => ⟨le_rfl, by norm_num [σ₀]⟩)).1
  let L := matchedOuterSelectedScaleExponent Cstar (C 0) (family σ₀).a (family σ₀).b
  have hL : 0 ≤ L := (matchedOuterSelectedScaleExponent_pos (h₀.constants_pos 0)
    h₀.geometry.1 (h₀.geometry.1.trans h₀.geometry.2.1)).le
  obtain ⟨Ck, Ak, hCk, hAk, Nk, hNmin, hNidx, hkernel⟩ :=
    exists_matchedMorse_uniform_actual_whole_modal_bounds hfamily hends
      hCstar hη0 hη hK hL minimum
  obtain ⟨Cn, An, hCn, hAn, Nn, _, _, hnatural⟩ :=
    exists_matchedMorse_uniform_actual_natural_column_bound hfamily hends
      hCstar hη0 hη hK hL minimum
  let C₁ := Ck + Cn + 1
  let A := Ak + An + 1
  let N₀ := max (max Nk Nn) 2
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCkC : Ck ≤ C₁ := by dsimp only [C₁]; linarith only [hCn]
  have hCnC : Cn ≤ C₁ := by dsimp only [C₁]; linarith only [hCk]
  have hAkA : Ak ≤ A := by dsimp only [A]; linarith only [hAn]
  have hAnA : An ≤ A := by dsimp only [A]; linarith only [hAk]
  refine ⟨C₁, A, hC₁, hA, N₀, by dsimp only [N₀]; omega,
    by dsimp only [N₀]; omega, ?_⟩
  intro n hn σ hσ j hj hupper entry he right
  dsimp only
  intro F H R hR U hU k m
  have hkn : Nk ≤ n := by dsimp only [N₀] at hn; omega
  have hnn : Nn ≤ n := by dsimp only [N₀] at hn; omega
  have hn₂ : 2 ≤ n := by dsimp only [N₀] at hn; omega
  have hstrict : T.index < n := by omega
  let p := r07PreviousCellJoin T right (n - 1)
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) ((family σ).w p) p
  have hscale : 0 < lam ∧
      lam / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2) ∧
      morseChainAmplitude T σ n / lam ≤ exp (L * (n : ℝ) ^ 2) := by
    have hs := matchedMorse_selected_boundaryScale_bounds (hfamily σ hσ).1 hσ
      right hstrict hn₂ hj hupper
    simpa only [L, lam, p, (hends σ σ₀).1, (hends σ σ₀).2] using hs
  have hk := (hkernel n hkn σ hσ j hj hupper entry he right lam
    hscale.1 hscale.2.1 hscale.2.2 F H).2 R hR k m
  have hu := hnatural n hnn σ hσ j hj hupper entry he right lam
    hscale.1 hscale.2.1 hscale.2.2 F H U hU m
  constructor
  · exact hk.trans (mul_le_mul hCkC
      (exp_le_exp.mpr (sub_le_sub_right
        (mul_le_mul_of_nonneg_right hAkA
          (add_nonneg (radialQ_nonneg _) (radialQ_nonneg _))) _))
      (exp_pos _).le hC₁.le)
  · exact hu.trans (mul_le_mul hCnC
      (exp_le_exp.mpr (sub_le_sub_right
        (mul_le_mul_of_nonneg_right hAnA
          (add_nonneg (radialQ_nonneg _) (radialQ_nonneg _))) _))
      (exp_pos _).le hC₁.le)

end ContinuousFlexibility.Radial
