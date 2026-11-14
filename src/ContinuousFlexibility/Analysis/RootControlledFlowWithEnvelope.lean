import ContinuousFlexibility.Analysis.RootControlledFlow
import ContinuousFlexibility.Analysis.RootFieldLocalization

/-!
# Controlled root flows retaining the material envelope

The raw coefficient constants precede the material weight and the root.
A displayed radius keeps the angular exponent equal to one. Its inverse
costs only the inverse input radius and a fixed power of that same weight.
The actual periodic flow and its entire displacement jet tower are then
supplied by the existing Picard and flow-jet theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The first angular derivative bound is numerical after restricting
one fixed low state seminorm. -/
def rootPolynomialControlRadius (ρ M : ℝ) : ℝ :=
  min ρ (min 1 (1 / (4 * (M + 1))))

theorem rootPolynomialControlRadius_bounds {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M) :
    let δ := rootPolynomialControlRadius ρ M
    0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧ 4 * δ * M ≤ 1 ∧
      δ⁻¹ ≤ ρ⁻¹ + 1 + 4 * (M + 1) := by
  let δ := rootPolynomialControlRadius ρ M
  have hden : 0 < 4 * (M + 1) := by positivity
  have hδ : 0 < δ := lt_min hρ (lt_min zero_lt_one (div_pos zero_lt_one hden))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδone : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδbound : δ ≤ 1 / (4 * (M + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 4 * δ * M ≤ 1 := by
    have h := (le_div_iff₀ hden).mp hδbound
    nlinarith only [h, hδ.le]
  refine ⟨hδ, hδρ, hδone, hsmall, ?_⟩
  change δ⁻¹ ≤ ρ⁻¹ + 1 + 4 * (M + 1)
  have hρinv : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ.le
  by_cases hr : ρ ≤ min 1 (1 / (4 * (M + 1)))
  · have he : δ = ρ := min_eq_left hr
    rw [he]
    linarith only [hden]
  · have he : δ = min 1 (1 / (4 * (M + 1))) := min_eq_right (le_of_not_ge hr)
    rw [he]
    by_cases h1 : 1 ≤ 1 / (4 * (M + 1))
    · rw [min_eq_left h1, inv_one]
      linarith only [hρinv, hden]
    · rw [min_eq_right (le_of_not_ge h1), one_div, inv_inv]
      linarith only [hρinv]

/-- One fixed low order and one loss give polynomially weighted actual
root flows. The collar is selected before every member of the state
family; all output jet constants precede the material weight. -/
theorem exists_rootRescaledFlow_material_family
    (hFlow : N04FlowJetsTarget)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ,
      ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ W : ℝ, 1 ≤ W → ∀ ρ : ℝ, 0 < ρ →
      ∀ (ι : Type) (V : Set ι) (w : ι → E) (d c : ι → PolarPoint → ℝ),
        (∀ i ∈ V, ContDiff ℝ ∞ (d i) ∧ ContDiff ℝ ∞ (c i)) →
        (∀ i ∈ V,
          (∀ r, Function.Periodic (fun θ => d i (r, θ)) Real.pi) ∧
          (∀ r, Function.Periodic (fun θ => c i (r, θ)) Real.pi)) →
        (∀ i ∈ V, p low (w i) ≤ 1) →
        (∀ i ∈ V, ∀ n r, |r| ≤ ρ → ∀ θ,
          ‖iteratedFDeriv ℝ n (d i) (r, θ)‖ ≤
            A n * W ^ (A n) * (1 + p (n + inputLoss) (w i))) →
        (∀ i ∈ V, ∀ n r, |r| ≤ ρ → ∀ θ,
          ‖iteratedFDeriv ℝ n (c i) (r, θ)‖ ≤
            A n * W ^ (A n) * (1 + p (n + inputLoss) (w i))) →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
          δ⁻¹ ≤ ρ⁻¹ + 1 + 4 * (2 * A 1 * W ^ (A 1) + 1) ∧
          ∀ i ∈ V,
            N04FlowAngularControl (rootRescaledField (d i) (c i) δ) 1 ∧
            ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
              N04FlowEquations (rootRescaledField (d i) (c i) δ) Θ ∧
              N04FlowJetBounds p outLoss B (w i) W 1 Θ := by
  obtain ⟨flowLow, outLoss, hflow⟩ :=
    exists_rootRescaledFlow_fixed_loss hFlow hp hI inputLoss
  refine ⟨max (1 + inputLoss) flowLow, outLoss, ?_⟩
  intro A hA
  obtain ⟨B, hB, hbound⟩ := hflow A hA 1 zero_le_one
  refine ⟨B, hB, ?_⟩
  intro W hW ρ hρ ι V w d c hregular hperiod hlow hdb hcb
  let M : ℝ := 2 * A 1 * W ^ (A 1)
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hA0 : 0 ≤ A 1 := zero_le_one.trans (hA 1)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (by norm_num) hA0) (Real.rpow_nonneg hW0 _)
  let δ := rootPolynomialControlRadius ρ M
  obtain ⟨hδ, hδρ, hδone, hδsmall, hδinv⟩ := rootPolynomialControlRadius_bounds hρ hM
  have hfirst (i : ι) (hi : i ∈ V) : p (1 + inputLoss) (w i) ≤ 1 :=
    (hp (Nat.le_max_left (1 + inputLoss) flowLow) _).trans (hlow i hi)
  have hcap (i : ι) (hi : i ∈ V) :
      A 1 * W ^ (A 1) * (1 + p (1 + inputLoss) (w i)) ≤ M := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 + p (1 + inputLoss) (w i) ≤ 2 by linarith only [hfirst i hi])
      (mul_nonneg hA0 (Real.rpow_nonneg hW0 (A 1)))
    exact h.trans_eq (by dsimp only [M]; ring)
  have hfirstD (i : ι) (hi : i ∈ V) (r : ℝ) (hr : |r| ≤ δ) (θ : ℝ) :
      |deriv (fun η => d i (r, η)) θ| ≤ M :=
    (abs_deriv_angular_le_first_frechet (hregular i hi).1 r θ).trans
      ((hdb i hi 1 r (hr.trans hδρ) θ).trans (hcap i hi))
  have hfirstC (i : ι) (hi : i ∈ V) (r : ℝ) (hr : |r| ≤ δ) (θ : ℝ) :
      |deriv (fun η => c i (r, η)) θ| ≤ M :=
    (abs_deriv_angular_le_first_frechet (hregular i hi).2 r θ).trans
      ((hcb i hi 1 r (hr.trans hδρ) θ).trans (hcap i hi))
  refine ⟨δ, hδ, hδρ, hδone, hδinv, ?_⟩
  intro i hi
  have hcontrol : N04FlowAngularControl (rootRescaledField (d i) (c i) δ) 1 := by
    refine ⟨fun _ => 1, continuousOn_const, fun _ _ => zero_le_one, ?_, ?_⟩
    · intro t ht v hv θ
      exact (rootRescaledField_angular_deriv_le (hregular i hi).1 (hregular i hi).2
        hδ.le hM (hfirstD i hi) (hfirstC i hi) ht hv θ).trans hδsmall
    · simp only [intervalIntegral.integral_const, sub_zero, one_smul, le_refl]
  refine ⟨hcontrol, ?_⟩
  exact hbound (w i)
    ((hp (Nat.le_max_right (1 + inputLoss) flowLow) _).trans (hlow i hi))
    W hW δ hδ.le hδone (d i) (c i)
    (hregular i hi).1 (hregular i hi).2 (hperiod i hi).1 (hperiod i hi).2
    (fun n r hr θ => hdb i hi n r (hr.trans hδρ) θ)
    (fun n r hr θ => hcb i hi n r (hr.trans hδρ) θ) hcontrol

end ContinuousFlexibility.Analysis
