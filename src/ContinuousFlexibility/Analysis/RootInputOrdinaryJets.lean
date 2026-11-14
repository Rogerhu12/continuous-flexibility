module

public import ContinuousFlexibility.Analysis.RootExtensionPhysicalBounds
public import ContinuousFlexibility.Analysis.RootChartSymmetry

/-!
# Ordinary root jets from actual smooth input jets

The fixed Seeley extensions agree with the physical even and odd formulas.
Their ordinary jets, including the root itself, obey the already proved
finite-order estimates. Packaging those estimates costs one fixed input
order and preserves a single high state seminorm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local notation "rootInputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))
local notation "rootOutputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Icc (-Real.pi) Real.pi)

def RootOrdinaryFieldJetBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (G : ℝ × ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ (extendedRootEven G) ∧
    ContDiff ℝ ∞ (extendedRootOddCoefficient G) ∧
    ∀ s : ℕ,
      CSBound s rootOutputBox (extendedRootEven G)
          (B s * (1 + p (s + loss) z)) ∧
        CSBound s rootOutputBox (extendedRootOddCoefficient G)
          (B s * (1 + p (s + loss) z))

/-- One numerical majorant is chosen before the state and the actual
input function. No ordinary boundary derivatives of a totalized raw
root formula are used. -/
theorem exists_rootInput_ordinaryField_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (loss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ s, 0 < A s) :
    ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      ∀ (z : E) (G : ℝ × ℝ × ℝ → ℝ), ContDiff ℝ ∞ G →
      (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) →
      (∀ s, CSBound s rootInputBox G (A s * (1 + p (s + loss) z))) →
        RootOrdinaryFieldJetBound p (loss + 1) B z G := by
  choose CE hCE hEven using exists_csBound_extendedRootEven
  choose CO hCO hOdd using exists_csBound_extendedRootOddCoefficient
  let B : ℕ → ℝ := fun s => 1 + CE s * A s + CO s * A (s + 1)
  have hCE0 (s : ℕ) : 0 ≤ CE s := zero_le_one.trans (hCE s)
  have hB (s : ℕ) : 0 < B s :=
    add_pos (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (hCE0 s) (hA s).le)) (mul_pos (hCO s) (hA (s + 1)))
  refine ⟨B, hB, ?_⟩
  intro z G hG hperiod hinput
  have hφ : ∀ r, 0 ≤ r → ∀ θ,
      rootEven G (r, θ + Real.pi) = rootEven G (r, θ) + Real.pi :=
    fun r _ θ => rootEven_period_add hperiod r θ
  have hχ : ∀ r, 0 ≤ r →
      Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hperiod r
  refine ⟨contDiff_extendedRootEven hG Real.pi_ne_zero hφ,
    contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχ, ?_⟩
  intro s
  have hE := hEven s G hG Real.pi Real.pi_ne_zero hφ
    (A s * (1 + p (s + loss) z)) (hinput s)
  have hO := hOdd s G hG Real.pi Real.pi_ne_zero hχ
    (A (s + 1) * (1 + p (s + 1 + loss) z)) (hinput (s + 1))
  have hEB : CE s * A s ≤ B s := by
    dsimp only [B]
    linarith [mul_nonneg (hCO s).le (hA (s + 1)).le]
  have hOB : CO s * A (s + 1) ≤ B s := by
    dsimp only [B]
    linarith [mul_nonneg (hCE0 s) (hA s).le]
  constructor
  · apply hE.mono_bound
    rw [← mul_assoc]
    exact mul_le_mul hEB
      (add_le_add (le_refl (1 : ℝ)) ((hp (show s + loss ≤ s + (loss + 1) by omega)) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hB s).le
  · apply hO.mono_bound
    rw [← mul_assoc, show s + 1 + loss = s + (loss + 1) by omega]
    exact mul_le_mul_of_nonneg_right hOB
      (add_nonneg zero_le_one (apply_nonneg _ _))

end ContinuousFlexibility.Analysis
