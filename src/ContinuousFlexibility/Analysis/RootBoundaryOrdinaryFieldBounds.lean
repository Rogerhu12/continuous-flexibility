module

public import ContinuousFlexibility.Analysis.RootBoundaryMaterialJets
public import ContinuousFlexibility.Analysis.RootInputOrdinaryJets

/-!
# Combining the actual ordinary field and coefficient inputs

The root-even/odd extension estimates and the original radial-coefficient
estimate can have different fixed losses. Their maximum is taken before
the root and the order constants; all subsequent numerical work stays
in the abstract state grading.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def RootBoundaryOrdinaryFieldControl
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (fieldLoss coefficientLoss base loss : ℕ)
    (A C : ℕ → ℝ) (χl al au : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z : E, p base z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ, ∀ a : PolarPoint → ℝ,
    ∀ h : ℝ → ℝ, ∀ θ k : ℝ, θ ∈ Icc (-Real.pi) Real.pi →
    ContDiff ℝ ∞ G →
    (∀ x ζ η, G (x, ζ, η + Real.pi) = G (x, ζ, η) + Real.pi) →
    (∀ η, G (0, 0, η) = h η) → HasDerivAt h k θ → k ∈ Icc (1 / 4 : ℝ) 4 →
    χl ≤ rootOddCoefficient G (0, θ) →
    ContDiffAt ℝ ∞ a (0, θ) → a (0, θ) ∈ Icc al au →
    RootOrdinaryFieldJetBound p fieldLoss A z G →
    PointwiseMaterialJetBound p coefficientLoss C z a (0, θ) →
    RootBoundaryMaterialJetBound p loss B z a G θ

theorem rootBoundary_from_ordinaryFields_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (fieldLoss coefficientLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A C : ℕ → ℝ, (∀ n, 0 < A n) → (∀ n, 0 < C n) →
      ∀ χl al au : ℝ, 0 < χl → 0 < al → al ≤ au →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        RootBoundaryOrdinaryFieldControl p fieldLoss coefficientLoss base loss A C χl al au B := by
  obtain ⟨base, loss, hbound⟩ :=
    rootBoundary_fixed_loss_material_bound hp hI (max fieldLoss coefficientLoss)
  refine ⟨base, loss, ?_⟩
  intro A C hA hC χl al au hχl hal halu
  obtain ⟨B, hB, hb⟩ := hbound (fun n => A n + C n)
    (fun n => add_pos (hA n) (hC n)) χl al au hχl hal halu
  refine ⟨B, hB, ?_⟩
  intro z hz G a h θ k hθ hG hperiod hzero hderiv hk hpositive ha havalue hfields hcoefficient
  have hpoint : (0, θ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi := by
    change ((0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1) ∧ θ ∈ Icc (-Real.pi) Real.pi
    exact ⟨⟨le_rfl, zero_le_one⟩, hθ⟩
  have hφ : PointwiseMaterialJetBound p fieldLoss A z (extendedRootEven G) (0, θ) :=
    fun n => (hfields.2.2 n).1 n le_rfl (0, θ) hpoint
  have hχ : PointwiseMaterialJetBound p fieldLoss A z (extendedRootOddCoefficient G) (0, θ) :=
    fun n => (hfields.2.2 n).2 n le_rfl (0, θ) hpoint
  exact hb z hz G a h θ k hG hperiod hzero hderiv hk hpositive ha havalue
    (hφ.mono hp (le_max_left _ _) (fun n => (hA n).le)
      (fun n => le_add_of_nonneg_right (hC n).le))
    (hχ.mono hp (le_max_left _ _) (fun n => (hA n).le)
      (fun n => le_add_of_nonneg_right (hC n).le))
    (hcoefficient.mono hp (le_max_right _ _) (fun n => (hC n).le)
      (fun n => le_add_of_nonneg_left (hA n).le))

end ContinuousFlexibility.Analysis
