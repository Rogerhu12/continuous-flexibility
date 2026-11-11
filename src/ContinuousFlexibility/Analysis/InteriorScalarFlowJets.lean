import ContinuousFlexibility.Analysis.InteriorScalarFlowField
import ContinuousFlexibility.Analysis.N04FlowTimeReversal

/-!
# Actual forward and inverse flows through a fixed radial interior

Only the original scalar speed has prescribed spatial estimates. Its
first derivative on one low state ball gives a state-independent angular
Gronwall constant. Picard existence and the proved mixed-flow theorem
then provide both actual flows and all their spatial displacement jets.
The common state order and loss precede the interval and its constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def InteriorSpeedJetBounds
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (A : ℕ → ℝ)
    (z : E) (a b : ℝ) (f : PolarPoint → ℝ) : Prop :=
  ∀ n : ℕ, ∀ r ∈ Icc a b, ∀ θ : ℝ,
    ‖iteratedFDeriv ℝ n f (r, θ)‖ ≤ A n * (1 + p (n + loss) z)

theorem interiorScalarFlowField_rawJets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (inputLoss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n) (a b : ℝ) (hab : a ≤ b) :
    ∃ D : ℕ → ℝ, (∀ n, 1 ≤ D n) ∧
      ∀ z : E, ∀ f : PolarPoint → ℝ, ContDiff ℝ ∞ f →
        InteriorSpeedJetBounds p inputLoss A z a b f →
        N04FlowRawJetBounds p inputLoss D z 1 (interiorScalarFlowField f a b) := by
  let H : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), A i
  have hAH (n k : ℕ) (hk : k ≤ n) : A k ≤ H n :=
    Finset.single_le_sum (fun i _ => zero_le_one.trans (hA i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hH (n : ℕ) : 1 ≤ H n := (hA n).trans (hAH n n le_rfl)
  let C : ℕ → ℝ := fun n =>
    affineWeightedCompositionJetConstant (1 + |(b - a) / 2|) n * (2 * |(b - a) / 2|)
  have hC (n : ℕ) : 0 ≤ C n := mul_nonneg
    (zero_le_one.trans (one_le_affineWeightedCompositionJetConstant (by positivity) n))
    (by positivity)
  let D : ℕ → ℝ := fun n => 1 + C n * H n
  have hD (n : ℕ) : 1 ≤ D n :=
    le_add_of_nonneg_right (mul_nonneg (hC n) (zero_le_one.trans (hH n)))
  refine ⟨D, hD, ?_⟩
  intro z f hf hjets n t ht q hq
  let M : ℝ := H n * (1 + p (n + inputLoss) z)
  have hstate : 0 ≤ 1 + p (n + inputLoss) z :=
    add_nonneg zero_le_one (apply_nonneg _ _)
  have hM : 0 ≤ M := mul_nonneg (zero_le_one.trans (hH n)) hstate
  have hinput (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k f (interiorFlowRadius a b t q.1, q.2)‖ ≤ M := by
    exact (hjets k _ (interiorFlowRadius_mem hab ht hq) q.2).trans
      (mul_le_mul (hAH n k hk)
        (add_le_add (le_refl (1 : ℝ))
          (hp (Nat.add_le_add_right hk inputLoss) z))
        (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hH n)))
  have hraw := interiorScalarFlowField_jet_le hf a b hM ht hq n hinput
  have hpack : C n * M ≤ D n * (1 + p (n + inputLoss) z) := by
    dsimp only [M, D]
    calc
      _ = (C n * H n) * (1 + p (n + inputLoss) z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one) hstate
  simpa only [Real.one_rpow, mul_one] using hraw.trans hpack

def InteriorFlowPairBounds
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (Λ a b : ℝ) (f : PolarPoint → ℝ)
    (Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ) : Prop :=
  N04FlowEquations (interiorScalarFlowField f a b) Θ ∧
    N04FlowEquations (n04FlowReverseField (interiorScalarFlowField f a b)) Ψ ∧
    (∀ v θ, Θ v 1 (Ψ v 1 θ) = θ ∧ Ψ v 1 (Θ v 1 θ) = θ) ∧
    N04FlowJetBounds p loss B z 1 Λ Θ ∧ N04FlowJetBounds p loss B z 1 Λ Ψ

/-- The actual inverse is constructed by reversing the actual equation.
Its quantitative derivative tower is a conclusion. The angular exponent
uses only the speed's first-order constant. -/
theorem exists_interiorScalarFlowPair_fixed_loss
    (hFlow : N04FlowJetsTarget)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ a b : ℝ, a ≤ b → ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ f : PolarPoint → ℝ,
        ContDiff ℝ ∞ f → (∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi) →
        InteriorSpeedJetBounds p inputLoss A z a b f →
        ∃ Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
          InteriorFlowPairBounds p outLoss B z Λ a b f Θ Ψ := by
  obtain ⟨flowBase, outLoss, htarget⟩ :=
    n04FlowJetsTarget_with_actual_inverse hFlow p hp hI inputLoss
  refine ⟨max flowBase (1 + inputLoss), outLoss, ?_⟩
  intro A hA a b hab
  obtain ⟨D, hD, hraw⟩ := interiorScalarFlowField_rawJets hp inputLoss A hA a b hab
  let Λ : ℝ := 2 * |(b - a) / 2| * (2 * A 1)
  have hΛ : 0 ≤ Λ := by
    have hA₁ : 0 ≤ A 1 := zero_le_one.trans (hA 1)
    dsimp only [Λ]
    positivity
  obtain ⟨B, hB, hbound⟩ := htarget D hD Λ hΛ
  refine ⟨Λ, hΛ, B, hB, ?_⟩
  intro z hz f hf hperiod hjets
  have hzFlow : p flowBase z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzOne : p (1 + inputLoss) z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hfirst (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) :
      |deriv (fun η => f (r, η)) θ| ≤ 2 * A 1 := by
    apply ((abs_deriv_angular_le_first_frechet hf r θ).trans (hjets 1 r hr θ)).trans
    calc
      _ ≤ A 1 * 2 := mul_le_mul_of_nonneg_left
        (by linarith only [hzOne]) (zero_le_one.trans (hA 1))
      _ = 2 * A 1 := by ring
  let F := interiorScalarFlowField f a b
  have hF : ContDiff ℝ ∞ F := contDiff_interiorScalarFlowField hf a b
  have hper : ∀ t v, Function.Periodic (fun θ => F (t, (v, θ))) Real.pi :=
    interiorScalarFlowField_periodic hperiod a b
  have hcontrol : N04FlowAngularControl F Λ :=
    interiorScalarFlowField_angularControl hf hab
      (mul_nonneg (by norm_num) (zero_le_one.trans (hA 1))) hfirst
  obtain ⟨Θ, hi, hd, _, _⟩ := exists_continuous_periodicScalarFlowFamily
    (F := F) zero_le_one Real.pi_ne_zero hF (fun t _ => hper t)
  have hΘ : N04FlowEquations F Θ := ⟨hi, hd⟩
  obtain ⟨hforward, Ψ, hΨ, hinverse, hreverse⟩ :=
    hbound z hzFlow 1 le_rfl F hF hper (hraw z f hf hjets) hcontrol Θ hΘ
  exact ⟨Θ, Ψ, hΘ, hΨ, hinverse, hforward, hreverse⟩

end ContinuousFlexibility.Analysis
