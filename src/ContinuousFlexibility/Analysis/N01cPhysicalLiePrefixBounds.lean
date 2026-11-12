import ContinuousFlexibility.Analysis.N01cPhysicalLieRawBounds
import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization

/-!
# A finite genuine outer Lie-jet prefix

The ordered graph formula uses finitely many state and angular orders.
Their material constants can be enlarged together while preserving the
individual angular exponent and the same raw loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem endpointMixedPowerBounds_physicalLiePrefix
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (hU : IsOpen U) (hΩ : ∀ m, IsOpen (Ω m))
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m))
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    {width : ℝ} (hwidth : ∀ m q, q ∈ Ω m → δ m q ≤ width)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    {RH : ℝ} (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q ∧ H m q ≤ RH)
    (n N S : ℕ) (hnN : n + N ≤ S) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ j b, j + b ≤ N → ∀ m q, q ∈ Ω m →
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative 0 b (physicalFlowLieJet (f m x) n) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      ∀ v : Fin j → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (S + loss) (x - center) ≤ R →
        (∀ i, p (S + loss) (v i) ≤ R) →
        δ m q ^ (n + 1) * ‖J.D j x v‖ ≤
          C * E m q ^ A * parameterHeightWeight (H m q) j *
            R ^ (((n + b : ℕ) : ℝ) / ((S : ℝ) + 1)) := by
  classical
  let P : (Fin (N + 1) × Fin (N + 1)) → ℝ → ℝ → Prop :=
    fun i C A => i.1.val + i.2.val ≤ N →
      ∀ m q, q ∈ Ω m →
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative 0 i.2.val (physicalFlowLieJet (f m x) n) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      ∀ v : Fin i.1.val → X, (∀ l, p base (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (S + loss) (x - center) ≤ R →
        (∀ l, p (S + loss) (v l) ≤ R) →
        δ m q ^ (n + 1) * ‖J.D i.1.val x v‖ ≤
          C * E m q ^ A * parameterHeightWeight (H m q) i.1.val *
            R ^ (((n + i.2.val : ℕ) : ℝ) / ((S : ℝ) + 1))
  have hmono : ∀ i C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      P i C A → P i C' A' := by
    intro i C A C' A' hC _ hCC hAA hb hi m q hq J x hx hxl v hv R hR hxh hvh
    have hfac : C * E m q ^ A ≤ C' * E m q ^ A' :=
      mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le (hE m q hq) hAA)
        (Real.rpow_nonneg (zero_le_one.trans (hE m q hq)) _)
        ((zero_le_one.trans hC).trans hCC)
    exact (hb hi m q hq J x hx hxl v hv R hR hxh hvh).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfac
          (parameterHeightWeight_nonneg (hH m q hq).1 _))
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have hbound : ∀ i, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ P i C A := by
    intro i
    obtain ⟨C, A, hC, hA, hb⟩ :=
      endpointMixedPowerBounds_physicalLieAngular hU hΩ F hf hδ hwidth hE hH
        n i.2.val i.1.val S
        ((Nat.add_le_add le_rfl (Nat.le_of_lt_succ i.2.isLt)).trans hnN)
    exact ⟨C, A, hC, hA, fun _ => hb⟩
  obtain ⟨C, A, hC, hA, hb⟩ := exists_finite_graph_materialConstants P hmono hbound
  refine ⟨C, A, hC, hA, ?_⟩
  intro j b hjb
  let ij : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le (by omega)⟩
  let ib : Fin (N + 1) := ⟨b, Nat.lt_succ_of_le (by omega)⟩
  exact hb (ij, ib) hjb

end ContinuousFlexibility.Analysis
