import ContinuousFlexibility.Analysis.N01cFlowParameterNormalization
import ContinuousFlexibility.Analysis.N01cFlowOrderConstants
import ContinuousFlexibility.Analysis.N01cStateInterpolation

/-!
# A common-base normalization interface for the flow induction

The property below is supplied by the already proved interpolation
normalization. It is available on every larger base before any
parameter order, polynomial degree, or spatial order is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

def FlowPolynomialNormalization
    (p : ℕ → Seminorm ℝ E) (base loss : ℕ) : Prop :=
  ∀ k degree offset s : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ x : E, p base x ≤ 1 → ∀ A : E [×k]→L[ℝ] ℝ, ∀ M : ℝ, 0 ≤ M →
      (∀ v : Fin k → E, (∀ i, p base (v i) < 1) →
        ‖A v‖ ≤ M *
          ((1 + p (s + offset) x) + ∑ i, p (s + offset) (v i)) *
          (((1 + p offset x) + ∑ i, p offset (v i)) ^ degree)) →
      ∀ v : Fin k → E, ‖A v‖ ≤ M * C *
        oneHighVariationWeight p base (s + (degree + 1) * offset + loss) x v

theorem exists_stable_flowPolynomialNormalization
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hi : HasInterpolation p) :
    ∃ base loss : ℕ, ∀ base' : ℕ, base ≤ base' →
      FlowPolynomialNormalization p base' loss := by
  obtain ⟨base, loss, hb⟩ := exists_flowVariationPolynomialNormalization (F := ℝ) p hp hi
  refine ⟨base, loss, fun base' hbase k degree offset s => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hb k degree offset s
  exact ⟨C, hC, hbound base' hbase⟩

theorem n01c_transform_offset_constants_map
    (P Q : ℕ → ℕ → ℝ → Prop) (f : ℕ → ℕ)
    (hP : ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P d s B)
    (hstep : ∀ d s B, 0 < B → P d s B →
      ∃ C : ℝ, 0 < C ∧ Q (f d) s C) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ Q d s C := by
  obtain ⟨d, hd⟩ := hP
  refine ⟨f d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hd s
  exact hstep d s B hB hb

theorem n01c_spatialize_offset_bounds
    (P : ℕ → ℕ → ℝ → Prop) (loss : ℕ)
    (hmono : ∀ b a a' B B', a ≤ a' → 0 < B → B ≤ B' →
      P b a B → P b a' B')
    (hP : ∃ d : ℕ, ∀ b : ℕ, ∃ B : ℝ, 0 < B ∧ P b (b + loss + d) B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ b, b ≤ s → P b (s + loss + d) B := by
  obtain ⟨d, hd⟩ := hP
  refine ⟨d, ?_⟩
  simpa only [Nat.add_assoc] using
    n01c_spatial_prefix P (loss + d) hmono (by simpa only [Nat.add_assoc] using hd)

end ContinuousFlexibility.Analysis
