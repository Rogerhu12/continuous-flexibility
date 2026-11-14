module

public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
public import ContinuousFlexibility.Analysis.N01cPhysicalGraphRawBounds

/-!
# Final normalization and finite constants for physical radial jets

The complete weighted multilinear map is normalized once. Its raw power
is at most one by the proved Lie/graph order budget. Finite choices of
parameter and spatial indices enlarge only the material constants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

theorem exists_finite_graph_materialConstants
    {ι : Type*} [Fintype ι] (P : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      P i C A → P i C' A')
    (hbound : ∀ i, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ P i C A) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ i, P i C A := by
  classical
  choose C A hC hA hb using hbound
  let C₀ : ℝ := 1 + ∑ i, C i
  let A₀ : ℝ := ∑ i, A i
  have hsC : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hC i))
  have hsA : 0 ≤ A₀ := Finset.sum_nonneg (fun i _ => hA i)
  refine ⟨C₀, A₀, by dsimp only [C₀]; linarith, hsA, ?_⟩
  intro i
  have hCi : C i ≤ C₀ :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hC j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAi : A i ≤ A₀ :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  exact hmono i (C i) (A i) C₀ A₀ (hC i) (hA i) hCi hAi (hb i)

/-- A fixed scalar endpoint power scales the complete true multilinear
map; the one-high expression is obtained only after the raw estimate. -/
theorem weightedMultilinear_oneHigh_of_unitPower
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (x : X) {k : ℕ}
    (A : X [×k]→L[ℝ] ℝ) {δ M exponent : ℝ}
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hexponent : exponent ≤ 1)
    (hraw : ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high x ≤ R → (∀ i, p high (v i) ≤ R) →
        δ * |A v| ≤ M * R ^ exponent) :
    ∀ v : Fin k → X,
      δ * |A v| ≤ M * oneHighVariationWeight p base high x v := by
  let B : X [×k]→L[ℝ] ℝ := δ • A
  have hB (v : Fin k → X) : ‖B v‖ = δ * |A v| := by
    simp only [B, smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hδ,
      Real.norm_eq_abs]
  have hn := multilinear_bound_of_unitBall B (normSeminorm ℝ ℝ)
    (p base) (p high) hM (a := 1 + p high x) (fun v hv => by
      let R : ℝ := (1 + p high x) + ∑ i, p high (v i)
      have hs : 0 ≤ ∑ i, p high (v i) := Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p high) x]
      have hx : p high x ≤ R := by dsimp only [R]; linarith
      have hvR (i : Fin k) : p high (v i) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left (by positivity))
      have hh := (hraw v (fun i => (hv i).le) R hR hx hvR).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hR hexponent) hM)
      simpa only [coe_normSeminorm, hB, R] using hh)
  simpa only [coe_normSeminorm, hB, multilinearTameSize, oneHighVariationWeight] using hn

def physicalFlowGraphTop (s K offset : ℕ) : ℕ :=
  s + (offset + 1) * (K + 1)

theorem physicalFlowGraph_order_le_top
    {n b k s K offset : ℕ} (hab : n + 1 + b ≤ s) (hk : k ≤ K) :
    n + b + (offset + 1) * k ≤ physicalFlowGraphTop s K offset := by
  have hm : (offset + 1) * k ≤ (offset + 1) * (K + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.mul_le_mul_left (offset + 1) (hk.trans (Nat.le_succ K))
  dsimp only [physicalFlowGraphTop]
  exact Nat.add_le_add (show n + b ≤ s by omega) hm

theorem physicalFlowGraph_slots_offset_le_top
    {n b k s K offset : ℕ} (hab : n + 1 + b ≤ s) (hk : k ≤ K) :
    (b + k) + offset ≤ physicalFlowGraphTop s K offset := by
  have hm : offset ≤ offset * (K + 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left offset (Nat.succ_le_succ (Nat.zero_le K))
  dsimp only [physicalFlowGraphTop]
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem physicalFlowGraph_outerOrder_le_top
    {n b k s K offset l : ℕ} (hab : n + 1 + b ≤ s)
    (hk : k ≤ K) (hl : l ≤ b + k) :
    n + l ≤ physicalFlowGraphTop s K offset := by
  have hm : k ≤ (offset + 1) * k := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right k (Nat.succ_le_succ (Nat.zero_le offset))
  exact (show n + l ≤ n + b + (offset + 1) * k by omega).trans
    (physicalFlowGraph_order_le_top hab hk)

end ContinuousFlexibility.Analysis
