import ContinuousFlexibility.Analysis.PositiveReferenceFiniteRadialJets
import Mathlib.Topology.Order.Compact

/-!
# All orders of the same finite radial Taylor slice

The degree is fixed before the derivative order. Only the original
finite coefficients enter the bound, linearly. Compactness is used on
the fixed interval [-1,1] for standard monomials, before the center,
source field or coefficient envelope is supplied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- One fixed Taylor representative has bounds at every requested order
on a unit neighborhood. No new degree or geometric width is selected. -/
theorem exists_radialEndpointTaylorSlice_jet_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : ℝ}, 0 ≤ M →
      ∀ (f : PolarPoint → ℝ) (c : ℝ),
        (∀ j, j ≤ n → |radialBoundaryJet f c j 0| ≤ M) →
        ∀ k, k ≤ N → ∀ x : ℝ, |x - c| ≤ 1 →
          |iteratedDeriv k (radialEndpointTaylorSlice n c f) x| ≤ C * M := by
  classical
  let V : ℕ → ℝ → ℝ := fun j x => x ^ j / (j.factorial : ℝ)
  have hV (j : ℕ) : ContDiff ℝ ∞ (V j) :=
    (contDiff_id.pow j).div_const _
  have hb (i : Fin (n + 1) × Fin (N + 1)) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
        |iteratedDeriv i.2.val (V i.1.val) x| ≤ B := by
    have hc : Continuous (fun x => |iteratedDeriv i.2.val (V i.1.val) x|) :=
      (ContDiff.continuous_iteratedDeriv i.2.val (hV i.1.val) (by simp)).abs
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun x hx =>
      (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let C : ℝ := 1 + ∑ i : Fin (n + 1) × Fin (N + 1), B i
  have hC : 1 ≤ C := by
    have hs : 0 ≤ ∑ i : Fin (n + 1) × Fin (N + 1), B i :=
      Finset.sum_nonneg fun i _ => hB i
    dsimp only [C]
    linarith only [hs]
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hbasis (j k : ℕ) (hj : j ≤ n) (hk : k ≤ N)
      (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      |iteratedDeriv k (V j) x| ≤ C := by
    let i : Fin (n + 1) × Fin (N + 1) :=
      (⟨j, Nat.lt_succ_of_le hj⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
    have hsingle : B i ≤ ∑ t : Fin (n + 1) × Fin (N + 1), B t :=
      Finset.single_le_sum (fun t _ => hB t) (Finset.mem_univ i)
    exact (hbound i x hx).trans (hsingle.trans
      (le_add_of_nonneg_left zero_le_one))
  refine ⟨1 + ((n + 1 : ℕ) : ℝ) * C,
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hC0), ?_⟩
  intro M hM f c hcoeff k hk x hx
  let A : ℕ → ℝ := fun j => radialBoundaryJet f c j 0
  have hformula : radialEndpointTaylorSlice n c f =
      fun t => ∑ j ∈ Finset.range (n + 1), A j * V j (t - c) := by
    funext t
    change (∑ j ∈ Finset.range (n + 1),
      A j / (j.factorial : ℝ) * (t - c) ^ j) = _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [V]
    ring
  have hterm (j : ℕ) : ContDiff ℝ ∞ (fun t => A j * V j (t - c)) :=
    contDiff_const.mul ((hV j).comp (contDiff_id.sub contDiff_const))
  rw [hformula, iteratedDeriv_fun_sum (fun j _ =>
    ((hterm j).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        |A j * iteratedDeriv k (fun t => V j (t - c)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (n + 1), M * C := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hshift := congrFun (iteratedDeriv_comp_sub_const k (V j) c) x
      rw [abs_mul, hshift]
      exact mul_le_mul (hcoeff j hjn)
        (hbasis j k hjn hk (x - c) (abs_le.mp hx)) (abs_nonneg _) hM
    _ = ((n + 1 : ℕ) : ℝ) * (M * C) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((n + 1 : ℕ) : ℝ) * C) * M := by ring
    _ ≤ (1 + ((n + 1 : ℕ) : ℝ) * C) * M :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hM

end ContinuousFlexibility.Analysis
