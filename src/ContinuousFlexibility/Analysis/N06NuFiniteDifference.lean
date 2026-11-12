import ContinuousFlexibility.Analysis.N06NuFiniteSmooth
import ContinuousFlexibility.Analysis.N06FiniteJetDifference

/-!
# Finite-dimensional Lipschitz jets of the actual nu formula

The compact derivative bounds for the real nu formula, the straight-segment
mean value estimate, and the actual ordered-partition chain rule give one
uniform Lipschitz bound for every fixed composition jet. These are ordinary
finite-dimensional estimates, before any state or source space is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem n06_norm_iteratedFDeriv_sub_eq_iteratedDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u v : ℝ → F) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n u x - iteratedFDeriv ℝ n v x‖ =
      ‖iteratedDeriv n u x - iteratedDeriv n v x‖ := by
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
    ← map_sub, LinearIsometryEquiv.norm_map]

theorem n06NuFiniteJetMap_finite_derivative_bound (M : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≤ n → ∀ v : N06NuJetCoordinates,
      ‖v‖ ≤ M → (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant v →
        ‖iteratedFDeriv ℝ k n06NuFiniteJetMap v‖ ≤ C := by
  classical
  have hchoices (i : Fin (n + 1)) := n06NuFiniteJetMap_iteratedFDeriv_bound M i.val
  choose c hc hbound using hchoices
  let C : ℝ := ∑ i : Fin (n + 1), c i
  refine ⟨C, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro k hk v hv hdisc
  let i : Fin (n + 1) := ⟨k, by omega⟩
  exact (hbound i v hv hdisc).trans
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i))

/-- The constant is fixed before the two actual input curves and their
difference size. Positivity is required along their literal value segment. -/
theorem n06NuFiniteJetMap_composition_difference_bound (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (u v : ℝ → N06NuJetCoordinates) (θ δ : ℝ),
      ContDiffAt ℝ ∞ u θ → ContDiffAt ℝ ∞ v θ → 0 ≤ δ →
      (∀ k, k ≤ n → ‖iteratedDeriv k u θ‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedDeriv k v θ‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedDeriv k u θ - iteratedDeriv k v θ‖ ≤ δ) →
      (∀ w ∈ segment ℝ (v θ) (u θ), (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant w) →
      ‖iteratedDeriv n (n06NuFiniteJetMap ∘ u) θ -
        iteratedDeriv n (n06NuFiniteJetMap ∘ v) θ‖ ≤ Q * δ := by
  obtain ⟨C, hC, houter⟩ := n06NuFiniteJetMap_finite_derivative_bound M (n + 1)
  refine ⟨n06CompositionDifferenceCost n C M,
    n06CompositionDifferenceCost_nonneg n hC hM, ?_⟩
  intro u v θ δ hu hv hδ hU hV hUV hdisc
  have hu₀ : ‖u θ‖ ≤ M := by simpa only [iteratedDeriv_zero] using hU 0 (Nat.zero_le n)
  have hv₀ : ‖v θ‖ ≤ M := by simpa only [iteratedDeriv_zero] using hV 0 (Nat.zero_le n)
  have hdiff₀ : ‖u θ - v θ‖ ≤ δ := by
    simpa only [iteratedDeriv_zero] using hUV 0 (Nat.zero_le n)
  have hvalue : ∀ w ∈ segment ℝ (v θ) (u θ), ‖w‖ ≤ M := by
    intro w hw
    have hvmem : v θ ∈ Metric.closedBall (0 : N06NuJetCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv₀
    have humem : u θ ∈ Metric.closedBall (0 : N06NuJetCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu₀
    have hwmem := (convex_closedBall (0 : N06NuJetCoordinates) M).segment_subset hvmem humem hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using hwmem
  have hsmooth : ∀ w ∈ segment ℝ (v θ) (u θ), ContDiffAt ℝ ∞ n06NuFiniteJetMap w := by
    intro w hw
    exact n06NuFiniteJetMap_contDiffAt (lt_of_lt_of_le (by norm_num) (hdisc w hw))
  have hΦu := hsmooth (u θ) (right_mem_segment ℝ (v θ) (u θ))
  have hΦv := hsmooth (v θ) (left_mem_segment ℝ (v θ) (u θ))
  have houterValue (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k n06NuFiniteJetMap (u θ)‖ ≤ C :=
    houter k (by omega) (u θ) hu₀ (hdisc (u θ) (right_mem_segment ℝ _ _))
  have houterDifference (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k n06NuFiniteJetMap (u θ) -
        iteratedFDeriv ℝ k n06NuFiniteJetMap (v θ)‖ ≤ C * δ := by
    have h := n06_iteratedFDeriv_difference_le_segment k hsmooth
      (fun w hw => houter (k + 1) (by omega) w (hvalue w hw) (hdisc w hw))
    exact h.trans (mul_le_mul_of_nonneg_left hdiff₀ hC)
  have hinputU (k : ℕ) (hk : k ≤ n) : ‖iteratedFDeriv ℝ k u θ‖ ≤ M := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hU k hk
  have hinputV (k : ℕ) (hk : k ≤ n) : ‖iteratedFDeriv ℝ k v θ‖ ≤ M := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hV k hk
  have hinputDiff (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k u θ - iteratedFDeriv ℝ k v θ‖ ≤ δ := by
    rw [n06_norm_iteratedFDeriv_sub_eq_iteratedDeriv]
    exact hUV k hk
  have h := n06_iteratedFDeriv_comp_difference_le n hΦu hΦv hu hv hC hM hδ
    houterValue houterDifference hinputU hinputV hinputDiff
  rw [n06_norm_iteratedFDeriv_sub_eq_iteratedDeriv] at h
  exact h

end ContinuousFlexibility.Analysis
