module

public import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph
public import ContinuousFlexibility.Radial.InnerBoundedOverlap
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Hilbert incidence for the actual finite physical chain

These restrictions are the same two endpoint values used by the physical
weak domain, now with their Euclidean norm. Each internal cut is counted
once on each of its two sides. The boundary vector contains no outer
endpoint coordinates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators InnerProductSpace

/-- The physical boundary restriction, with the Euclidean two-cut norm. -/
def innerChainBoundaryCLM (n : ℕ) (p : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘L
    (innerChainBoundaryRestriction n p).toContinuousLinearMap

@[simp] theorem innerChainBoundaryCLM_apply (n : ℕ) (p : Fin (n + 1))
    (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin 2) :
    innerChainBoundaryCLM n p ξ i = innerChainBoundaryRestriction n p ξ i := rfl

theorem innerChainBoundary_left_sum (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ p : Fin (n + 1), (innerChainBoundaryRestriction n p ξ 0) ^ 2) =
      ∑ i : Fin n, (ξ i) ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [(innerChainBoundaryRestriction_outer n ξ).1,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z : ℝ => z ^ 2)
    (innerChainBoundaryRestriction_match n i ξ).2)

theorem innerChainBoundary_right_sum (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ p : Fin (n + 1), (innerChainBoundaryRestriction n p ξ 1) ^ 2) =
      ∑ i : Fin n, (ξ i) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [(innerChainBoundaryRestriction_outer n ξ).2,
    zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, zero_add]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z : ℝ => z ^ 2)
    (innerChainBoundaryRestriction_match n i ξ).1)

/-- The exact incidence identity, on the boundary space used by gluing. -/
theorem innerChainBoundary_bessel_eq (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ p : Fin (n + 1), ‖innerChainBoundaryCLM n p ξ‖ ^ 2) = 2 * ‖ξ‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, innerChainBoundaryCLM_apply]
  rw [Finset.sum_add_distrib, innerChainBoundary_left_sum, innerChainBoundary_right_sum]
  ring

theorem innerChainBoundary_bessel (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ p : Fin (n + 1), ‖innerChainBoundaryCLM n p ξ‖ ^ 2) ≤ 2 * ‖ξ‖ ^ 2 :=
  (innerChainBoundary_bessel_eq n ξ).le

/-- The local two-cut errors are extended by the adjoints of the same
restrictions as in the actual weak outgoing-flux sum. -/
theorem norm_innerChainBoundaryBlockSum_le (n : ℕ)
    (K : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ p, ‖K p‖ ≤ η) :
    ‖innerInterfaceBlockSum (innerChainBoundaryCLM n) K‖ ≤ 2 * η :=
  norm_innerInterfaceBlockSum_le _ K (by norm_num) hη (innerChainBoundary_bessel n) hK

/-- The contractive full reference normalization gives the strict
one-half bound on the actual physical boundary space. -/
theorem norm_innerChainBoundaryBlockSum_normalized_lt_half (n : ℕ)
    (K : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (hK : ∀ p, ‖K p‖ ≤ η) (hA : ‖A‖ ≤ 1) :
    ‖A ∘L innerInterfaceBlockSum (innerChainBoundaryCLM n) K ∘L A.adjoint‖ < 1 / 2 := by
  have h := norm_innerInterfaceBlockSum_normalized_le
    (innerChainBoundaryCLM n) K A (by norm_num : (0 : ℝ) ≤ 2) hη
    (innerChainBoundary_bessel n) hK hA
  exact h.trans_lt (by linarith)

end ContinuousFlexibility.Radial
