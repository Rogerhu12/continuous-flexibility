import ContinuousFlexibility.Analysis.N04PositiveGeometryFiniteKernelBounds
import ContinuousFlexibility.Analysis.N01cStateAngleSelections

/-!
# Saved positive words through a finite coefficient kernel

Every nonempty partition block has positive weighted order. Subtracting
one from each block therefore leaves at least one saved order after the
blocks are combined. The original parameter arity still determines the
single height factor in the resulting bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_partition_savedWord_cost
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (C : ℕ) (hC : 1 ≤ C)
    (π : OrderedFinpartition n) :
    (∑ i : Fin π.length, ((w.restrict (π.emb i)).angleArity +
      C * (w.restrict (π.emb i)).stateArity - 1)) ≤
        w.angleArity + C * w.stateArity - 1 := by
  have hpos (i : Fin π.length) :
      1 ≤ (w.restrict (π.emb i)).angleArity + C * (w.restrict (π.emb i)).stateArity := by
    have hs := (w.restrict (π.emb i)).arity_sum
    have hp := π.partSize_pos i
    have hc : (w.restrict (π.emb i)).stateArity ≤
        C * (w.restrict (π.emb i)).stateArity := by
      simpa only [one_mul] using Nat.mul_le_mul_right (w.restrict (π.emb i)).stateArity hC
    omega
  have he : (∑ i : Fin π.length, ((w.restrict (π.emb i)).angleArity +
      C * (w.restrict (π.emb i)).stateArity - 1)) + π.length =
        w.angleArity + C * w.stateArity := by
    calc
      _ = ∑ i : Fin π.length, (((w.restrict (π.emb i)).angleArity +
          C * (w.restrict (π.emb i)).stateArity - 1) + 1) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_id, mul_one]
      _ = ∑ i : Fin π.length, ((w.restrict (π.emb i)).angleArity +
          C * (w.restrict (π.emb i)).stateArity) :=
        Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hpos i))
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          w.sum_restrict_angleArity π, w.sum_restrict_stateArity π]
  have hp := π.length_pos hn
  omega

variable {X F G : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set X} {V : Set F} {f : X → F} {g : F → G}

theorem n04PositiveGeometry_finiteKernel_savedWord_bound
    (J : SmoothDirections U f) (hV : IsOpen V)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    (Q : SmoothDirections U (g ∘ f))
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (shift : ℕ) (hshift : 1 ≤ shift)
    (x : X) (hx : x ∈ U) (v : Fin n → X)
    {A M H t : ℝ} (hA : 0 ≤ A) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHM : H ≤ M) (ht : 1 ≤ t)
    (houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A)
    (hinner : ∀ π : OrderedFinpartition n, ∀ i : Fin π.length,
      ‖J.D (π.partSize i) x (v ∘ π.emb i)‖ ≤
        M * parameterHeightWeight H (w.restrict (π.emb i)).stateArity *
          t ^ ((w.restrict (π.emb i)).angleArity +
            shift * (w.restrict (π.emb i)).stateArity - 1)) :
    ‖Q.D n x v‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) *
      A * M ^ n * M ^ n * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) :=
  n04PositiveGeometry_finiteKernel_weighted_bound J hV hg hmap Q
    n w.stateArity (w.angleArity + shift * w.stateArity - 1) x hx v
    (fun π i => (w.restrict (π.emb i)).stateArity)
    (fun π i => (w.restrict (π.emb i)).angleArity +
      shift * (w.restrict (π.emb i)).stateArity - 1)
    w.sum_restrict_stateArity
    (fun π => n04PositiveGeometry_partition_savedWord_cost hn w shift hshift π)
    hA hM hH hHM hM ht houter hinner

end ContinuousFlexibility.Analysis
