import ContinuousFlexibility.Analysis.N04PositiveGeometryFiniteKernelBounds
import ContinuousFlexibility.Analysis.N01cStateAngleSelections

/-!
# Pure spatial savings through the actual finite kernel

A positive joint derivative with no parameter slot saves one spatial
order. A block containing parameter slots pays its fixed parameter
offset. Both properties survive composition with a material-controlled
finite kernel, because the exact partition arities are added before
the powers are estimated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_savedSpatialCost {n : ℕ}
    (w : StateAngleWord n) (offset : ℕ) : ℕ :=
  if w.stateArity = 0 then w.angleArity - 1
    else w.angleArity + offset * w.stateArity

/-- Nonempty pure spatial partitions save at least one order in total. -/
theorem n04PositiveGeometry_partition_savedSpatial_cost
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n)
    (c : OrderedFinpartition n) (offset : ℕ) :
    (∑ i : Fin c.length,
      n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset) ≤
        n04PositiveGeometry_savedSpatialCost w offset := by
  classical
  by_cases hw : w.stateArity = 0
  · have hz (i : Fin c.length) : (w.restrict (c.emb i)).stateArity = 0 := by
      have hle : (w.restrict (c.emb i)).stateArity ≤
          ∑ j : Fin c.length, (w.restrict (c.emb j)).stateArity :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [w.sum_restrict_stateArity c, hw] at hle
      exact Nat.eq_zero_of_le_zero hle
    have hpos (i : Fin c.length) : 0 < (w.restrict (c.emb i)).angleArity := by
      have hsum := (w.restrict (c.emb i)).arity_sum
      have hp := c.partSize_pos i
      rw [hz i, Nat.zero_add] at hsum
      omega
    have hstep (i : Fin c.length) :
        n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset + 1 =
          (w.restrict (c.emb i)).angleArity := by
      have hp := hpos i
      simp only [n04PositiveGeometry_savedSpatialCost, hz i, ite_true]
      omega
    have hsum :
        (∑ i : Fin c.length,
          n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset) + c.length =
          w.angleArity := by
      calc
        _ = ∑ i : Fin c.length,
            (n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset + 1) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_id, mul_one]
        _ = ∑ i : Fin c.length, (w.restrict (c.emb i)).angleArity :=
          Finset.sum_congr rfl (fun i _ => hstep i)
        _ = w.angleArity := w.sum_restrict_angleArity c
    have hc := c.length_pos hn
    simp only [n04PositiveGeometry_savedSpatialCost, hw, ite_true]
    omega
  · have hblock (i : Fin c.length) :
        n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset ≤
          (w.restrict (c.emb i)).angleArity +
            offset * (w.restrict (c.emb i)).stateArity := by
      unfold n04PositiveGeometry_savedSpatialCost
      split_ifs with hi
      · simp only [hi, Nat.mul_zero, Nat.add_zero]
        exact Nat.sub_le _ _
      · exact le_rfl
    calc
      _ ≤ ∑ i : Fin c.length, ((w.restrict (c.emb i)).angleArity +
          offset * (w.restrict (c.emb i)).stateArity) :=
        Finset.sum_le_sum (fun i _ => hblock i)
      _ = w.angleArity + offset * w.stateArity := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          w.sum_restrict_angleArity c, w.sum_restrict_stateArity c]
      _ = _ := by simp only [n04PositiveGeometry_savedSpatialCost, if_neg hw]

variable {X F G : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set X} {V : Set F} {f : X → F} {g : F → G}

/-- The same genuine joint tower retains its pure spatial saving and
its original positive-parameter height factor through a finite kernel. -/
theorem n04PositiveGeometry_finiteKernel_savedSpatial_bound
    (J : SmoothDirections U f) (hV : IsOpen V)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    (Q : SmoothDirections U (g ∘ f))
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (offset : ℕ)
    (x : X) (hx : x ∈ U) (v : Fin n → X)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hinner : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ ≤
        M * parameterHeightWeight H (w.restrict (c.emb i)).stateArity *
          t ^ n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset) :
    ‖Q.D n x v‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) *
      C * M ^ n * L ^ n * parameterHeightWeight H w.stateArity *
        t ^ n04PositiveGeometry_savedSpatialCost w offset :=
  n04PositiveGeometry_finiteKernel_weighted_bound J hV hg hmap Q
    n w.stateArity (n04PositiveGeometry_savedSpatialCost w offset) x hx v
    (fun c i => (w.restrict (c.emb i)).stateArity)
    (fun c i => n04PositiveGeometry_savedSpatialCost (w.restrict (c.emb i)) offset)
    (w.sum_restrict_stateArity)
    (fun c => n04PositiveGeometry_partition_savedSpatial_cost hn w c offset)
    hC hM hH hHL hL ht houter hinner

end ContinuousFlexibility.Analysis
