import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRadialKernel
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# The finite root kernel for the original mixed spatial word

Radial and intrinsic angular derivatives are taken before the parameter
and additional angular slots. Each spatial partition records its actual
two coordinate counts. This prevents a fixed intrinsic angular loss
from being paid again for every future angular derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_rootSpatialPacket {n : ℕ} (c : OrderedFinpartition n)
    (u : PolarPoint → N06RootNormalizedCoordinates) (p : PolarPoint)
    (v : Fin n → PolarPoint) : N04RootRadialPacket c.length := fun ij =>
  (Fin.cons (α := fun _ : Fin (c.length + 1) => N06RootNormalizedCoordinates)
    (u p) (fun j => iteratedFDeriv ℝ (c.partSize j) u p (v ∘ c.emb j))) ij.1 ij.2

def n04PositiveGeometry_rootPartitionRadialOrder {n : ℕ} (c : OrderedFinpartition n)
    (w : Fin n → Fin 2) : Fin (c.length + 1) → ℕ :=
  Fin.cons 0 (fun j => ∑ t : Fin (c.partSize j), if w (c.emb j t) = 0 then 1 else 0)

def n04PositiveGeometry_rootPartitionAngularOrder {n : ℕ} (c : OrderedFinpartition n)
    (w : Fin n → Fin 2) : Fin (c.length + 1) → ℕ :=
  Fin.cons 0 (fun j => ∑ t : Fin (c.partSize j), if w (c.emb j t) = 0 then 0 else 1)

theorem n04PositiveGeometry_rootPartition_orders_le {n : ℕ} (c : OrderedFinpartition n)
    (w : Fin n → Fin 2) (j : Fin (c.length + 1)) :
    n04PositiveGeometry_rootPartitionRadialOrder c w j +
      n04PositiveGeometry_rootPartitionAngularOrder c w j ≤ n := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact Nat.zero_le n
  · change (∑ t : Fin (c.partSize i), if w (c.emb i t) = 0 then 1 else 0) +
      (∑ t : Fin (c.partSize i), if w (c.emb i t) = 0 then 0 else 1) ≤ n
    rw [← Finset.sum_add_distrib]
    have he (t : Fin (c.partSize i)) :
        (if w (c.emb i t) = 0 then (1 : ℕ) else 0) +
          (if w (c.emb i t) = 0 then 0 else 1) = 1 := by split_ifs <;> rfl
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact c.partSize_le i

/-- Each scalar row is an actual mixed derivative, with the counts of
the original partition block and without any reordering hypothesis. -/
theorem n04PositiveGeometry_rootSpatialPacket_mixed {n : ℕ}
    (c : OrderedFinpartition n) (u : PolarPoint → N06RootNormalizedCoordinates)
    (hu : ContDiff ℝ ∞ u) (p : PolarPoint) (w : Fin n → Fin 2)
    (ij : Fin (c.length + 1) × Fin 6) :
    n04PositiveGeometry_rootSpatialPacket c u p (fun t => cylinderBasisVector (w t)) ij =
      mixedDerivative (n04PositiveGeometry_rootPartitionRadialOrder c w ij.1)
        (n04PositiveGeometry_rootPartitionAngularOrder c w ij.1)
        (fun q => u q ij.2) p := by
  dsimp only [n04PositiveGeometry_rootSpatialPacket,
    n04PositiveGeometry_rootPartitionRadialOrder, n04PositiveGeometry_rootPartitionAngularOrder]
  refine Fin.cases ?_ (fun j => ?_) ij.1
  · simp only [n04PositiveGeometry_rootSpatialPacket,
      n04PositiveGeometry_rootPartitionRadialOrder, n04PositiveGeometry_rootPartitionAngularOrder,
      Fin.cons_zero, mixedDerivative, iteratedDeriv_zero]
  · change (iteratedFDeriv ℝ (c.partSize j) u p
        ((fun t => cylinderBasisVector (w t)) ∘ c.emb j)) ij.2 = _
    have he := congrArg
      (fun A : PolarPoint [×c.partSize j]→L[ℝ] ℝ =>
        A ((fun t => cylinderBasisVector (w t)) ∘ c.emb j))
      ((ContinuousLinearMap.proj ij.2 : N06RootNormalizedCoordinates →L[ℝ] ℝ)
        .iteratedFDeriv_comp_left hu.contDiffAt (i := c.partSize j) (by simp))
    change iteratedFDeriv ℝ (c.partSize j) (fun q => u q ij.2) p
        ((fun t => cylinderBasisVector (w t)) ∘ c.emb j) =
      (iteratedFDeriv ℝ (c.partSize j) u p
        ((fun t => cylinderBasisVector (w t)) ∘ c.emb j)) ij.2 at he
    apply he.symm.trans
    exact iteratedFDeriv_cylinderBasis_eq_mixedDerivative isOpen_univ
      ((contDiff_apply ℝ ℝ ij.2).comp hu).contDiffOn (c.partSize j) (mem_univ p)
      (w ∘ c.emb j)

theorem n04PositiveGeometry_rootSpatialPacket_norm_le {n : ℕ}
    (c : OrderedFinpartition n) (u : PolarPoint → N06RootNormalizedCoordinates)
    (p : PolarPoint) (v : Fin n → PolarPoint) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ j, ‖v j‖ ≤ 1)
    (hinput : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j u p‖ ≤ M) :
    ‖n04PositiveGeometry_rootSpatialPacket c u p v‖ ≤ M := by
  have hval : ‖u p‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hinput 0 (Nat.zero_le n)
  have hjet (j : Fin c.length) :
      ‖iteratedFDeriv ℝ (c.partSize j) u p (v ∘ c.emb j)‖ ≤ M := by
    have hp : (∏ t : Fin (c.partSize j), ‖v (c.emb j t)‖) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun t _ => hv (c.emb j t))
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right (hinput (c.partSize j) (c.partSize_le j))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans
        ((mul_le_mul_of_nonneg_left hp hM).trans_eq (mul_one _)))
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro ij
  dsimp only [n04PositiveGeometry_rootSpatialPacket]
  refine Fin.cases ?_ (fun j => ?_) ij.1
  · exact ((pi_norm_le_iff_of_nonneg hM).mp hval) ij.2
  · exact ((pi_norm_le_iff_of_nonneg hM).mp (hjet j)) ij.2

/-- The genuine Faà di Bruno identity for an arbitrary original
spatial word, on the local positive normalized locus. -/
theorem n04PositiveGeometry_rootSpatialKernel_formula
    (u : PolarPoint → N06RootNormalizedCoordinates) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (p : PolarPoint) (v : Fin n → PolarPoint)
    (hQ : 0 < n06RootNormalizedQ (u p))
    (hD : 0 < n06RootNormalizedDiscriminant (u p)) :
    iteratedFDeriv ℝ n (fun q => n06RootNormalizedFields (u q)) p v =
      ∑ c : OrderedFinpartition n, n04PositiveGeometry_rootRadialKernel c.length
        (n04PositiveGeometry_rootSpatialPacket c u p v) := by
  let V : Set N06RootNormalizedCoordinates :=
    {v | 0 < n06RootNormalizedQ v ∧ 0 < n06RootNormalizedDiscriminant v}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const n06RootNormalizedQ_contDiff.continuous).inter
      (isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous)
  have hg : ContDiffOn ℝ ∞ n06RootNormalizedFields V :=
    fun v hv => (n06RootNormalizedFields_contDiffAt hv.1.ne' hv.2).contDiffWithinAt
  have hf := iteratedFDeriv_comp_ordered_apply (hV.preimage hu.continuous) hV
    hu.contDiffOn hg (fun _ h => h) n (show p ∈ u ⁻¹' V from ⟨hQ, hD⟩) v
  simpa only [n04PositiveGeometry_rootRadialKernel, n04PositiveGeometry_rootSpatialPacket,
    Fin.cons_zero, Fin.cons_succ] using hf

end ContinuousFlexibility.Analysis
