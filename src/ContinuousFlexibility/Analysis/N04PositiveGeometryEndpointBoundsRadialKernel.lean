module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsAngularKernel
public import ContinuousFlexibility.Analysis.N06RootAbsorbedPacket

/-!
# The exact finite radial prolongation of the normalized root kernel

Each spatial partition is a smooth finite-dimensional function of the
actual value and radial input jets. The finite low-order state bound
places that entire tuple in a fixed compact set. Thus all derivatives
of the radial kernel have uniform constants before the root, state and
angular order are evaluated. No derivative of a selected root chart is
an input to this construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

abbrev N04RootRadialPacket (n : ℕ) := (Fin (n + 1) × Fin 6) → ℝ

/-- A spatial partition term, with its actual normalized root formula. -/
def n04PositiveGeometry_rootRadialKernel (n : ℕ) (v : N04RootRadialPacket n) : PolarPoint :=
  iteratedFDeriv ℝ n n06RootNormalizedFields (fun j => v (0, j))
    (fun i j => v (i.succ, j))

def n04PositiveGeometry_rootRadialKernelDomain (n : ℕ) : Set (N04RootRadialPacket n) :=
  {v | 0 < n06RootNormalizedQ (fun j => v (0, j)) ∧
    0 < n06RootNormalizedDiscriminant (fun j => v (0, j))}

theorem n04PositiveGeometry_rootRadialKernelDomain_open (n : ℕ) :
    IsOpen (n04PositiveGeometry_rootRadialKernelDomain n) := by
  have hrow : Continuous (fun v : N04RootRadialPacket n => fun j => v (0, j)) :=
    continuous_pi (fun j => continuous_apply (0, j))
  exact (isOpen_lt continuous_const
    (n06RootNormalizedQ_contDiff.continuous.comp hrow)).inter
    (isOpen_lt continuous_const
      (n06RootNormalizedDiscriminant_contDiff.continuous.comp hrow))

theorem n04PositiveGeometry_rootRadialKernel_contDiff (n : ℕ) :
    ContDiffOn ℝ ∞ (n04PositiveGeometry_rootRadialKernel n)
      (n04PositiveGeometry_rootRadialKernelDomain n) := by
  intro v hv
  have hrow : ContDiffAt ℝ ∞
      (fun y : N04RootRadialPacket n => fun j => y (0, j)) v :=
    contDiffAt_pi.mpr (fun j => contDiffAt_apply ℝ ℝ (0, j) v)
  have htail : ContDiffAt ℝ ∞
      (fun y : N04RootRadialPacket n => fun i : Fin n => fun j : Fin 6 => y (i.succ, j)) v :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr
      (fun j => contDiffAt_apply ℝ ℝ (i.succ, j) v))
  have houter : ContDiffAt ℝ ∞
      (fun y : N04RootRadialPacket n =>
        iteratedFDeriv ℝ n n06RootNormalizedFields (fun j => y (0, j))) v :=
    ((n06RootNormalizedFields_contDiffAt hv.1.ne' hv.2).iteratedFDeriv_right
      (by simp)).comp v hrow
  exact ((contDiff_multilinearEvaluation (Y := N06RootNormalizedCoordinates)
    (Z := PolarPoint) n).contDiffAt.comp v (houter.prodMk htail)).contDiffWithinAt

/-- Compact bounds on all outer derivatives of one actual radial
partition term. Both root denominator lower bounds stay explicit. -/
theorem n04PositiveGeometry_rootRadialKernel_finite_bound (n k : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j, j ≤ k → ∀ v : N04RootRadialPacket n,
      ‖v‖ ≤ B → (7 / 8 : ℝ) ≤ n06RootNormalizedQ (fun i => v (0, i)) →
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant (fun i => v (0, i)) →
        ‖iteratedFDeriv ℝ j (n04PositiveGeometry_rootRadialKernel n) v‖ ≤ C := by
  let K : Set (N04RootRadialPacket n) := Metric.closedBall 0 B ∩
    ({v | (7 / 8 : ℝ) ≤ n06RootNormalizedQ (fun i => v (0, i))} ∩
      {v | (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant (fun i => v (0, i))})
  have hrow : Continuous (fun v : N04RootRadialPacket n => fun j => v (0, j)) :=
    continuous_pi (fun j => continuous_apply (0, j))
  have hK : IsCompact K := (isCompact_closedBall (0 : N04RootRadialPacket n) B).inter_right
    ((isClosed_le continuous_const (n06RootNormalizedQ_contDiff.continuous.comp hrow)).inter
      (isClosed_le continuous_const
        (n06RootNormalizedDiscriminant_contDiff.continuous.comp hrow)))
  have hs : ∀ v ∈ K, ContDiffAt ℝ ∞ (n04PositiveGeometry_rootRadialKernel n) v := by
    intro v hv
    apply (n04PositiveGeometry_rootRadialKernel_contDiff n).contDiffAt
    apply (n04PositiveGeometry_rootRadialKernelDomain_open n).mem_nhds
    exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hv.2.1,
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hv.2.2⟩
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_bound hK hs k
  refine ⟨C, hC, fun j hj v hv hQ hD => hbound j hj v ?_⟩
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hQ, hD⟩

/-- The packet contains the actual input value and the actual radial
jets selected by a spatial partition. -/
def n04PositiveGeometry_rootRadialPacket {n : ℕ} (c : OrderedFinpartition n)
    (u : PolarPoint → N06RootNormalizedCoordinates) (p e : PolarPoint) :
    N04RootRadialPacket c.length := fun ij =>
  (Fin.cons (α := fun _ : Fin (c.length + 1) => N06RootNormalizedCoordinates)
    (u p) (fun i => iteratedFDeriv ℝ (c.partSize i) u p
    (fun _ => e))) ij.1 ij.2

theorem n04PositiveGeometry_rootRadialPacket_norm_le {n : ℕ}
    (c : OrderedFinpartition n) (u : PolarPoint → N06RootNormalizedCoordinates)
    (p e : PolarPoint) {M : ℝ} (hM : 0 ≤ M) (he : ‖e‖ ≤ 1)
    (hinput : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j u p‖ ≤ M) :
    ‖n04PositiveGeometry_rootRadialPacket c u p e‖ ≤ M := by
  have hval : ‖u p‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hinput 0 (Nat.zero_le n)
  have hjet (i : Fin c.length) :
      ‖iteratedFDeriv ℝ (c.partSize i) u p (fun _ => e)‖ ≤ M := by
    have hp : (∏ _j : Fin (c.partSize i), ‖e‖) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => he)
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right (hinput (c.partSize i) (c.partSize_le i))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans
        ((mul_le_mul_of_nonneg_left hp hM).trans_eq (mul_one _)))
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro ij
  dsimp only [n04PositiveGeometry_rootRadialPacket]
  refine Fin.cases ?_ (fun i => ?_) ij.1
  · exact ((pi_norm_le_iff_of_nonneg hM).mp hval) ij.2
  · exact ((pi_norm_le_iff_of_nonneg hM).mp (hjet i)) ij.2

/-- The ordinary chain rule identifies each genuine radial derivative
with these same finite kernel evaluations, on the local positive locus. -/
theorem n04PositiveGeometry_rootRadialKernel_formula
    (u : PolarPoint → N06RootNormalizedCoordinates) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (p e : PolarPoint)
    (hQ : 0 < n06RootNormalizedQ (u p))
    (hD : 0 < n06RootNormalizedDiscriminant (u p)) :
    iteratedFDeriv ℝ n (fun q => n06RootNormalizedFields (u q)) p (fun _ => e) =
      ∑ c : OrderedFinpartition n, n04PositiveGeometry_rootRadialKernel c.length
        (n04PositiveGeometry_rootRadialPacket c u p e) := by
  let V : Set N06RootNormalizedCoordinates :=
    {v | 0 < n06RootNormalizedQ v ∧ 0 < n06RootNormalizedDiscriminant v}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const n06RootNormalizedQ_contDiff.continuous).inter
      (isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous)
  have hg : ContDiffOn ℝ ∞ n06RootNormalizedFields V :=
    fun v hv => (n06RootNormalizedFields_contDiffAt hv.1.ne' hv.2).contDiffWithinAt
  have hf := iteratedFDeriv_comp_ordered_apply (hV.preimage hu.continuous) hV
    hu.contDiffOn hg (fun _ h => h) n (show p ∈ u ⁻¹' V from ⟨hQ, hD⟩)
    (fun _ => e)
  simpa only [Function.comp_def, n04PositiveGeometry_rootRadialKernel,
    n04PositiveGeometry_rootRadialPacket, Fin.cons_zero, Fin.cons_succ] using hf

end ContinuousFlexibility.Analysis
