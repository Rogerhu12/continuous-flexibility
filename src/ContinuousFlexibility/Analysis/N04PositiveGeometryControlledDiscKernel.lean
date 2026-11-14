import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsSpatialKernel

/-!
# Finite spatial kernels for powers of the actual root discriminant

Only positivity of the discriminant is needed for this scalar kernel.
The packet radius in the compact estimate is fixed before its future
outer derivative order. The actual input bound supplies that radius at
one fixed low parameter order; no polynomial dependence on a varying
compact radius is asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_rootDiscPower (γ : ℝ)
    (v : N06RootNormalizedCoordinates) : ℝ :=
  n06RootNormalizedDiscriminant v ^ γ

theorem n04PositiveGeometry_rootDiscPower_contDiffAt (γ : ℝ)
    {v : N06RootNormalizedCoordinates} (hD : 0 < n06RootNormalizedDiscriminant v) :
    ContDiffAt ℝ ∞ (n04PositiveGeometry_rootDiscPower γ) v :=
  n06RootNormalizedDiscriminant_contDiff.contDiffAt.rpow_const_of_ne hD.ne'

/-- The same finite spatial packet as for the physical root fields,
with the scalar discriminant power as its outer function. -/
def n04PositiveGeometry_rootDiscKernel (γ : ℝ) (n : ℕ)
    (v : N04RootRadialPacket n) : ℝ :=
  iteratedFDeriv ℝ n (n04PositiveGeometry_rootDiscPower γ) (fun j => v (0, j))
    (fun i j => v (i.succ, j))

def n04PositiveGeometry_rootDiscKernelDomain (n : ℕ) : Set (N04RootRadialPacket n) :=
  {v | 0 < n06RootNormalizedDiscriminant (fun j => v (0, j))}

theorem n04PositiveGeometry_rootDiscKernelDomain_open (n : ℕ) :
    IsOpen (n04PositiveGeometry_rootDiscKernelDomain n) := by
  have hrow : Continuous (fun v : N04RootRadialPacket n => fun j => v (0, j)) :=
    continuous_pi (fun j => continuous_apply (0, j))
  exact isOpen_lt continuous_const
    (n06RootNormalizedDiscriminant_contDiff.continuous.comp hrow)

theorem n04PositiveGeometry_rootDiscKernel_contDiff (γ : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (n04PositiveGeometry_rootDiscKernel γ n)
      (n04PositiveGeometry_rootDiscKernelDomain n) := by
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
        iteratedFDeriv ℝ n (n04PositiveGeometry_rootDiscPower γ) (fun j => y (0, j))) v :=
    ((n04PositiveGeometry_rootDiscPower_contDiffAt γ hv).iteratedFDeriv_right
      (by simp)).comp v hrow
  exact ((contDiff_multilinearEvaluation (Y := N06RootNormalizedCoordinates)
    (Z := ℝ) n).contDiffAt.comp v (houter.prodMk htail)).contDiffWithinAt

/-- Every ordinary outer derivative through a fixed order has a
uniform bound on the fixed packet ball with the actual lower bound. -/
theorem n04PositiveGeometry_rootDiscKernel_finite_bound (γ : ℝ) (n k : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j, j ≤ k → ∀ v : N04RootRadialPacket n,
      ‖v‖ ≤ B → (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant (fun i => v (0, i)) →
        ‖iteratedFDeriv ℝ j (n04PositiveGeometry_rootDiscKernel γ n) v‖ ≤ C := by
  let K : Set (N04RootRadialPacket n) := Metric.closedBall 0 B ∩
    {v | (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant (fun i => v (0, i))}
  have hrow : Continuous (fun v : N04RootRadialPacket n => fun j => v (0, j)) :=
    continuous_pi (fun j => continuous_apply (0, j))
  have hK : IsCompact K := (isCompact_closedBall (0 : N04RootRadialPacket n) B).inter_right
    (isClosed_le continuous_const
      (n06RootNormalizedDiscriminant_contDiff.continuous.comp hrow))
  have hs : ∀ v ∈ K, ContDiffAt ℝ ∞ (n04PositiveGeometry_rootDiscKernel γ n) v := by
    intro v hv
    apply (n04PositiveGeometry_rootDiscKernel_contDiff γ n).contDiffAt
    apply (n04PositiveGeometry_rootDiscKernelDomain_open n).mem_nhds
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hv.2
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_bound hK hs k
  refine ⟨C, hC, fun j hj v hv hD => hbound j hj v ?_⟩
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hD⟩

/-- The genuine spatial chain rule, with every block using its
original direction family. -/
theorem n04PositiveGeometry_rootDiscKernel_formula (γ : ℝ)
    (u : PolarPoint → N06RootNormalizedCoordinates) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (p : PolarPoint) (v : Fin n → PolarPoint)
    (hD : 0 < n06RootNormalizedDiscriminant (u p)) :
    iteratedFDeriv ℝ n (fun q => n04PositiveGeometry_rootDiscPower γ (u q)) p v =
      ∑ c : OrderedFinpartition n, n04PositiveGeometry_rootDiscKernel γ c.length
        (n04PositiveGeometry_rootSpatialPacket c u p v) := by
  let V : Set N06RootNormalizedCoordinates := {v | 0 < n06RootNormalizedDiscriminant v}
  have hV : IsOpen V :=
    isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous
  have hg : ContDiffOn ℝ ∞ (n04PositiveGeometry_rootDiscPower γ) V :=
    fun v hv => (n04PositiveGeometry_rootDiscPower_contDiffAt γ hv).contDiffWithinAt
  have hf := iteratedFDeriv_comp_ordered_apply (hV.preimage hu.continuous) hV
    hu.contDiffOn hg (fun _ h => h) n (show p ∈ u ⁻¹' V from hD) v
  refine hf.trans ?_
  apply Finset.sum_congr rfl
  intro c _
  rfl

end ContinuousFlexibility.Analysis
