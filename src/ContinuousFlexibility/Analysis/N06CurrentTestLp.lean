module

public import ContinuousFlexibility.Analysis.N06CurrentChartChange
public import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
public import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual current-coordinate test functions in the original L2 space

The genuine stored inverse is smooth on the closed canonical cylinder.
Continuous physical data therefore have a bounded pullback on its compact
half-period tile. The closed-boundary clauses of N04 give the same result
for the actual height and source transformations. The physical domain may
have a moving cut; its reference radial rectangle is not used as a current
compact domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Continuous data on the actual closed physical tile pull back to L2
through the genuine current inverse chart. The compact bound is allowed
to depend on this piece and this state. -/
theorem n06_inverseChart_comp_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (physicalPieceClosed S K z m)) :
    MemLp (fun p => f (K.inverseChart z m p)) 2 (canonicalMeasure S K m) := by
  apply n06_memLp_canonical_of_continuousOn_closed m
  have hGc : ContinuousOn (K.inverseChart z m)
      (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) := by
    intro p hp
    exact (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m
      ⟨hp.1, mem_univ _⟩).continuousAt.continuousWithinAt
  exact hf.comp hGc (fun p hp =>
    (h04.1.boundary z hz hs m).2.1 ⟨hp.1, mem_univ _⟩)

/-- The actual N04 closed-boundary hypotheses give continuous nonzero
weights on the actual closed physical piece. The Jacobian here is the frozen
Jacobian of the actual current chart, identified with its derivative's
determinant. -/
theorem n06_currentChart_closed_weights
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ContinuousOn (K.height z m)
      (physicalPieceClosed S K z m) ∧
    ContinuousOn (planeJacobian (K.chart z m))
      (physicalPieceClosed S K z m) ∧
    (∀ p ∈ physicalPieceClosed S K z m,
      0 < K.height z m p) ∧
    (∀ p ∈ physicalPieceClosed S K z m,
      planeJacobian (K.chart z m) p ≠ 0) := by
  have hb := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hdet : Continuous (fun f : PolarPoint →L[ℝ] PolarPoint => f.det) :=
    ContinuousLinearMap.continuous_det
  have hd : ContinuousOn (fderiv ℝ (K.chart z m))
      (physicalPieceClosed S K z m) :=
    fun p hp => ((hb p hp).1.continuousAt_fderiv (by simp)).continuousWithinAt
  have heq : planeJacobian (K.chart z m) =
      fun p => (fderiv ℝ (K.chart z m) p).det :=
    funext (n05_planeJacobian_eq_det (K.chart z m))
  refine ⟨fun p hp => (hb p hp).2.1.continuousAt.continuousWithinAt, ?_,
    fun p hp => (hb p hp).2.2.2, fun p hp => (hb p hp).2.2.1⟩
  rw [heq]
  exact hdet.comp_continuousOn hd

/-- The actual current height transform of a physical test belongs to
the same original canonical L2 space, including tests nonzero at either
radial boundary. -/
theorem n06_current_canonicalHeight_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ContinuousOn f
      (physicalPieceClosed S K z m)) :
    MemLp (canonicalHeight S K z m f) 2 (canonicalMeasure S K m) := by
  have hw := n06_currentChart_closed_weights h04 hz hs m
  exact n06_inverseChart_comp_memLp h04 hz hs m
    (hf.div hw.1 (fun p hp => (hw.2.2.1 p hp).ne'))

/-- The genuine current source transform is L2 by the actual positive
height and nonvanishing Jacobian on the closed physical tile. -/
theorem n06_current_canonicalSource_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ContinuousOn f
      (physicalPieceClosed S K z m)) :
    MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m) := by
  have hw := n06_currentChart_closed_weights h04 hz hs m
  exact n06_inverseChart_comp_memLp h04 hz hs m
    ((hw.1.mul hf).div hw.2.1.abs (fun p hp => abs_ne_zero.mpr (hw.2.2.2 p hp)))

/-- In particular, every genuine smooth physical test has both current
transforms in the original L2 space. This fact does not require the test
to be even or to vanish at the piece endpoints. -/
theorem n06_current_canonicalTests_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m) ∧
    MemLp (canonicalSource S K z m φ) 2 (canonicalMeasure S K m) :=
  ⟨n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn,
    n06_current_canonicalSource_memLp h04 hz hs m hφ.continuous.continuousOn⟩

end ContinuousFlexibility.Statements
