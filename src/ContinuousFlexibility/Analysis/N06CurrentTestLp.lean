import ContinuousFlexibility.Analysis.N06CurrentChartChange
import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual current-coordinate test functions in the original L2 space

The current inverse chart maps the measured half-period cylinder into the
corresponding physical half-period rectangle. A function continuous on the
closed physical rectangle is bounded there, so its actual pullback belongs
to the original canonical L2 space. The closed-boundary clauses of N04 give
the same conclusion for the genuine height and source transformations:
the height is positive and the actual Jacobian does not vanish on that
compact rectangle. No angular identity, uniform piecewise bound, or prior
L2 hypothesis on the transformed test is required.
-/

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
    (hf : ContinuousOn f
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)) :
    MemLp (fun p => f (K.inverseChart z m p)) 2 (canonicalMeasure S K m) := by
  let Q : Set PolarPoint :=
    Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi
  let R : Set PolarPoint :=
    Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hm := (n06_canonicalChart_halfPeriod_maps h04 hz hs m).2
  have hmap : MapsTo (K.inverseChart z m) R Q := by
    intro p hp
    have hx := hm hp
    exact ⟨mem_Icc_of_Ioo hx.1, hx.2.1.le, hx.2.2⟩
  have hsub : R ⊆ canonicalOpen S K m := fun _ hp => ⟨hp.1, mem_univ _⟩
  have hc := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hGc : ContinuousOn (K.inverseChart z m) R :=
    hc.2.2.2.2.2.1.continuousOn.mono hsub
  have hcomp : ContinuousOn (fun p => f (K.inverseChart z m p)) R :=
    hf.comp hGc hmap
  have hmeas : AEStronglyMeasurable (fun p => f (K.inverseChart z m p))
      (canonicalMeasure S K m) :=
    hcomp.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
  obtain ⟨M, hM⟩ := hQ.bddAbove_image hf.norm
  have hconst : MemLp (fun _ : PolarPoint => M) 2 (canonicalMeasure S K m) :=
    n06_memLp_canonical_of_continuous m continuous_const
  apply hconst.of_le hmeas
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact (hM ⟨K.inverseChart z m p, hmap hp, rfl⟩).trans
    (by simpa only [Real.norm_eq_abs] using le_abs_self M)

/-- The actual N04 closed-boundary hypotheses give continuous nonzero
weights on the physical compact tile. The Jacobian here is the frozen
Jacobian of the actual current chart, identified with its derivative's
determinant. -/
theorem n06_currentChart_closed_weights
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ContinuousOn (K.height z m)
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi) ∧
    ContinuousOn (planeJacobian (K.chart z m))
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi) ∧
    (∀ p ∈ Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi,
      0 < K.height z m p) ∧
    (∀ p ∈ Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi,
      planeJacobian (K.chart z m) p ≠ 0) := by
  have hb := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  have hdet : Continuous (fun f : PolarPoint →L[ℝ] PolarPoint => f.det) :=
    ContinuousLinearMap.continuous_det
  have hd : ContinuousOn (fderiv ℝ (K.chart z m))
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    fun p hp => ((hb p hp.1).1.continuousAt_fderiv (by simp)).continuousWithinAt
  have heq : planeJacobian (K.chart z m) =
      fun p => (fderiv ℝ (K.chart z m) p).det :=
    funext (n05_planeJacobian_eq_det (K.chart z m))
  refine ⟨fun p hp => (hb p hp.1).2.1.continuousAt.continuousWithinAt, ?_,
    fun p hp => (hb p hp.1).2.2.2, fun p hp => (hb p hp.1).2.2.1⟩
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
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)) :
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
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)) :
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
