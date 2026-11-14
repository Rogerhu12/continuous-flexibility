module

public import ContinuousFlexibility.Analysis.N07bCanonicalSourceEnergy
public import ContinuousFlexibility.Analysis.N05CanonicalTests
public import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity
public import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# Actual square integrability of each canonical source piece

The physical source factor is continuous on the closure of the actual
state-dependent physical domain. The stored boundary inverse germ gives
continuity of the actual inverse on the closed canonical cylinder.
Consequently the actual source is bounded on one compact canonical
fundamental rectangle and belongs to the prescribed piece's L² space.

No physical domain is assumed to be a rectangle or compact. The bound may
depend on the piece and state; no uniform material estimate or global
summability is asserted here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hK hz hsector

/-- The physical source factor is continuous on the actual closed domain. -/
theorem n07b_continuousOn_physicalSourceFactor (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (physicalPieceClosed S K z m)) :
    ContinuousOn
      (fun p => K.height z m p * f p / |planeJacobian (K.chart z m) p|)
      (physicalPieceClosed S K z m) := by
  intro p hp
  have hclosed := (hK.boundary z hz hsector m).2.2.2.2.1 p hp
  have hJ := ContinuousFlexibility.contDiffAt_planeJacobian hclosed.1
  exact (hclosed.2.1.continuousAt.continuousWithinAt.mul (hf p hp)).div
    hJ.continuousAt.abs.continuousWithinAt (abs_ne_zero.mpr hclosed.2.2.1)

/-- The actual closed inverse transports continuity to the whole closed
canonical cylinder, including both radial boundary circles. -/
theorem n07b_continuousOn_canonicalSource_closed (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (physicalPieceClosed S K z m)) :
    ContinuousOn (canonicalSource S K z m f) (canonicalClosed S K m) := by
  have hG : ContinuousOn (K.inverseChart z m) (canonicalClosed S K m) := by
    intro p hp
    exact (n04b_inverseChart_contDiffAt_closed hK hz hsector m hp).continuousAt.continuousWithinAt
  change ContinuousOn
    ((fun x => K.height z m x * f x / |planeJacobian (K.chart z m) x|) ∘
      K.inverseChart z m) (canonicalClosed S K m)
  exact (n07b_continuousOn_physicalSourceFactor hK hz hsector m hf).comp hG
    (hK.boundary z hz hsector m).2.1

/-- In particular the actual source conversion is continuous on its open
canonical piece. -/
theorem n07b_continuousOn_canonicalSource (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (physicalPieceClosed S K z m)) :
    ContinuousOn (canonicalSource S K z m f) (canonicalOpen S K m) :=
  (n07b_continuousOn_canonicalSource_closed hK hz hsector m hf).mono
    (fun _ hp => ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩)

/-- Every fixed canonical piece of a continuous physical source is an
actual L² function. Compactness is used only in canonical coordinates. -/
theorem n07b_canonicalSource_memLp (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (physicalPieceClosed S K z m)) :
    MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m) := by
  have hg : ContinuousOn (canonicalSource S K z m f)
      (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    (n07b_continuousOn_canonicalSource_closed hK hz hsector m hf).mono
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hcompact : IsCompact
      (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hg.norm
  have hmeas : AEStronglyMeasurable (canonicalSource S K z m f)
      (canonicalMeasure S K m) := by
    apply ((n07b_continuousOn_canonicalSource_closed hK hz hsector m hf).mono
      (fun p (hp : p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) =>
        show p ∈ canonicalClosed S K m from
          ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩)).aestronglyMeasurable
    exact measurableSet_Ioo.prod measurableSet_Ioc
  refine MemLp.of_bound hmeas B ?_
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [ha] with p hp
  exact hB ⟨p, ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2⟩⟩, rfl⟩

/-- Globally continuous physical data satisfy the actual closed-domain
input with no change to the source formula. -/
theorem n07b_canonicalSource_memLp_of_continuous (m : ℕ) {f : PolarPoint → ℝ}
    (hf : Continuous f) :
    MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m) :=
  n07b_canonicalSource_memLp hK hz hsector m hf.continuousOn

end ContinuousFlexibility.Analysis
