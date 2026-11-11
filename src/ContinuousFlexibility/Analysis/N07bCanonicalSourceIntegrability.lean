import ContinuousFlexibility.Analysis.N07bCanonicalSourceEnergy
import ContinuousFlexibility.Analysis.N05CanonicalTests

/-!
# Actual square integrability of each canonical source piece

PartA gives a smooth chart and height, with nonzero Jacobian, at every
point of the physical closed piece. A continuous physical source therefore
makes its physical source factor bounded on the compact fundamental
rectangle. The actual chart image identifies its canonical pullback on a
full-measure open rectangle.

This proves genuine piecewise L² membership. The bound may depend on the
piece and the state; no uniform material estimate or global summability
is asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- Smoothness of the actual Jacobian follows from the actual derivative. -/
theorem n07b_contDiffAt_planeJacobian
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (planeJacobian F) p := by
  have hr : ContDiffAt ℝ ∞ (fun x => fderiv ℝ F x (1, 0)) p :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (fun x => fderiv ℝ F x (0, 1)) p :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  exact (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hK hz hsector

/-- The physical source factor is continuous through both radial endpoints. -/
theorem n07b_continuousOn_physicalSourceFactor (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ univ)) :
    ContinuousOn
      (fun p => K.height z m p * f p / |planeJacobian (K.chart z m) p|)
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ univ) := by
  intro p hp
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hsector m p hp.1
  have hJ := n07b_contDiffAt_planeJacobian hclosed.1
  exact (hclosed.2.1.continuousAt.continuousWithinAt.mul (hf p hp)).div
    hJ.continuousAt.abs.continuousWithinAt (abs_ne_zero.mpr hclosed.2.2.1)

/-- Continuity of the given inverse on the canonical interior gives
continuity of the actual source conversion there. -/
theorem n07b_continuousOn_canonicalSource (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ univ)) :
    ContinuousOn (canonicalSource S K z m f) (canonicalOpen S K m) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hmap : MapsTo (K.inverseChart z m) (canonicalOpen S K m)
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ univ) := by
    intro p hp
    have hx := hcharts.2.1 hp
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, mem_univ _⟩
  have h := (n07b_continuousOn_physicalSourceFactor hK hz hsector m hf).comp
    hcharts.2.2.2.2.2.1.continuousOn hmap
  simpa only [canonicalSource, Function.comp_def] using h

/-- Every fixed canonical piece of a continuous physical source is an
actual L² function. No uniform bound in `m` or `z` is used. -/
theorem n07b_canonicalSource_memLp (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ univ)) :
    MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m) := by
  let g : PolarPoint → ℝ := fun p =>
    K.height z m p * f p / |planeJacobian (K.chart z m) p|
  have hg : ContinuousOn g
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    (n07b_continuousOn_physicalSourceFactor hK hz hsector m hf).mono
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hcompact : IsCompact
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hg.norm
  have hmeas : AEStronglyMeasurable (canonicalSource S K z m f)
      (canonicalMeasure S K m) := by
    apply ((n07b_continuousOn_canonicalSource hK hz hsector m hf).mono
      (fun p (hp : p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) =>
        show p ∈ canonicalOpen S K m from ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
    exact measurableSet_Ioo.prod measurableSet_Ioc
  refine MemLp.of_bound hmeas B ?_
  have hmeasure : canonicalMeasure S K m =
      volume.restrict (Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi) :=
    Measure.restrict_congr_set
      (polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi)
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi := by
    rw [hmeasure]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have himage := canonicalChart_image_openStrip hK hz hsector m
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  filter_upwards [ha] with p hp
  have hpin : p ∈ canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi) :=
    ⟨⟨hp.1, mem_univ _⟩, ⟨mem_univ _, hp.2⟩⟩
  rw [← himage] at hpin
  obtain ⟨x, hx, hxp⟩ := hpin
  have hinv : K.inverseChart z m p = x := by
    rw [← hxp]
    exact hcharts.2.2.1 x hx.1
  change ‖g (K.inverseChart z m p)‖ ≤ B
  rw [hinv]
  exact hB ⟨x, ⟨⟨hx.1.1.1.le, hx.1.1.2.le⟩,
    ⟨hx.2.2.1.le, hx.2.2.2.le⟩⟩, rfl⟩

/-- In particular, the actual canonical L² class exists for every globally
continuous physical source. -/
theorem n07b_canonicalSource_memLp_of_continuous (m : ℕ) {f : PolarPoint → ℝ}
    (hf : Continuous f) :
    MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m) :=
  n07b_canonicalSource_memLp hK hz hsector m hf.continuousOn

end ContinuousFlexibility.Analysis
