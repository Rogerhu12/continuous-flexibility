import ContinuousFlexibility.Analysis.N07bCanonicalSourceIntegrability
import ContinuousFlexibility.Analysis.N07bCompactLocalBounds
import ContinuousFlexibility.Analysis.CanonicalInteriorInverse
import ContinuousFlexibility.Analysis.PointwiseCylinderJets
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual canonical source jets on a single piece

At a physical endpoint the prescribed inverse is used only on the
canonical interior. The actual inverse function theorem supplies a smooth
local inverse agreeing there with the prescribed inverse. Each actual jet
therefore has a local bound pulled back to the physical closed piece.
Compactness of one fundamental physical rectangle gives a bound for that
piece, and hence actual L² membership of every canonical mixed jet.

No estimate uniform in the piece or state, and no global summability, is
claimed in this module.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hK hz hsector

/-- The physical source factor is smooth at every closed-piece point where
the physical source itself is smooth. -/
theorem n07b_contDiffAt_physicalSourceFactor (m : ℕ)
    {f : PolarPoint → ℝ} {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (hf : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞
      (fun x => K.height z m x * f x / |planeJacobian (K.chart z m) x|) p := by
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hsector m p hp
  have hJ := ContinuousFlexibility.contDiffAt_planeJacobian hclosed.1
  exact (hclosed.2.1.mul hf).div (hJ.abs hclosed.2.2.1)
    (abs_ne_zero.mpr hclosed.2.2.1)

/-- The actual prescribed source conversion is smooth on its canonical
open piece. Only pointwise physical smoothness on the closed strip is used. -/
theorem n07b_contDiffOn_canonicalSource (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint,
      p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) → ContDiffAt ℝ ∞ f p) :
    ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  intro p hp
  have hx := hcharts.2.1 hp
  have hxclosed : (K.inverseChart z m p).1 ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := ⟨hx.1.1.le, hx.1.2.le⟩
  have hraw := n07b_contDiffAt_physicalSourceFactor hK hz hsector m
    hxclosed (hf _ hxclosed)
  have hinv : ContDiffAt ℝ ∞ (K.inverseChart z m) p :=
    hcharts.2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  simpa only [canonicalSource, Function.comp_def] using
    (hraw.comp p hinv).contDiffWithinAt (s := canonicalOpen S K m)

/-- Every finite actual mixed jet has an interior bound near each physical
closed-piece point. This statement never evaluates the prescribed inverse
at a canonical endpoint. -/
theorem n07b_canonicalSource_mixedDerivative_local_bound
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint,
      p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) → ContDiffAt ℝ ∞ f p)
    (a b : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    ∃ B : ℝ, ∀ᶠ x in 𝓝 p, x ∈ physicalPieceOpen S K m →
      ‖mixedDerivative a b (canonicalSource S K z m f) (K.chart z m x)‖ ≤ B := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hsector m p hp
  obtain ⟨e, δ, he, hpe, heSmooth, hδ, htarget, hlocal, heq⟩ :=
    canonicalChart_exists_smooth_interiorInverse hK hz hsector m p hp
  let g₀ : PolarPoint → ℝ := fun x =>
    K.height z m x * f x / |planeJacobian (K.chart z m) x|
  let g : PolarPoint → ℝ := g₀ ∘ e.symm
  have hinvp : e.symm (K.chart z m p) = p := by
    rw [← he]
    exact e.left_inv hpe
  have hg₀ : ContDiffAt ℝ ∞ g₀ (e.symm (K.chart z m p)) := by
    rw [hinvp]
    exact n07b_contDiffAt_physicalSourceFactor hK hz hsector m hp (hf p hp)
  have hg : ContDiffAt ℝ ∞ g (K.chart z m p) := hg₀.comp _ heSmooth
  have hjet : ContinuousAt (mixedDerivative a b g) (K.chart z m p) :=
    (contDiffAt_mixedDerivative hg a b).continuousAt
  let B := ‖mixedDerivative a b g (K.chart z m p)‖ + 1
  have hbound : ∀ᶠ q in 𝓝 (K.chart z m p), ‖mixedDerivative a b g q‖ ≤ B :=
    hjet.norm.eventually_le_const (lt_add_one _)
  have hnear : ∀ᶠ x in 𝓝 p,
      K.chart z m x ∈ Metric.ball (K.chart z m p) δ :=
    hclosed.1.continuousAt.eventually (Metric.ball_mem_nhds _ hδ)
  have hcompose : ∀ᶠ x in 𝓝 p,
      ‖mixedDerivative a b g (K.chart z m x)‖ ≤ B :=
    hclosed.1.continuousAt.eventually hbound
  have hsame : EqOn (canonicalSource S K z m f) g
      (Metric.ball (K.chart z m p) δ ∩ canonicalOpen S K m) := by
    intro q hq
    change g₀ (K.inverseChart z m q) = g₀ (e.symm q)
    rw [heq hq]
  have hjetsame := mixedDerivative_eqOn_of_isOpen
    (Metric.isOpen_ball.inter (isOpen_Ioo.prod isOpen_univ)) hsame a b
  refine ⟨B, ?_⟩
  filter_upwards [hnear, hcompose] with x hx hboundx
  intro hxopen
  rw [hjetsame ⟨hx, hcharts.1 hxopen⟩]
  exact hboundx

/-- Compactness gives one bound for each actual canonical mixed jet on the
open fundamental rectangle. The constant may depend on every displayed
parameter. -/
theorem n07b_canonicalSource_mixedDerivative_bound
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint,
      p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) → ContDiffAt ℝ ∞ f p)
    (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈
      Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi,
        ‖mixedDerivative a b (canonicalSource S K z m f) p‖ ≤ B := by
  have hcompact : IsCompact
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB, hbound⟩ := n07b_exists_bound_on_compact_of_local_bounds
    (U := physicalPieceOpen S K m)
    (f := fun x => mixedDerivative a b (canonicalSource S K z m f) (K.chart z m x))
    hcompact (fun p hp =>
      n07b_canonicalSource_mixedDerivative_local_bound hK hz hsector m hf a b p hp.1)
  refine ⟨B, hB, ?_⟩
  intro p hp
  have hpin : p ∈ canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi) :=
    ⟨⟨hp.1, mem_univ _⟩, ⟨mem_univ _, hp.2⟩⟩
  rw [← canonicalChart_image_openStrip hK hz hsector m] at hpin
  obtain ⟨x, hx, hxp⟩ := hpin
  rw [← hxp]
  exact hbound x
    ⟨⟨hx.1.1.1.le, hx.1.1.2.le⟩, ⟨hx.2.2.1.le, hx.2.2.2.le⟩⟩ hx.1

/-- Every actual mixed derivative of the actual source conversion belongs
to the prescribed piece's L² space. -/
theorem n07b_canonicalSource_mixedDerivative_memLp
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint,
      p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) → ContDiffAt ℝ ∞ f p)
    (a b : ℕ) :
    MemLp (mixedDerivative a b (canonicalSource S K z m f))
      2 (canonicalMeasure S K m) := by
  have hcont := (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
    (n07b_contDiffOn_canonicalSource hK hz hsector m hf) a b).continuousOn
  have hmeas : AEStronglyMeasurable
      (mixedDerivative a b (canonicalSource S K z m f)) (canonicalMeasure S K m) := by
    apply (hcont.mono
      (fun p (hp : p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) =>
        show p ∈ canonicalOpen S K m from ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
    exact measurableSet_Ioo.prod measurableSet_Ioc
  obtain ⟨B, _, hB⟩ := n07b_canonicalSource_mixedDerivative_bound hK hz hsector m hf a b
  refine MemLp.of_bound hmeas B ?_
  have hmeasure : canonicalMeasure S K m =
      volume.restrict (Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi) :=
    Measure.restrict_congr_set
      (polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi)
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi := by
    rw [hmeasure]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [ha] with p hp
  exact hB p hp

/-- Globally smooth physical data satisfy the pointwise closed-piece input
without any endpoint convention for the prescribed inverse. -/
theorem n07b_canonicalSource_mixedDerivative_memLp_of_contDiff
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℕ) :
    MemLp (mixedDerivative a b (canonicalSource S K z m f))
      2 (canonicalMeasure S K m) :=
  n07b_canonicalSource_mixedDerivative_memLp hK hz hsector m
    (fun _ _ => hf.contDiffAt) a b

end ContinuousFlexibility.Analysis
