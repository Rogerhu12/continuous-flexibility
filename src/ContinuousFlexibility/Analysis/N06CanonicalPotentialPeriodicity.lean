import ContinuousFlexibility.Analysis.N06CurrentOperatorPeriodicity
import ContinuousFlexibility.Analysis.N06CanonicalHeightGerm
import ContinuousFlexibility.Analysis.N06FiniteSourceGeometry
import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity
import ContinuousFlexibility.Analysis.N06CanonicalProperties
import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities

/-!
# The genuine current canonical potential has period pi

The constant canonical test identifies the potential with the actual
source transform of the physical operator applied to the height. The
height is locally realized by one original HeightPair along each circle;
N03 then forces its operator image to be periodic. The actual inverse
chart and Jacobian lift transport this equality to the canonical cylinder.
No smoothness or periodicity of the corrected b and c fields is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The actual source transform needs periodicity only on its own physical
piece. All inverse and Jacobian values remain in the original open domains. -/
theorem n06_canonicalSource_periodicOn_piece
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ q ∈ physicalPieceOpen S K z m, f (q + (0, Real.pi)) = f q)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p + (0, Real.pi)) = canonicalSource S K z m f p := by
  have hc := hA.charts z hz hs m
  have hd := hA.domains z hz hs m
  have hshift : ∀ q ∈ physicalPieceOpen S K z m,
      q + (0, Real.pi) ∈ physicalPieceOpen S K z m :=
    fun q hq => (hd.2.2.2.1 q).mpr hq
  have hq := hc.2.1 hp
  have hG := inverseChart_periodic_of_chart_periodic_on hc.2.1 hshift hc.2.2.1
    hc.2.2.2.1 (fun q hq => (hc.2.2.2.2.2.2.2 q hq).2.2.1) hp
  have hH := (hc.2.2.2.2.2.2.2 _ hq).2.2.2
  have hJ := n06_planeJacobian_chart_lift_on hd.1 hc.2.2.2.2.1 hshift
    (fun q hq => (hc.2.2.2.2.2.2.2 q hq).2.2.1) hq
  change K.height z m (K.inverseChart z m (p + (0, Real.pi))) *
      f (K.inverseChart z m (p + (0, Real.pi))) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (p + (0, Real.pi)))| = _
  rw [hG, hH, hf _ hq, hJ]
  rfl

/-- N03 applies to a genuine compact realization of the actual N04 height,
so its divergence has period pi everywhere inside the physical piece. -/
theorem n06_correctedHeightDivergence_periodicOn_piece
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    divergenceOperator (L.coefficients z) (K.height z m) (p + (0, Real.pi)) =
      divergenceOperator (L.coefficients z) (K.height z m) p := by
  obtain ⟨η, hη⟩ := n06_exists_heightPair_canonicalHeight_germ hT hS hA hz hs m hp
  have hd := hA.domains z hz hs m
  have hp' : p + (0, Real.pi) ∈ physicalPieceOpen S K z m :=
    (hd.2.2.2.1 p).mpr hp
  have hradial : (K.chart z m (p + (0, Real.pi))).1 = (K.chart z m p).1 := by
    simpa only [Prod.fst_add, add_zero] using congrArg Prod.fst
      (((hA.charts z hz hs m).2.2.2.2.2.2.2 p hp).2.2.1)
  have hper := n06_correctedDivergence_heightPair_periodicOn hS h03 hz hs η
    (hd.2.2.1 hp)
  exact (n05_divergenceOperator_congr (L.coefficients z)
    (hη _ hp' hradial)).symm.trans
      (hper.trans (n05_divergenceOperator_congr (L.coefficients z) (hη p hp rfl)))

/-- Constant-test identification of the potential and the genuine N03
source property force its period on both positive and negative pieces. -/
theorem n06_canonicalPotential_periodicOn_of_parts
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    K.potential z m (p + (0, Real.pi)) = K.potential z m p := by
  have hp' : p + (0, Real.pi) ∈ canonicalOpen S K m :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  rw [canonicalPotential_eq_source_height hB hz hs m hp',
    canonicalPotential_eq_source_height hB hz hs m hp]
  exact congrArg (fun a : ℝ => (if K.positive m then -1 else (1 : ℝ)) * a)
    (n06_canonicalSource_periodicOn_piece hA hz hs m
      (fun q hq => n06_correctedHeightDivergence_periodicOn_piece
        hT hS h03 hA hz hs m hq) hp)

/-- The period is derived directly from the original unchanged N03 and N04
contracts on the same chosen current data. -/
theorem n06_canonicalPotential_periodicOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    K.potential z m (p + (0, Real.pi)) = K.potential z m p :=
  n06_canonicalPotential_periodicOn_of_parts hT hS h03
    (n06_N04_qualitative_parts h04).1 (n06_N04_qualitative_parts h04).2 hz hs m hp

end ContinuousFlexibility.Statements
