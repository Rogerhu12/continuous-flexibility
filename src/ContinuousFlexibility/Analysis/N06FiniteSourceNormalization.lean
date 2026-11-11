import ContinuousFlexibility.Analysis.N06NormalizedRepresentation
import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
import ContinuousFlexibility.Analysis.N06ReferenceNuColumn
import ContinuousFlexibility.Analysis.N06CanonicalDifference

/-!
# Exact cancellation of normalized reference source columns

On the open normalization region, N04 fixes the chart and height. The
chart germ also fixes its actual Jacobian. Consequently a physical source
supported in that region has exactly the same canonical source at every
allowed state. In particular, the reference nu field has no coordinate
variation, including at every mixed spatial jet order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_chartJacobian_on_normalization
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) (hpN : p.1 ∈ K.normalizationRegion) :
    planeJacobian (K.chart z m) p = planeJacobian (K.chart (C.referenceState, 0) m) p := by
  have heq : K.chart z m =ᶠ[𝓝 p] K.chart (C.referenceState, 0) m := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp,
      (hN04.1.preimage continuous_fst).mem_nhds hpN] with q hq hqN
    exact (hN04.2.2.1 z hz hs m q hq hqN).1
  unfold planeJacobian
  rw [heq.fderiv_eq (𝕜 := ℝ)]

/-- The fixed chart identity can also be applied when it is the reference
inverse image, rather than the current inverse image, that lies in the
normalization region. -/
theorem n06_inverseChart_of_reference_normalization
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (hpN : (K.inverseChart (C.referenceState, 0) m p).1 ∈ K.normalizationRegion) :
    K.inverseChart z m p = K.inverseChart (C.referenceState, 0) m p := by
  have hc := hN04.2.2.2.2.2.2.2.1 z hz hs m
  have hr := hN04.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsector m
  have hq := hr.2.1 hp
  have hfixed := hN04.2.2.1 z hz hs m _ hq hpN
  have hchart : K.chart z m (K.inverseChart (C.referenceState, 0) m p) = p :=
    hfixed.1.trans (hr.2.2.2.1 p hp)
  calc
    K.inverseChart z m p = K.inverseChart z m
        (K.chart z m (K.inverseChart (C.referenceState, 0) m p)) :=
      congrArg (K.inverseChart z m) hchart.symm
    _ = _ := hc.2.2.1 _ hq

/-- Every physical source supported in the fixed normalization region
has an identical actual canonical source at the current and reference
states. No regularity of the source is required. -/
theorem n06_canonicalSource_normalization_fixed
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hsupport : ∀ p, f p ≠ 0 → p.1 ∈ K.normalizationRegion)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f p = canonicalSource S K (C.referenceState, 0) m f p := by
  by_cases hzero : f (K.inverseChart z m p) = 0
  · have hrefzero : f (K.inverseChart (C.referenceState, 0) m p) = 0 := by
      by_contra hnonzero
      have hi := n06_inverseChart_of_reference_normalization hN04 href hsector hz hs hp
        (hsupport _ hnonzero)
      exact hnonzero (by rw [← hi]; exact hzero)
    simp only [canonicalSource, hzero, hrefzero, mul_zero, zero_div]
  · have hpN := hsupport _ hzero
    have hi := n06_inverseChart_on_normalization hN04 href hsector hz hs hp hpN
    have hq := (hN04.2.2.2.2.2.2.2.1 z hz hs m).2.1 hp
    have hJ := n06_chartJacobian_on_normalization hN04 hz hs hq hpN
    dsimp only [canonicalSource]
    rw [hi.2, hJ, hi.1]

theorem n06_canonicalSource_normalization_difference_jet_zero
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hsupport : ∀ p, f p ≠ 0 → p.1 ∈ K.normalizationRegion)
    (m a b : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a b (fun q => canonicalSource S K z m f q -
      canonicalSource S K (C.referenceState, 0) m f q) p = 0 := by
  apply n06_mixedDerivative_eq_zero_on_strip _ a b hp.1
  intro q hq
  exact sub_eq_zero.mpr
    (n06_canonicalSource_normalization_fixed hN04 href hsector hz hs hsupport m
      ⟨hq, mem_univ _⟩)

/-- The fixed-region source hypothesis for the true reference border is
already a literal N04 clause. -/
theorem n06_canonicalReferenceNu_fixed
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (n06ReferenceNuField D) p =
      canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D) p := by
  apply n06_canonicalSource_normalization_fixed hN04 href hsector hz hs _ m hp
  intro q hq
  apply hN04.2.1
  apply Function.mem_support.mpr
  intro hzero
  exact hq (by simp only [n06ReferenceNuField, hzero, zero_mul])

theorem n06_canonicalReferenceNu_difference_jet_zero
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m a b : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a b (fun q => canonicalSource S K z m (n06ReferenceNuField D) q -
      canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D) q) p = 0 := by
  apply n06_mixedDerivative_eq_zero_on_strip _ a b hp.1
  intro q hq
  exact sub_eq_zero.mpr (n06_canonicalReferenceNu_fixed hN04 href hsector hz hs m
    ⟨hq, mem_univ _⟩)

/-- The actual nu-column difference contains only the changed physical
nu field: the reference column contributes exactly zero coordinate
variation on the same canonical piece. -/
theorem n06_canonicalNuDifference_eq_physicalDifference
    (hN04 : N04Properties D T S C L K base loss ε)
    (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    (hrefState : referenceStateConditions D S C)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (nuColumnField D S C z) p -
        canonicalSource S K (C.referenceState, 0) m
          (nuColumnField D S C (C.referenceState, 0)) p =
      canonicalSource S K z m (fun q => nuColumnField D S C z q - n06ReferenceNuField D q) p := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hq := (hN04.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsector m).2.1 hp
  have hqD := (hN04.2.2.2.1 m).2.2 hq.1
  have hnu := n06_nuColumn_reference
    (p := K.inverseChart (C.referenceState, 0) m p)
    hgeom.2.2.1.1 hb.1 hgeom.2.2.2.1.1 hrefState
    (hgeom.1.trans hqD.1).ne'
  have hrefnu : canonicalSource S K (C.referenceState, 0) m
      (nuColumnField D S C (C.referenceState, 0)) p =
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D) p := by
    dsimp only [canonicalSource]
    rw [hnu]
    rfl
  rw [hrefnu, ← n06_canonicalReferenceNu_fixed hN04 href hsector hz hs m hp]
  simp only [canonicalSource, div_eq_mul_inv]
  ring

end ContinuousFlexibility.Statements
