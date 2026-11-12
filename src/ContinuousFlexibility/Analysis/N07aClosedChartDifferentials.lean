import ContinuousFlexibility.Analysis.N07aActualChartDifferentials
import ContinuousFlexibility.Analysis.N07aClosedPhysicalHeight
import ContinuousFlexibility.Analysis.N04bBoundaryInverseRegularity

/-!
# Closed chart differentials and the actual transport first jet

The inverse differential identities extend from the open canonical strip
by continuity of the genuine boundary inverse germs. The global primitive
transport therefore has the same invertible first jet as each actual
piece transition at every interior reference boundary point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open N07aClosedJets
open scoped Topology ContDiff

/-- Continuous values on a genuine closure are determined by their open values. -/
theorem n07a_eq_of_continuousAt_of_eqOn_closure
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    {s : Set E} {p : E} {f g : E → F}
    (hp : p ∈ closure s) (hf : ContinuousAt f p) (hg : ContinuousAt g p)
    (he : EqOn f g s) : f p = g p := by
  haveI : NeBot (𝓝[s] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) (hg.mono_left nhdsWithin_le_nhds)
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- Genuine one-sided equality determines the first jet of two C¹ germs. -/
theorem n07a_firstJet_eq_of_eqOn_closure
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {p : E} {f g : E → F}
    (hs : IsOpen s) (hp : p ∈ closure s)
    (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p)
    (he : EqOn f g s) : f p = g p ∧ fderiv ℝ f p = fderiv ℝ g p := by
  refine ⟨n07a_eq_of_continuousAt_of_eqOn_closure hp hf.continuousAt hg.continuousAt he, ?_⟩
  apply n07a_eq_of_continuousAt_of_eqOn_closure hp
    (hf.fderiv_right (by simp : (0 : ℕ∞ω) + 1 ≤ 1)).continuousAt
    (hg.fderiv_right (by simp : (0 : ℕ∞ω) + 1 ≤ 1)).continuousAt
  intro x hx
  have hnear : f =ᶠ[𝓝 x] g := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact he hy
  exact hnear.fderiv_eq

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The actual inverse matrices remain inverse at every canonical endpoint. -/
theorem n07a_actualChart_fderiv_inverse_closed
    (hgeom : CanonicalGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {y : PolarPoint} (hy : y ∈ canonicalClosed S K m) :
    (fderiv ℝ (K.chart z m) (K.inverseChart z m y)).comp
        (fderiv ℝ (K.inverseChart z m) y) = ContinuousLinearMap.id ℝ PolarPoint ∧
      (fderiv ℝ (K.inverseChart z m) y).comp
        (fderiv ℝ (K.chart z m) (K.inverseChart z m y)) =
          ContinuousLinearMap.id ℝ PolarPoint := by
  have hG := n04b_inverseChart_contDiffAt_closed hgeom hz hs m hy
  have hF := ((hgeom.boundary z hz hs m).2.2.2.2.1 _
    ((hgeom.boundary z hz hs m).2.1 hy)).1
  have hDG : ContinuousAt (fderiv ℝ (K.inverseChart z m)) y :=
    (hG.fderiv_right (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousAt
  have hDF : ContinuousAt
      (fun q => fderiv ℝ (K.chart z m) (K.inverseChart z m q)) y :=
    (hF.fderiv_right (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousAt.comp hG.continuousAt
  have hcl : y ∈ closure (canonicalOpen S K m) := by
    rw [show canonicalOpen S K m = openStrip (K.left m) (K.right m) from rfl,
      closure_openStrip (hgeom.referenceBounds m).2.1]
    exact hy
  constructor
  · exact n07a_eq_of_continuousAt_of_eqOn_closure hcl (hDF.clm_comp hDG)
      continuousAt_const (fun q hq => (n07a_actualChart_fderiv_inverse hgeom hz hs m hq).1)
  · exact n07a_eq_of_continuousAt_of_eqOn_closure hcl (hDG.clm_comp hDF)
      continuousAt_const (fun q hq => (n07a_actualChart_fderiv_inverse hgeom hz hs m hq).2)

/-- The actual transition is smooth as a full germ at a reference closed point. -/
theorem n07a_canonicalCurrentPoint_contDiffAt_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    ContDiffAt ℝ ∞ (canonicalCurrentPoint C K z m) p := by
  have hb := h04.1.boundary (C.referenceState, 0) href hsref m
  exact (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m (hb.1 hp)).comp p
    (hb.2.2.2.2.1 p hp).1

/-- The transition differential is onto because it is a composition of
actual inverse differentials, including at the reference boundary. -/
theorem n07a_canonicalCurrentPoint_fderiv_surjective
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    Function.Surjective (fderiv ℝ (canonicalCurrentPoint C K z m) p) := by
  have hb := h04.1.boundary (C.referenceState, 0) href hsref m
  have hq := hb.1 hp
  have hF := (hb.2.2.2.2.1 p hp).1.differentiableAt (by simp)
  have hG := (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m hq).differentiableAt
    (by simp)
  have hIref := (n07a_actualChart_fderiv_inverse_closed h04.1 href hsref m hq).1
  rw [hb.2.2.1 p hp] at hIref
  have hIcur := (n07a_actualChart_fderiv_inverse_closed h04.1 hz hs m hq).2
  have hFs : Function.Surjective (fderiv ℝ (K.chart (C.referenceState, 0) m) p) := by
    intro v
    refine ⟨fderiv ℝ (K.inverseChart (C.referenceState, 0) m)
      (K.chart (C.referenceState, 0) m p) v, ?_⟩
    exact congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A v) hIref
  have hGs : Function.Surjective
      (fderiv ℝ (K.inverseChart z m) (K.chart (C.referenceState, 0) m p)) := by
    intro v
    refine ⟨fderiv ℝ (K.chart z m)
      (K.inverseChart z m (K.chart (C.referenceState, 0) m p)) v, ?_⟩
    exact congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A v) hIcur
  change Function.Surjective (fderiv ℝ
    (K.inverseChart z m ∘ K.chart (C.referenceState, 0) m) p)
  rw [fderiv_comp p hG hF]
  exact hGs.comp hFs

/-- The source-independent primitive transport has the same value and
first derivative as each actual piece transition on its reference closure. -/
theorem n07a_primitiveTransport_closed_firstJet
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {τ : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
    (hτ : ContDiffOn ℝ 3 τ (annularOpen D))
    (hq : ContDiffOn ℝ 3 q (annularOpen D))
    (hpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = canonicalCurrentPoint C K z m p ∧
        q p = K.height (C.referenceState, 0) m p / K.height z m (τ p))
    (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m)
    (hpD : p ∈ annularOpen D) :
    let Ti := canonicalCurrentPoint C K z m
    let ρi := fun x => K.height (C.referenceState, 0) m x / K.height z m (Ti x)
    (τ p = Ti p ∧ fderiv ℝ τ p = fderiv ℝ Ti p) ∧
      (q p = ρi p ∧ fderiv ℝ q p = fderiv ℝ ρi p) ∧
      q p ≠ 0 ∧ Function.Surjective (fderiv ℝ τ p) := by
  let Ti := canonicalCurrentPoint C K z m
  let ρi := fun x => K.height (C.referenceState, 0) m x / K.height z m (Ti x)
  have hTi := n07a_canonicalCurrentPoint_contDiffAt_closed h04 href hsref hz hs m hp
  have hB := h04.1.boundary (C.referenceState, 0) href hsref m
  have hcurp : Ti p ∈ physicalPieceClosed S K z m :=
    (h04.1.boundary z hz hs m).2.1 (hB.1 hp)
  have hhi := hB.2.2.2.2.1 p hp
  have hhc := (h04.1.boundary z hz hs m).2.2.2.2.1 (Ti p) hcurp
  have hρi : ContDiffAt ℝ ∞ ρi p :=
    hhi.2.1.div (hhc.2.1.comp p hTi) hhc.2.2.2.ne'
  have hpcl : p ∈ closure (referencePhysicalPieceOpen S K m) := by
    rw [← h04.1.referenceDomain m]
    exact hp
  have hτi := n07a_firstJet_eq_of_eqOn_closure (isOpen_Ioo.prod isOpen_univ) hpcl
    ((hτ.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpD)).of_le (by norm_num))
    (hTi.of_le (by simp)) (fun x hx => (hpiece m x hx).1)
  have hqi := n07a_firstJet_eq_of_eqOn_closure (isOpen_Ioo.prod isOpen_univ) hpcl
    ((hq.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpD)).of_le (by norm_num))
    (hρi.of_le (by simp)) (fun x hx => by
      change q x = K.height (C.referenceState, 0) m x /
        K.height z m (canonicalCurrentPoint C K z m x)
      rw [(hpiece m x hx).2, (hpiece m x hx).1])
  refine ⟨hτi, hqi, ?_, ?_⟩
  · rw [hqi.1]
    exact div_ne_zero hhi.2.2.2.ne' hhc.2.2.2.ne'
  · rw [hτi.2]
    exact n07a_canonicalCurrentPoint_fderiv_surjective h04 href hsref hz hs m hp

end ContinuousFlexibility.Analysis
