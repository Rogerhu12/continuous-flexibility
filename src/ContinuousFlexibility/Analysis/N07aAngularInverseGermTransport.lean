import ContinuousFlexibility.Analysis.N07aAngularInverseExtension
import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-!
# The genuine inverse germ after reference pullback

Every map below is the actual forward chart or an extension of its actual
open inverse. The smooth germ agrees with the extension on the closed
strip, which is the equality needed for subsequent one-jet gluing.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff NNReal

theorem n07a_inverseExtension_eq_smooth_germ
    {g g₀ G : PolarPoint → PolarPoint} {t : Set PolarPoint} {a : PolarPoint}
    (hg₀ : Continuous g₀) (hgg₀ : EqOn g g₀ t)
    (hG : ContDiffAt ℝ ∞ G a)
    (he : ∀ᶠ p in 𝓝 a, p ∈ t → g p = G p) :
    ∀ᶠ p in 𝓝 a, p ∈ closure t → g₀ p = G p := by
  have hG0 : ContDiffAt ℝ 0 G a := hG.of_le (by simp)
  apply n07a_eventuallyEq_on_closure (Eventually.of_forall fun _ => hg₀.continuousAt)
    ((hG0.eventually (by simp)).mono fun _ hp => hp.continuousAt)
  filter_upwards [he] with p hp hpt
  exact (hgg₀ hpt).symm.trans (hp hpt)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_actual_chart_maps_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    MapsTo (K.chart z m)
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ univ)
      (Icc (K.left m) (K.right m) ×ˢ univ) := by
  intro p hp
  have hgeom := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hclosed := h04.2.2.2.2.2.2.2.2.1 z hz hs m p hp.1
  have hpcl : p ∈ closure (physicalPieceOpen S K m) := by
    simpa only [physicalPieceOpen, closure_prod_eq,
      closure_Ioo (h04.2.2.2.1 m).1.ne, closure_univ] using hp
  have h := hclosed.1.continuousAt.continuousWithinAt.mem_closure hpcl hgeom.1
  simpa only [canonicalOpen, closure_prod_eq,
    closure_Ioo (h04.2.2.2.1 m).2.1.ne, closure_univ] using h

theorem n07a_actual_inverse_pullback_germ
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p q : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (hq : q.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (heq : K.chart z m q = K.chart (C.referenceState, 0) m p)
    {g₀ : PolarPoint → PolarPoint} (hg₀ : Continuous g₀)
    (hgg₀ : EqOn (K.inverseChart z m) g₀ (canonicalOpen S K m))
    (hLip : ∃ M : ℝ≥0, LipschitzOnWith M (K.inverseChart z m) (canonicalOpen S K m)) :
    ∃ (B : PolarPoint ≃L[ℝ] PolarPoint) (G : PolarPoint → PolarPoint),
      (B : PolarPoint →L[ℝ] PolarPoint) = fderiv ℝ (K.chart z m) q ∧
      ContDiffAt ℝ ∞ G (K.chart (C.referenceState, 0) m p) ∧
      G (K.chart (C.referenceState, 0) m p) = q ∧
      HasFDerivAt G (B.symm : PolarPoint →L[ℝ] PolarPoint)
        (K.chart (C.referenceState, 0) m p) ∧
      ∀ᶠ x in 𝓝 p, x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
        g₀ (K.chart (C.referenceState, 0) m x) =
          G (K.chart (C.referenceState, 0) m x) := by
  have hgeom := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hclosed := h04.2.2.2.2.2.2.2.2.1 z hz hs m q hq
  have hqcl : q ∈ closure (physicalPieceOpen S K m) := by
    rw [physicalPieceOpen, closure_prod_eq,
      closure_Ioo (h04.2.2.2.1 m).1.ne, closure_univ]
    exact ⟨hq, mem_univ _⟩
  have hdet : (fderiv ℝ (K.chart z m) q).det ≠ 0 := by
    simpa only [← n07a_planeJacobian_eq_det] using hclosed.2.2.1
  let B := (fderiv ℝ (K.chart z m) q).toContinuousLinearEquivOfDetNeZero hdet
  obtain ⟨M, hM⟩ := hLip
  obtain ⟨G, hG, hGq, hGd, hGe⟩ := n07a_boundary_inverse_germ hqcl
    hgeom.1 hgeom.2.2.1 hgeom.2.2.2.1 hclosed.1 hdet hM
  have hec := n07a_inverseExtension_eq_smooth_germ hg₀ hgg₀ hG hGe
  have hrefz := n07a_reference_mem_stateNeighborhood h01
  have hrefs := h01.2.2.1.stateSector
  have hrp := h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) hrefz hrefs m p hp
  have hec' : ∀ᶠ y in 𝓝 (K.chart (C.referenceState, 0) m p),
      y ∈ closure (canonicalOpen S K m) → g₀ y = G y := by
    simpa only [heq] using hec
  refine ⟨B, G, by simp only [B, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero],
    by simpa only [heq] using hG, by simpa only [heq] using hGq,
    by simpa only [heq, B] using hGd, ?_⟩
  filter_upwards [hrp.1.continuousAt.eventually hec'] with x hx hxc
  apply hx
  have hm : K.chart (C.referenceState, 0) m x ∈
      Icc (K.left m) (K.right m) ×ˢ univ :=
    n07a_actual_chart_maps_closed h04 hrefz hrefs m ⟨hxc, mem_univ _⟩
  simpa only [canonicalOpen, closure_prod_eq,
    closure_Ioo (h04.2.2.2.1 m).2.1.ne, closure_univ] using hm

end ContinuousFlexibility.Analysis
