import ContinuousFlexibility.Analysis.N06CurrentCubicTestPairing
import ContinuousFlexibility.Analysis.N06N05PositiveCubicSourceMap

/-!
# The original N05 cubic source map paired with current physical tests

The compact equation of the very same source endomorphism extends to
actual transformed physical tests. N04 supplies their open smoothness
and all required L2 jets. No extension of the inverse chart at a radial
endpoint is assumed, and the reference height and source level stay fixed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The seven coefficient jets needed by the actual open-test extension
are consequences of the original positive cubic control. -/
theorem N06PositiveCubicControl.actual_firstJets
    {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
    {scale : ℕ → ℝ} {δ : ℝ} {A B C : ℕ → PolarPoint → ℝ}
    (h : N06PositiveCubicControl K b scale δ A B C)
    (m : ℕ) (hm : K.positive m = true) (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
    |A m p| ≤ δ * scale m ∧ |B m p| ≤ δ * scale m ∧ |C m p| ≤ δ * scale m ∧
      |radialPartial (A m) p| ≤ δ * scale m ∧ |angularPartial (B m) p| ≤ δ * scale m ∧
      |radialPartial (B m) p| ≤ δ * scale m ∧ |angularPartial (C m) p| ≤ δ * scale m := by
  have hzero := h.jets m hm 0 0 (by omega) p hp
  have hrad := h.jets m hm 1 0 (by omega) p hp
  have hang := h.jets m hm 0 1 (by omega) p hp
  simp only [spaces_mixedDerivative_zero] at hzero
  have hR (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
      radialPartial f p = mixedDerivative 1 0 f p := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      mixedDerivative_radialPartial (isOpen_Ioo.prod isOpen_univ) hf 0 0 hp
  have hT (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
      angularPartial f p = mixedDerivative 0 1 f p := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      mixedDerivative_angularPartial (isOpen_Ioo.prod isOpen_univ) hf 0 0 hp
  refine ⟨hzero.1, hzero.2.1, hzero.2.2, ?_, ?_, ?_, ?_⟩
  · rw [hR _ (h.a_smooth m hm)]
    exact hrad.1
  · rw [hT _ (h.b_smooth m hm)]
    exact hang.2.1
  · rw [hR _ (h.b_smooth m hm)]
    exact hrad.2.1
  · rw [hT _ (h.c_smooth m hm)]
    exact hang.2.2


end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- The original positive cubic source endomorphism has the weak identity
against the exact current-coordinate transform of every full-period
physical test. This uses the map's already established compact identity. -/
theorem n06N05_positiveCubicSourceMap_current_physical_pairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K Vol b}
    {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {scale : ℕ → ℝ} {δ : ℝ} {A Bc Cc : ℕ → PolarPoint → ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ A Bc Cc)
    (M : Vol.level (3 / 4 : ℝ) 0 b →L[ℝ] Vol.level (3 / 4 : ℝ) 0 b)
    (hM : ∀ F n ψ, CanonicalTest S K n ψ →
      (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) n p * ψ p ∂canonicalMeasure S K n) =
        ∫ p, n06InverseCanonicalHeight B F n p *
          n06PositiveCubicTestOperator K A Bc Cc n ψ p ∂canonicalMeasure S K n)
    (F : Vol.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m = true)
    (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    (∫ p, Vol.forget (3 / 4 : ℝ) 0 b (M F) m p *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) =
      ∫ p, n06InverseCanonicalHeight B F m p *
        n06PositiveCubicTestOperator K A Bc Cc m
          (canonicalHeight S K z m (n06_radialTestAverage φ)) p
            ∂canonicalMeasure S K m := by
  have hmid : ((1 / 2 : ℝ), (0 : ℝ)) ∈ canonicalOpen S K m := by
    simp only [canonicalOpen, hl, hr, mem_prod, mem_Ioo, mem_univ, and_true]
    norm_num
  have hδm : 0 ≤ δ * scale m :=
    (abs_nonneg (A m ((1 / 2 : ℝ), 0))).trans (hcoeff.actual_firstJets m hm _ hmid).1
  rw [n06PositiveCubicTestOperator, if_pos hm]
  apply n06_cubic_pairing_actual_fullPhysical_test h04 hz hs m hl hr hδm
    (hcoeff.a_smooth m hm) (hcoeff.b_smooth m hm) (hcoeff.c_smooth m hm)
    (hcoeff.actual_firstJets m hm)
    (n06InverseCanonicalHeight B F m) (Vol.forget (3 / 4 : ℝ) 0 b (M F) m)
    ?_ hφ
  intro ψ hψ
  simpa only [n06PositiveCubicTestOperator, if_pos hm] using hM F m ψ hψ

end ContinuousFlexibility.Statements
