import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing
import ContinuousFlexibility.Analysis.N07aGeometryOpenCoefficients

/-!
# The actual physical measure and rough chart pullback

The Jacobian change of variables is applied to the real chart on its real
half-period strip.  In particular, equality of canonical L² representatives
pulls back to equality of the original physical representatives.  A bound
for the inverse Jacobian gives the corresponding L² pullback; the final
lemma supplies that bound from the primitive geometric jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal

/-- The existing interval weak-jet spaces on the actual physical interval. -/
def n07aPhysicalIntervalData {S : PhysicalSpacesData} (K : CanonicalData S) :
    CanonicalData S :=
  { K with left := K.physicalLeft, right := K.physicalRight }

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Half-strip geometry for the actual chart, including the hypotheses of
the ordinary two-dimensional change-of-variables theorem. -/
theorem n07a_physicalHalfGeometry
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    let Q := Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
    (K.chart z m '' Q = Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    InjOn (K.chart z m) Q ∧
    (∀ p ∈ Q, HasFDerivWithinAt (K.chart z m) (fderiv ℝ (K.chart z m) p) Q p) ∧
    (∀ p ∈ Q, K.inverseChart z m (K.chart z m p) = p ∧
      K.height z m p ≠ 0 ∧ planeJacobian (K.chart z m) p ≠ 0) := by
  rcases h04 with ⟨_, _, _, _, _, _, _, hgeom, _, href, hiref, _⟩
  obtain ⟨hf, hg, hgf, hfg, hfs, hgs, _, hgp⟩ := hgeom z hz hs m
  have hfr : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) :=
    fun p hp => (href z hz hs m p hp).1
  have hfp : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) :=
    fun p hp => (hgp p hp).2.2.1
  refine ⟨n07a_strip_image_half hf hg hgf hfg hfs hgs hfr (hiref z hz hs m) hfp,
    ?_, ?_, ?_⟩
  · intro p hp q hq he
    exact (hgf p ⟨hp.1, mem_univ _⟩).symm.trans
      ((congrArg (K.inverseChart z m) he).trans (hgf q ⟨hq.1, mem_univ _⟩))
  · intro p hp
    exact ((hfs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hp.1, mem_univ _⟩)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro p hp
    have hp' : p ∈ physicalPieceOpen S K m := ⟨hp.1, mem_univ _⟩
    exact ⟨hgf p hp', (hgp p hp').1.ne', (hgp p hp').2.1⟩

def n07aChartDensity (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (p : PolarPoint) : ℝ≥0∞ :=
  ENNReal.ofReal |planeJacobian (K.chart z m) p|

theorem n07a_chartDensity_aemeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    AEMeasurable (n07aChartDensity K z m)
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  obtain ⟨_, _, hd, _⟩ := n07a_physicalHalfGeometry h04 hz hs m
  unfold n07aChartDensity
  simpa only [n07a_planeJacobian_eq_det,
    canonicalMeasure, n07aPhysicalIntervalData] using
    aemeasurable_ofReal_abs_det_fderivWithin volume
      (measurableSet_Ioo.prod measurableSet_Ioc) hd

theorem n07a_chart_aemeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    AEMeasurable (K.chart z m)
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  obtain ⟨_, _, hd, _⟩ := n07a_physicalHalfGeometry h04 hz hs m
  exact ContinuousOn.aemeasurable
    (fun p hp => (hd p hp).differentiableWithinAt.continuousWithinAt)
    (measurableSet_Ioo.prod measurableSet_Ioc)

theorem n07a_chartDensity_ne_zero_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ∀ᵐ p ∂canonicalMeasure S (n07aPhysicalIntervalData K) m,
      n07aChartDensity K z m p ≠ 0 := by
  obtain ⟨_, _, _, hp⟩ := n07a_physicalHalfGeometry h04 hz hs m
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hq
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (hp p hq).2.2))

/-- The genuine physical Jacobian measure pushes to the genuine canonical
Lebesgue measure, with no regularity requirement on functions integrated. -/
theorem n07a_chart_map_withDensity
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    Measure.map (K.chart z m)
      ((canonicalMeasure S (n07aPhysicalIntervalData K) m).withDensity
        (n07aChartDensity K z m)) = canonicalMeasure S K m := by
  obtain ⟨hi, hinj, hd, _⟩ := n07a_physicalHalfGeometry h04 hz hs m
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume
    (measurableSet_Ioo.prod measurableSet_Ioc).nullMeasurableSet hd hinj
  rw [hi] at h
  unfold n07aChartDensity
  simpa only [n07a_planeJacobian_eq_det,
    canonicalMeasure, n07aPhysicalIntervalData] using h

/-- Actual a.e. equality pulls back from canonical to physical representatives. -/
theorem n07a_chart_ae_pullback {E : Type*}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → E}
    (he : f =ᵐ[canonicalMeasure S K m] g) :
    (fun p => f (K.chart z m p)) =ᵐ[canonicalMeasure S (n07aPhysicalIntervalData K) m]
      fun p => g (K.chart z m p) := by
  have hchart := (n07a_chart_aemeasurable h04 hz hs m).mono_ac
    (withDensity_absolutelyContinuous _ (n07aChartDensity K z m))
  rw [← n07a_chart_map_withDensity h04 hz hs m] at he
  exact (withDensity_ae_eq (n07a_chartDensity_aemeasurable h04 hz hs m)
    (n07a_chartDensity_ne_zero_ae h04 hz hs m)).mp (ae_of_ae_map hchart he)

/-- A pointwise inverse Jacobian bound controls the unweighted physical
measure by the actual Jacobian measure. -/
theorem n07a_physicalMeasure_le_jacobian
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ p ∈ physicalPieceOpen S K m,
      |planeJacobian (K.chart z m) p|⁻¹ ≤ A) :
    canonicalMeasure S (n07aPhysicalIntervalData K) m ≤
      ENNReal.ofReal A •
        (canonicalMeasure S (n07aPhysicalIntervalData K) m).withDensity
          (n07aChartDensity K z m) := by
  obtain ⟨_, _, _, hpoint⟩ := n07a_physicalHalfGeometry h04 hz hs m
  have hb : ∀ᵐ p ∂canonicalMeasure S (n07aPhysicalIntervalData K) m,
      (1 : PolarPoint → ℝ≥0∞) p ≤
        (ENNReal.ofReal A • n07aChartDensity K z m) p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hj : 0 < |planeJacobian (K.chart z m) p| :=
      abs_pos.mpr (hpoint p hp).2.2
    have hmul : 1 ≤ A * |planeJacobian (K.chart z m) p| :=
      (inv_le_iff_one_le_mul₀ hj).mp (hbound p ⟨hp.1, mem_univ _⟩)
    simpa only [Pi.one_apply, Pi.smul_apply, smul_eq_mul,
      n07aChartDensity, ← ENNReal.ofReal_mul hA, ENNReal.ofReal_one] using
      (ENNReal.ofReal_le_ofReal hmul)
  have h := withDensity_mono hb
  rwa [withDensity_one,
    withDensity_smul' (ENNReal.ofReal A) (n07aChartDensity K z m)
      ENNReal.ofReal_ne_top] at h

/-- L² pullback through the actual chart under its actual inverse-Jacobian
bound. The hypothesis is discharged from primitive geometry below. -/
theorem n07a_chart_memLp_pullback
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ p ∈ physicalPieceOpen S K m,
      |planeJacobian (K.chart z m) p|⁻¹ ≤ A)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (canonicalMeasure S K m)) :
    MemLp (fun p => f (K.chart z m p)) 2
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  have hchart := (n07a_chart_aemeasurable h04 hz hs m).mono_ac
    (withDensity_absolutelyContinuous _ (n07aChartDensity K z m))
  rw [← n07a_chart_map_withDensity h04 hz hs m] at hf
  have hp := (hf.comp_of_map hchart).smul_measure (c := ENNReal.ofReal A)
    ENNReal.ofReal_ne_top
  exact MemLp.mono_measure
    (n07a_physicalMeasure_le_jacobian h04 hz hs m hA hbound) hp

/-- Primitive unit-strip jets give an actual physical inverse-Jacobian bound. -/
theorem n07a_current_inverseJacobian_bounded
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ physicalPieceOpen S K m,
      |planeJacobian (K.chart (liftSectorParameter S C z) m) p|⁻¹ ≤ A := by
  obtain ⟨A, hA, hbound⟩ := n07a_currentAtom_bounded href hcur z hz m .jacobianInverse 0 0
  refine ⟨A, hA, ?_⟩
  intro p hp
  let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m p
  have hq : q ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps hm hp
  have he : CanonicalGeometry.physicalUnitPoint K m q = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) hm p
  have h := hbound q hq
  simpa only [spaces_mixedDerivative_zero, CanonicalGeometry.atom, he,
    abs_inv, abs_abs] using h

/-- The actual current chart pulls every canonical L² function to its
physical piece, using only the already specified primitive geometric data. -/
theorem n07a_current_chart_memLp_pullback
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : MemLp f 2 (canonicalMeasure S K m)) :
    MemLp (fun p => f (K.chart (liftSectorParameter S C z) m p)) 2
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  obtain ⟨A, hA, hb⟩ := n07a_current_inverseJacobian_bounded href hcur z hz m
    (h04.2.2.2.1 m).1
  exact n07a_chart_memLp_pullback h04 hz' hs m hA hb hf

end ContinuousFlexibility.Analysis
