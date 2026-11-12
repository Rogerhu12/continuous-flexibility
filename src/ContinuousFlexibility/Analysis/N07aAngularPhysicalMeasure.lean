import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing
import ContinuousFlexibility.Analysis.N07aGeometryOpenCoefficients

/-!
# The actual physical measure and rough chart pullback

The Jacobian change of variables is applied to the real chart on its real
half-period strip.  In particular, equality of canonical L² representatives
pulls back to equality of the original physical representatives.  A bound
for the inverse Jacobian gives the corresponding L² pullback; the final
lemma supplies a qualitative bound from the closed current atlas geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

def n07aChartDensity (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (p : PolarPoint) : ℝ≥0∞ :=
  ENNReal.ofReal |planeJacobian (K.chart z m) p|

theorem n07a_chartDensity_aemeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    AEMeasurable (n07aChartDensity K z m) (n07aPhysicalMeasure S K z m) := by
  obtain ⟨_, _, hd, _⟩ := n07a_physicalHalfGeometry h04 hz hs m
  rw [n07aPhysicalMeasure_eq_openAngularStrip]
  unfold n07aChartDensity
  simpa only [n07a_planeJacobian_eq_det] using
    aemeasurable_ofReal_abs_det_fderivWithin volume
      (((h04.1.domains z hz hs m).1.inter
        (isOpen_univ.prod isOpen_Ioo)).measurableSet) hd

theorem n07a_chart_aemeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    AEMeasurable (K.chart z m) (n07aPhysicalMeasure S K z m) := by
  exact (((h04.1.charts z hz hs m).2.2.2.2.1.continuousOn).mono
    inter_subset_left).aemeasurable
      ((h04.1.domains z hz hs m).1.measurableSet.inter
        (MeasurableSet.univ.prod measurableSet_Ioc))

theorem n07a_chartDensity_ne_zero_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ∀ᵐ p ∂n07aPhysicalMeasure S K z m, n07aChartDensity K z m p ≠ 0 := by
  filter_upwards [n07aPhysicalMeasure_ae h04 hz hs m] with p hp
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (abs_pos.mpr ((h04.1.charts z hz hs m).2.2.2.2.2.2.2 p hp).2.1))

/-- The Jacobian measure on the actual current domain pushes to the
canonical measure. Angular boundary lines are removed only as null sets. -/
theorem n07a_chart_map_withDensity
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    Measure.map (K.chart z m)
      ((n07aPhysicalMeasure S K z m).withDensity (n07aChartDensity K z m)) =
        canonicalMeasure S K m := by
  obtain ⟨hi, hinj, hd, _⟩ := n07a_physicalHalfGeometry h04 hz hs m
  have hQ : MeasurableSet
      (physicalPieceOpen S K z m ∩ ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi)) :=
    ((h04.1.domains z hz hs m).1.inter
      (isOpen_univ.prod isOpen_Ioo)).measurableSet
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume
    hQ.nullMeasurableSet hd hinj
  rw [hi] at h
  rw [n07aPhysicalMeasure_eq_openAngularStrip,
    n07a_canonicalMeasure_eq_openAngularStrip]
  unfold n07aChartDensity
  simpa only [n07a_planeJacobian_eq_det] using h

/-- Actual a.e. equality pulls back from canonical to physical representatives. -/
theorem n07a_chart_ae_pullback {E : Type*}
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → E}
    (he : f =ᵐ[canonicalMeasure S K m] g) :
    (fun p => f (K.chart z m p)) =ᵐ[n07aPhysicalMeasure S K z m]
      fun p => g (K.chart z m p) := by
  have hchart := (n07a_chart_aemeasurable h04 hz hs m).mono_ac
    (withDensity_absolutelyContinuous _ (n07aChartDensity K z m))
  rw [← n07a_chart_map_withDensity h04 hz hs m] at he
  exact (withDensity_ae_eq (n07a_chartDensity_aemeasurable h04 hz hs m)
    (n07a_chartDensity_ne_zero_ae h04 hz hs m)).mp (ae_of_ae_map hchart he)

/-- An a.e. inverse Jacobian bound controls the unweighted physical
measure by the actual Jacobian measure. -/
theorem n07a_physicalMeasure_le_jacobian
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ᵐ p ∂n07aPhysicalMeasure S K z m,
      |planeJacobian (K.chart z m) p|⁻¹ ≤ A) :
    n07aPhysicalMeasure S K z m ≤
      ENNReal.ofReal A •
        (n07aPhysicalMeasure S K z m).withDensity
          (n07aChartDensity K z m) := by
  have hb : ∀ᵐ p ∂n07aPhysicalMeasure S K z m,
      (1 : PolarPoint → ℝ≥0∞) p ≤
        (ENNReal.ofReal A • n07aChartDensity K z m) p := by
    filter_upwards [hbound, n07aPhysicalMeasure_ae h04 hz hs m] with p hb hp
    have hj : 0 < |planeJacobian (K.chart z m) p| :=
      abs_pos.mpr ((h04.1.charts z hz hs m).2.2.2.2.2.2.2 p hp).2.1
    have hmul : 1 ≤ A * |planeJacobian (K.chart z m) p| :=
      (inv_le_iff_one_le_mul₀ hj).mp hb
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
    (hbound : ∀ᵐ p ∂n07aPhysicalMeasure S K z m,
      |planeJacobian (K.chart z m) p|⁻¹ ≤ A)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (canonicalMeasure S K m)) :
    MemLp (fun p => f (K.chart z m p)) 2
      (n07aPhysicalMeasure S K z m) := by
  have hchart := (n07a_chart_aemeasurable h04 hz hs m).mono_ac
    (withDensity_absolutelyContinuous _ (n07aChartDensity K z m))
  rw [← n07a_chart_map_withDensity h04 hz hs m] at hf
  have hp := (hf.comp_of_map hchart).smul_measure (c := ENNReal.ofReal A)
    ENNReal.ofReal_ne_top
  exact MemLp.mono_measure
    (n07a_physicalMeasure_le_jacobian h04 hz hs m hA hbound) hp

/-- Closed current geometry gives a finite inverse-Jacobian bound on
this state's actual fundamental piece. No uniform estimate is asserted. -/
theorem n07a_current_inverseJacobian_bounded
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ p ∂n07aPhysicalMeasure S K z m,
      |planeJacobian (K.chart z m) p|⁻¹ ≤ A := by
  have hf : ∀ p ∈ physicalPieceClosed S K z m,
      ContDiffAt ℝ ∞ (fun q => |planeJacobian (K.chart z m) q|⁻¹) p := by
    intro p hp
    have h := (h04.1.boundary z hz hs m).2.2.2.2.1 p hp
    exact ((ContinuousFlexibility.contDiffAt_planeJacobian h.1).abs h.2.2.1).inv
      (abs_ne_zero.mpr h.2.2.1)
  obtain ⟨A, hA, hb⟩ := n07a_physical_mixedDerivative_bound_ae h04 hz hs m hf 0 0
  refine ⟨A, hA, ?_⟩
  simpa only [spaces_mixedDerivative_zero, abs_inv, abs_abs] using hb

/-- The actual current chart pulls every canonical L² function to its
state-dependent physical piece. The qualitative bound comes from the
closed atlas geometry already present in N04. -/
theorem n07a_current_chart_memLp_pullback
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : MemLp f 2 (canonicalMeasure S K m)) :
    MemLp (fun p => f (K.chart (liftSectorParameter S C z) m p)) 2
      (n07aPhysicalMeasure S K (liftSectorParameter S C z) m) := by
  obtain ⟨A, hA, hb⟩ := n07a_current_inverseJacobian_bounded h04 hz' hs m
  exact n07a_chart_memLp_pullback h04 hz' hs m hA hb hf

end ContinuousFlexibility.Analysis
