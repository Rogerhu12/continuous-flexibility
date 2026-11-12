import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05CanonicalAngularTransport
import ContinuousFlexibility.Analysis.N05PeriodicPhysicalL2Norm
import ContinuousFlexibility.Analysis.N05CanonicalOutputChange
import ContinuousFlexibility.Analysis.N05CanonicalTests

/-!
# Actual angular weak derivatives after the canonical height transform

The genuine coordinate Jacobian transports a canonical test to its physical
test. The physical mean uses a full period while the canonical measure uses
a half period; their pairing differs by exactly pi. This identifies the
canonical weak derivative of the actual height transform, including odd jets.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Radial

theorem n05CanonicalTest_angular {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (j : ℕ) :
    CanonicalTest S K m (mixedDerivative 0 j φ) := by
  refine ⟨contDiff_mixedDerivative hφ.1 0 j, ?_, ?_⟩
  · intro p
    have hslice : Function.Periodic (fun θ => φ (p.1, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (p.1, θ)
    simpa only [mixedDerivative, iteratedDeriv_zero, Prod.fst_add,
      Prod.snd_add, add_zero] using n05_periodic_iteratedDeriv hslice j p.2
  · obtain ⟨J, hJ, hJI, hzero⟩ := hφ.2.2
    refine ⟨J, hJ, hJI, fun r hr θ => ?_⟩
    have hz : (fun t : ℝ => φ (r, t)) = (0 : ℝ → ℝ) :=
      funext (fun t => hzero r hr t)
    simp only [mixedDerivative, iteratedDeriv_zero, hz,
      iteratedDeriv_const_zero, Pi.zero_apply]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hab : D.a ≤ D.b)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include hab h hcoordinates

/-- This is the pairing for the actual inverse chart and actual height,
with the original physical angular mean and its full-period normalization. -/
theorem n05_canonicalHeight_angular_test_pairing (m : ℕ)
    {u : PolarPoint → ℝ} (hup : Function.Periodic u (0, Real.pi))
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, canonicalHeight S K (C.referenceState, 0) m u p * φ p
      ∂canonicalMeasure S K m) =
      Real.pi * ∫ r in D.a..D.b, radialAngularMean
        (fun θ => u (r, θ) * n05CanonicalAngularTransport S C K m φ (r, θ)) := by
  classical
  let z : AnnularState S × ℝ := (C.referenceState, 0)
  have hz : z ∈ stateNeighborhood S C base ε := n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S z.1 := n05_referenceState_sector h.1.1.1.2.2.1
  have hangle : ∀ p ∈ referencePhysicalPieceOpen S K m, (K.chart z m p).2 = p.2 := by
    intro p hp
    rw [(hcoordinates.1 m p hp).1]
  have ht := n05CanonicalAngularTransport_test h hcoordinates m hφ
  have htLp : MemLp (n05CanonicalAngularTransport S C K m φ) 2
      (radialPhysicalMeasure D) := r11b_continuous_memLp ht.1.continuous
  have hperiodic : Function.Periodic
      (fun p => u p * n05CanonicalAngularTransport S C K m φ p) (0, Real.pi) := by
    simpa only [Pi.mul_def] using
      hup.mul (n05CanonicalAngularTransport_periodic S C K m hφ.2.1)
  have hfull := n05_piPeriodic_integral_fullPeriod (J := radialCore D) measurableSet_Ioo
    hperiodic (hu.integrable_mul htLp)
  have hmean := r11b_integral_angularMean_mul_eq hab hu htLp
  change (∫ r in D.a..D.b, radialAngularMean
      (fun θ => u (r, θ) * n05CanonicalAngularTransport S C K m φ (r, θ))) =
    (2 * Real.pi)⁻¹ * ∫ p, u p * n05CanonicalAngularTransport S C K m φ p
      ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) at hmean
  rw [hfull] at hmean
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hsubset : Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      radialCore D ×ˢ Ioc (0 : ℝ) Real.pi :=
    fun p hp => ⟨(hpieces m).2.2 hp.1, hp.2⟩
  have hwhole :
      (∫ p, u p * n05CanonicalAngularTransport S C K m φ p
        ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) =
      ∫ p, u p * n05CanonicalAngularTransport S C K m φ p
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioo.prod measurableSet_Ioc) hsubset
    intro p hp
    have hpout : p.1 ∉ Ioo (K.physicalLeft m) (K.physicalRight m) :=
      fun hpi => hp.2 ⟨hpi, hp.1.2⟩
    simp only [n05CanonicalAngularTransport, if_neg hpout, mul_zero]
  calc
    _ = ∫ p, |planeJacobian (K.chart z m) p| *
        (canonicalHeight S K z m u (K.chart z m p) * φ (K.chart z m p))
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) :=
      n05_referenceCanonicalChart_integral h.2.2.2.2.1 hz hs m hangle _
    _ = ∫ p, u p * n05CanonicalAngularTransport S C K m φ p
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
      apply integral_congr_ae
      filter_upwards [n05_referenceCanonicalHeight_chart_ae h.2.2.2.2.1 hz hs m u,
        ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
      change |planeJacobian (K.chart z m) p| *
        (canonicalHeight S K z m u (K.chart z m p) * φ (K.chart z m p)) =
          u p * n05CanonicalAngularTransport S C K m φ p
      rw [hp, n05CanonicalAngularTransport_eq_actual h hcoordinates m φ
        ⟨hpm.1, mem_univ _⟩]
      ring
    _ = ∫ p, u p * n05CanonicalAngularTransport S C K m φ p
        ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := hwhole.symm
    _ = _ := by
      rw [hmean]
      field_simp [Real.pi_ne_zero] <;> ring

/-- Any actual canonical representatives inherit the physical weak jet.
Periodicity is needed for the two-period integral; no parity hypothesis is
imposed on the derivative representative. -/
theorem n05_weakCanonicalAngularDerivative_of_physical (m j : ℕ)
    {u d : PolarPoint → ℝ}
    (hup : Function.Periodic u (0, Real.pi))
    (hdp : Function.Periodic d (0, Real.pi))
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (hweak : n05_weakReferenceAngularJet D u d j)
    {f g : CanonicalL2 S K m}
    (hf : (f : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m u)
    (hg : (g : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m d) :
    WeakCanonicalAngularDerivative S K m f g j := by
  intro φ hφ
  have hleft : (∫ p, g p * φ p ∂canonicalMeasure S K m) =
      Real.pi * ∫ r in D.a..D.b, radialAngularMean
        (fun θ => d (r, θ) * n05CanonicalAngularTransport S C K m φ (r, θ)) := by
    have hmul : (fun p => g p * φ p) =ᵐ[canonicalMeasure S K m]
        (fun p => canonicalHeight S K (C.referenceState, 0) m d p * φ p) :=
      hg.mul (show φ =ᵐ[canonicalMeasure S K m] φ from Filter.EventuallyEq.rfl)
    rw [integral_congr_ae hmul]
    exact n05_canonicalHeight_angular_test_pairing hab h hcoordinates m hdp hd hφ
  have hright : (∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m) =
      Real.pi * ∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) *
        n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ) (r, θ)) := by
    have hmul : (fun p => f p * mixedDerivative 0 j φ p) =ᵐ[canonicalMeasure S K m]
        (fun p => canonicalHeight S K (C.referenceState, 0) m u p *
          mixedDerivative 0 j φ p) :=
      hf.mul (show mixedDerivative 0 j φ =ᵐ[canonicalMeasure S K m]
        mixedDerivative 0 j φ from Filter.EventuallyEq.rfl)
    rw [integral_congr_ae hmul]
    exact n05_canonicalHeight_angular_test_pairing hab h hcoordinates m hup hu
      (n05CanonicalTest_angular hφ j)
  rw [hleft, hright, hweak _ (n05CanonicalAngularTransport_test h hcoordinates m hφ)]
  simp_rw [n05CanonicalAngularTransport_angular]
  ring

end ContinuousFlexibility.Statements
