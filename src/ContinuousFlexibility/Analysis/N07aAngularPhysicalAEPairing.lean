module

public import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals
public import ContinuousFlexibility.Analysis.N07aPeriodicRadialPairing
public import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# The same periodic physical representative retains every original pairing

A half-period a.e. equality between genuinely π-periodic functions extends
to the full physical 2π measure by the actual half-period translation.
Consequently their pairings agree against arbitrary tests, including the
original 2π-periodic RadialTest class. No periodicity of the test or
integrability shortcut is needed for this a.e. invariance statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial

variable {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07a_fullPeriod_ae_of_half {μ : Measure ℝ} [SFinite μ]
    {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (hg : Function.Periodic g (0, Real.pi))
    (he : f =ᵐ[μ.prod angleMeasure] g) :
    f =ᵐ[μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))] g := by
  have hpres : MeasurePreserving (fun p : PolarPoint => (p.1, p.2 - Real.pi))
      (μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))) (μ.prod angleMeasure) :=
    (MeasurePreserving.id μ).prod n07aAngularHalfShift_preserving
  have hshift := hpres.quasiMeasurePreserving.ae_eq_comp he
  have hupper : f =ᵐ[μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))] g := by
    filter_upwards [hshift] with p hp
    have hpSub : p - (0, Real.pi) = (p.1, p.2 - Real.pi) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
    have hfs : f (p.1, p.2 - Real.pi) = f p := by
      simpa only [hpSub] using hf.sub_eq p
    have hgs : g (p.1, p.2 - Real.pi) = g p := by
      simpa only [hpSub] using hg.sub_eq p
    exact hfs.symm.trans (hp.trans hgs)
  have hsum : μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) =
      μ.prod angleMeasure + μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi))) := by
    rw [← Ioc_union_Ioc_eq_Ioc Real.pi_pos.le
        (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos]),
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.prod_add]
    rfl
  rw [hsum]
  exact ae_add_measure_iff.mpr ⟨he, hupper⟩

/-- Arbitrary full-period tests have identical original physical pairings. -/
theorem n07a_physicalPairing_congr_ae (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (hg : Function.Periodic g (0, Real.pi))
    (he : f =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] g)
    (φ : PolarPoint → ℝ) (w : ℝ → ℝ) :
    (∫ r in D.a..D.b, w r * radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, w r * radialAngularMean (fun θ => g (r, θ) * φ (r, θ)) := by
  have he' : f =ᵐ[(volume.restrict (Ioo D.a D.b)).prod angleMeasure] g := by
    simpa only [n07aCanonicalMeasure_eq_prod, n07aRadialIntervalData] using he
  have hrows := Measure.ae_ae_of_ae_prod (n07a_fullPeriod_ae_of_half hf hg he')
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← restrict_Ioo_eq_restrict_Ioc]
  apply integral_congr_ae
  filter_upwards [hrows] with r hr
  apply congrArg (w r * ·)
  unfold radialAngularMean
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  apply congrArg ((2 * Real.pi)⁻¹ * ·)
  exact integral_congr_ae (hr.mono fun θ hθ => congrArg (· * φ (r, θ)) hθ)

theorem n07a_referenceRow_congr_ae (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (hg : Function.Periodic g (0, Real.pi))
    (he : f =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] g) :
    referenceRow D f = referenceRow D g :=
  n07a_physicalPairing_congr_ae hab hf hg he
    (fun p => cosineMode 2 p.2) (referenceColumn D)

/-- Only equality after multiplication by the actual row column is
required to preserve the normalization functional. -/
theorem n07a_referenceRow_congr_weighted_ae (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (hg : Function.Periodic g (0, Real.pi))
    (he : (fun p => referenceColumn D p.1 * f p) =ᵐ[
      canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0]
        fun p => referenceColumn D p.1 * g p) :
    referenceRow D f = referenceRow D g := by
  have hfp : Function.Periodic (fun p : PolarPoint => referenceColumn D p.1 * f p)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero, hf p]
  have hgp : Function.Periodic (fun p : PolarPoint => referenceColumn D p.1 * g p)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero, hg p]
  have h := n07a_physicalPairing_congr_ae hab hfp hgp he
    (fun p => cosineMode 2 p.2) (fun _ => 1)
  simpa only [one_mul, mul_assoc, radialAngularMean_const_mul,
    referenceRow, referenceMode] using h

end ContinuousFlexibility.Analysis
