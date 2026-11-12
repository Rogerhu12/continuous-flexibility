import ContinuousFlexibility.Analysis.N01aReferenceGreen
import ContinuousFlexibility.Radial.TailKernelTestExtension

/-!
# Interior cutoff tests approaching the actual reference eigenfunction

Green symmetry removes all derivatives of the cutoff before passing to the
limit.  The resulting test bounds are uniform even though the cutoff support
approaches both end circles.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

theorem EndpointFlat.support_subset {D : ReferenceData} {f : ℝ → ℝ}
    (hf : EndpointFlat D f) : Function.support f ⊆ radialCore D := by
  intro r hr
  by_contra hn
  apply hr
  apply hf.2 r
  simpa only [radialCore, mem_Ioo, not_and_or, not_lt] using hn

theorem EndpointFlat.exists_bound {D : ReferenceData} {f : ℝ → ℝ}
    (hf : EndpointFlat D f) : ∃ B : ℝ, 0 < B ∧ ∀ r, |f r| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc D.a D.b) hf.1.continuous.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun r => ?_⟩
  by_cases hr : r ∈ Icc D.a D.b
  · exact (hB r hr).trans (le_max_right _ _)
  · have hz : f r = 0 := hf.2 r (by
      have hsplit : r < D.a ∨ D.b < r := by
        simpa only [mem_Icc, not_and_or, not_le] using hr
      exact hsplit.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))
    rw [hz, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)

def referencePhiCutoff (D : ReferenceData) (n : ℕ) : ℝ → ℝ :=
  Radial.intervalCutoffTest D.a D.b D.phi n

def referencePhiCosineCutoff (D : ReferenceData) (n : ℕ) : PolarPoint → ℝ :=
  fun p => referencePhiCutoff D n p.1 * Radial.cosineMode 2 p.2

theorem contDiff_referencePhiCutoff {D : ReferenceData}
    (hphi : ContDiff ℝ ∞ D.phi) (n : ℕ) : ContDiff ℝ ∞ (referencePhiCutoff D n) :=
  Radial.contDiff_intervalCutoffTest hphi n

theorem radialTest_referencePhiCosineCutoff {D : ReferenceData}
    (hphi : ContDiff ℝ ∞ D.phi) (n : ℕ) :
    RadialTest D (referencePhiCosineCutoff D n) :=
  radialTest_cosine (contDiff_referencePhiCutoff hphi n)
    (Radial.intervalCutoffTest_hasCompactSupport D.a D.b D.phi n)
    (Radial.intervalCutoffTest_tsupport_subset D.a D.b D.phi n) 2

theorem abs_referencePhiCosineCutoff_le {D : ReferenceData} {B : ℝ}
    (hB : ∀ r, |D.phi r| ≤ B) (n : ℕ) (p : PolarPoint) :
    |referencePhiCosineCutoff D n p| ≤ B * Real.sqrt 2 := by
  have hc : |Radial.cosineMode 2 p.2| ≤ Real.sqrt 2 := by
    rw [Radial.cosineMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_cos_le_one ((2 : ℕ) * p.2)) (Real.sqrt_nonneg 2)
  have hcut : |referencePhiCutoff D n p.1| ≤ B :=
    (Radial.abs_intervalCutoffTest_le D.a D.b D.phi n p.1).trans (hB p.1)
  rw [referencePhiCosineCutoff, abs_mul]
  exact mul_le_mul hcut hc (abs_nonneg _) ((abs_nonneg (D.phi p.1)).trans (hB p.1))

theorem tendsto_integral_referencePhiCutoff {D : ReferenceData}
    (hab : D.a ≤ D.b) (hphi : EndpointFlat D D.phi) {κ : ℝ → ℝ}
    (hκ : ContinuousOn κ (Icc D.a D.b)) :
    Tendsto (fun n => ∫ r in D.a..D.b, κ r * referencePhiCutoff D n r) atTop
      (𝓝 (∫ r in D.a..D.b, κ r * D.phi r)) := by
  have hi : IntervalIntegrable (fun r => κ r * D.phi r) volume D.a D.b :=
    (hκ.mul hphi.1.continuous.continuousOn).intervalIntegrable_of_Icc hab
  have h := Radial.tendsto_integral_intervalCutoffTest
    (μ := volume.restrict (Ioc D.a D.b)) hphi.support_subset
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi)
  simpa only [referencePhiCutoff, intervalIntegral.integral_of_le hab] using h

/-- The natural kernel condition applies to the smooth admissible mode after
Green symmetry has moved the differential operator off the cutoff. -/
theorem tendsto_radialWeakPairing_referencePhiCutoff {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hkernel : RadialNaturalKernels D)
    {U : RadialUnknown} (hU : SmoothAdmissibleField D U) :
    Tendsto (fun n => radialWeakPairing D U.1 (referencePhiCosineCutoff D n))
      atTop (𝓝 0) := by
  have hw : ContDiff ℝ ∞ D.w := hgeo.2.2.1.1
  have hphi : EndpointFlat D D.phi := hgeo.2.2.2.1
  have hq := contDiff_referenceMode hU.1 2
  have hmove (n : ℕ) :
      radialWeakPairing D U.1 (referencePhiCosineCutoff D n) =
        ∫ r in D.a..D.b,
          Radial.radialJacobi 4 D.w (referenceMode U.1 2) r * referencePhiCutoff D n r := by
    have hsep : radialWeakPairing D U.1 (referencePhiCosineCutoff D n) =
        ∫ r in D.a..D.b, referenceMode U.1 2 r *
          Radial.radialJacobi 4 D.w (referencePhiCutoff D n) r := by
      change radialWeakPairing D U.1
        (fun p : PolarPoint => referencePhiCutoff D n p.1 * Radial.cosineMode 2 p.2) = _
      simpa only [Nat.cast_ofNat,
        show (2 : ℝ) ^ 2 = 4 by norm_num] using
        radialWeakPairing_cosine_test hw (contDiff_referencePhiCutoff hphi.1 n) U.1 2
    rw [hsep, integral_radialJacobi_symm hw hq (contDiff_referencePhiCutoff hphi.1 n)
      hgeo.1 hgeo.2.1.le (hgeo.2.2.1.2 _ (Or.inl le_rfl))
      (hgeo.2.2.1.2 _ (Or.inr le_rfl)) 4]
    apply intervalIntegral.integral_congr
    intro r _
    exact mul_comm _ _
  have hlim := tendsto_integral_referencePhiCutoff hgeo.2.1.le hphi
    (continuousOn_radialJacobi hw hq hgeo.1 4)
  have hzero : (∫ r in D.a..D.b,
      Radial.radialJacobi 4 D.w (referenceMode U.1 2) r * D.phi r) = 0 := by
    simpa only [mul_comm] using natural_phi_pairing_referenceMode hkernel hU
  simpa only [hmove, hzero] using hlim

theorem tendsto_referenceColumn_referencePhiCutoff {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    Tendsto (fun n => ∫ r in D.a..D.b,
      referenceColumn D r * referencePhiCutoff D n r) atTop (𝓝 1) := by
  have hcol : ContinuousOn (referenceColumn D) (Icc D.a D.b) :=
    continuousOn_radialJacobi (hgeo.2.2.1.1.mul hborder.1)
      hgeo.2.2.2.1.1 hgeo.1 4
  simpa only [hborder.2.2.2.1] using
    tendsto_integral_referencePhiCutoff hgeo.2.1.le hgeo.2.2.2.1 hcol

end ContinuousFlexibility.Statements
