import ContinuousFlexibility.Analysis.N01aReferenceScalar

/-!
# Extending smooth graph tests to ordinary-support radial tests

These are exactly the test functions in `NaturalRadialNull`.  Their support
may approach the end circles, while their interior cutoffs are valid tests
for the original two-dimensional distributional graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

theorem endpointFlat_of_support_subset {D : ReferenceData} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ radialCore D) : EndpointFlat D ψ := by
  refine ⟨hψ, fun r hr => ?_⟩
  by_contra hn
  have h := hs hn
  rcases hr with hleft | hright
  · exact (not_lt.mpr hleft) h.1
  · exact (not_lt.mpr hright) h.2

theorem tendsto_integral_radial_cutoff {D : ReferenceData} {ψ κ : ℝ → ℝ}
    (hab : D.a ≤ D.b) (hψ : EndpointFlat D ψ)
    (hκ : ContinuousOn κ (Icc D.a D.b)) :
    Tendsto (fun n => ∫ r in D.a..D.b,
      κ r * Radial.intervalCutoffTest D.a D.b ψ n r) atTop
      (𝓝 (∫ r in D.a..D.b, κ r * ψ r)) := by
  have hi : IntervalIntegrable (fun r => κ r * ψ r) volume D.a D.b :=
    (hκ.mul hψ.1.continuous.continuousOn).intervalIntegrable_of_Icc hab
  have h := Radial.tendsto_integral_intervalCutoffTest
    (μ := volume.restrict (Ioc D.a D.b)) hψ.support_subset
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi)
  simpa only [intervalIntegral.integral_of_le hab] using h

theorem tendsto_radialWeakPairing_radial_cutoff {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) {ψ : ℝ → ℝ} (hψ : EndpointFlat D ψ) :
    Tendsto (fun n => radialWeakPairing D u (fun p =>
      Radial.intervalCutoffTest D.a D.b ψ n p.1 * Radial.cosineMode 2 p.2)) atTop
      (𝓝 (∫ r in D.a..D.b,
        referenceMode u 2 r * Radial.radialJacobi 4 D.w ψ r)) := by
  have hw : ContDiff ℝ ∞ D.w := hgeo.2.2.1.1
  have hq := contDiff_referenceMode hu 2
  have hwa : D.w D.a = 0 := hgeo.2.2.1.2 _ (Or.inl le_rfl)
  have hwb : D.w D.b = 0 := hgeo.2.2.1.2 _ (Or.inr le_rfl)
  have hmove (n : ℕ) :
      radialWeakPairing D u (fun p =>
        Radial.intervalCutoffTest D.a D.b ψ n p.1 * Radial.cosineMode 2 p.2) =
      ∫ r in D.a..D.b, Radial.radialJacobi 4 D.w (referenceMode u 2) r *
        Radial.intervalCutoffTest D.a D.b ψ n r := by
    have hsep := radialWeakPairing_cosine_test hw
      (Radial.contDiff_intervalCutoffTest hψ.1 n) u 2
    have hsep' : radialWeakPairing D u (fun p =>
        Radial.intervalCutoffTest D.a D.b ψ n p.1 * Radial.cosineMode 2 p.2) =
      ∫ r in D.a..D.b, referenceMode u 2 r *
        Radial.radialJacobi 4 D.w (Radial.intervalCutoffTest D.a D.b ψ n) r := by
      simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsep
    rw [hsep', integral_radialJacobi_symm hw hq
      (Radial.contDiff_intervalCutoffTest hψ.1 n) hgeo.1 hgeo.2.1.le hwa hwb 4]
    apply intervalIntegral.integral_congr
    intro r _
    exact mul_comm _ _
  have htarget : (∫ r in D.a..D.b,
      Radial.radialJacobi 4 D.w (referenceMode u 2) r * ψ r) =
        ∫ r in D.a..D.b, referenceMode u 2 r * Radial.radialJacobi 4 D.w ψ r := by
    rw [integral_radialJacobi_symm hw hq hψ.1 hgeo.1 hgeo.2.1.le hwa hwb 4]
    apply intervalIntegral.integral_congr
    intro r _
    exact mul_comm _ _
  simpa only [hmove, htarget] using
    tendsto_integral_radial_cutoff hgeo.2.1.le hψ
      (continuousOn_radialJacobi hw hq hgeo.1 4)

/-- Uniform source continuity for every ordinary-support smooth radial test. -/
theorem exists_smooth_reference_mode_test_bound {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hborder : RadialTrueBorder D) {γ : ℝ} (hγ : 0 < γ) (M₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₁ : ℝ) (U : RadialUnknown) (F : RadialSource),
      ReferenceGraph D γ M₀ M₁ U F → SmoothAdmissibleField D U →
      ∀ (ψ : ℝ → ℝ), EndpointFlat D ψ → ∀ B : ℝ, 0 ≤ B → (∀ r, |ψ r| ≤ B) → ∀ η : ℝ,
      |(∫ r in D.a..D.b, referenceMode U.1 2 r * Radial.radialJacobi 4 D.w ψ r) +
        U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r)| ≤
      C * (B * Real.sqrt 2) * Real.sqrt
        (sourceNormSquare D γ M₀ (F - ((0 : PolarPoint → ℝ), η))) := by
  obtain ⟨C, hC, hbound⟩ := exists_source_pairing_bound hgeo.2.1.le hpart hγ M₀
  refine ⟨C, hC, fun M₁ U F hgraph hU ψ hψ B hB hψB η => ?_⟩
  let ψn (n : ℕ) (p : PolarPoint) : ℝ :=
    Radial.intervalCutoffTest D.a D.b ψ n p.1 * Radial.cosineMode 2 p.2
  have htest (n : ℕ) : RadialTest D (ψn n) :=
    radialTest_cosine (Radial.contDiff_intervalCutoffTest hψ.1 n)
      (Radial.intervalCutoffTest_hasCompactSupport D.a D.b ψ n)
      (Radial.intervalCutoffTest_tsupport_subset D.a D.b ψ n) 2
  have htestB (n : ℕ) (p : PolarPoint) : |ψn n p| ≤ B * Real.sqrt 2 := by
    have hcos : |Radial.cosineMode 2 p.2| ≤ Real.sqrt 2 := by
      rw [Radial.cosineMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one ((2 : ℕ) * p.2)) (Real.sqrt_nonneg 2)
    dsimp only [ψn]
    rw [abs_mul]
    exact mul_le_mul
      ((Radial.abs_intervalCutoffTest_le D.a D.b ψ n p.1).trans (hψB p.1)) hcos
      (abs_nonneg _) hB
  have hcol : ContinuousOn (referenceColumn D) (Icc D.a D.b) :=
    continuousOn_radialJacobi (hgeo.2.2.1.1.mul hborder.1)
      hgeo.2.2.2.1.1 hgeo.1 4
  have hlim := ((tendsto_radialWeakPairing_radial_cutoff hgeo hU.1 hψ).add
    ((tendsto_integral_radial_cutoff hgeo.2.1.le hψ hcol).const_mul U.2)).abs
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have hg := hgraph.2.2.2 (ψn n) (htest n)
  dsimp only [ψn] at hg
  rw [referenceColumn_cosine_test] at hg
  rw [hg]
  simpa only [ψn, Prod.fst_sub, Pi.sub_apply, Pi.zero_apply, sub_zero] using
    hbound (F - ((0 : PolarPoint → ℝ), η)) (hgraph.2.1.sub_pure_row η)
      (ψn n) (B * Real.sqrt 2) (by positivity) (htestB n)

end ContinuousFlexibility.Statements
