module

public import ContinuousFlexibility.Analysis.N01aReferenceModeConvergence
public import ContinuousFlexibility.Analysis.N01aReferenceTestExtension

/-!
# Identification of the pure-row inverse's actual second mode

The smooth-core closure, ordinary-support natural tests, and true border
determine the mode.  Weighted membership of the eigenfunction is not an
input to this argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

theorem referenceGraph_pure_row_mode_natural {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hkernel : RadialNaturalKernels D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    {U : RadialUnknown} {η : ℝ}
    (hgraph : ReferenceGraph D γ M₀ M₁ U ((0 : PolarPoint → ℝ), η)) :
    NaturalRadialNull D 2 (referenceMode U.1 2) := by
  have hchi : ContDiff ℝ ∞ D.chiLeft := hborder.2.2.2.2.1
  have hU := hgraph.memLp_two hgeo.2.1.le hpart hchi hγ hcore
  have hq := referenceMode_memLp_two hU 2
  have hscalar := referenceGraph_pure_row_scalar_eq_zero hgeo hpart hkernel hborder
    hγ hcore hgraph
  obtain ⟨Un, Fn, an, hn, hF, hUn⟩ := hcore U ((0 : PolarPoint → ℝ), η) hgraph
  have hqn (n : ℕ) : MemLp (referenceMode (Un n).1 2) 2
      (volume.restrict (radialCore D)) :=
    referenceMode_memLp_two
      (continuous_memLp_radialPhysicalMeasure (hn n).2.1.1.continuous) 2
  have hqconv := tendsto_referenceMode_core_square hgeo.2.1.le hpart hchi.continuous hγ
    an hU (fun n => (hn n).2.1.1.continuous) (fun n => (hn n).2.2) hUn 2 (by decide)
  have hscalarN : Tendsto (fun n => (Un n).2) atTop (𝓝 0) := by
    simpa only [Prod.snd_sub, hscalar, sub_zero] using
      tendsto_output_scalar_of_normSquare hgeo.2.1.le γ M₁ (fun n => Un n - U) an hUn
  obtain ⟨C, hC, htestBound⟩ :=
    exists_smooth_reference_mode_test_bound hgeo hpart hborder hγ M₀
  refine ⟨memLp_radialHilbertMeasure_of_memLp hgeo hq, ?_⟩
  intro ψ hψ _ hs
  have hflat := endpointFlat_of_support_subset hψ hs
  obtain ⟨B, hB, hψB⟩ := hflat.exists_bound
  have hκ : MemLp (Radial.radialJacobi 4 D.w ψ) 2
      (volume.restrict (radialCore D)) :=
    continuousOn_memLp_two_radialCore (continuousOn_radialJacobi hgeo.2.2.1.1 hψ hgeo.1 4)
  have hpair : Tendsto
      (fun n => ∫ r in D.a..D.b,
        referenceMode (Un n).1 2 r * Radial.radialJacobi 4 D.w ψ r) atTop
      (𝓝 (∫ r in D.a..D.b, referenceMode U.1 2 r * Radial.radialJacobi 4 D.w ψ r)) := by
    simpa only [radialCore, restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le hgeo.2.1.le] using
      n01a_tendsto_integral_mul_of_integral_sq hqn hq hκ hqconv
  have hcombo := (hpair.add
    (hscalarN.mul_const (∫ r in D.a..D.b, referenceColumn D r * ψ r))).abs
  have hcombo0 : Tendsto (fun n =>
      |(∫ r in D.a..D.b, referenceMode (Un n).1 2 r * Radial.radialJacobi 4 D.w ψ r) +
        (Un n).2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall fun n =>
        htestBound M₁ (Un n) (Fn n) (hn n).1 (hn n).2.1 ψ hflat B hB.le hψB η)
    simpa only [Real.sqrt_zero, mul_zero] using
      hF.sqrt.const_mul (C * (B * Real.sqrt 2))
  have hz : |∫ r in D.a..D.b,
      referenceMode U.1 2 r * Radial.radialJacobi 4 D.w ψ r| = 0 := by
    have hcombo' : Tendsto (fun n =>
        |(∫ r in D.a..D.b, referenceMode (Un n).1 2 r * Radial.radialJacobi 4 D.w ψ r) +
          (Un n).2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r)|) atTop
        (𝓝 |∫ r in D.a..D.b,
          referenceMode U.1 2 r * Radial.radialJacobi 4 D.w ψ r|) := by
      simpa only [zero_mul, add_zero] using hcombo
    exact tendsto_nhds_unique hcombo' hcombo0
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using abs_eq_zero.mp hz

/-- The actual normalization row fixes the scalar in the natural kernel. -/
theorem referenceGraph_pure_row_mode_eq {D : ReferenceData}
    (hgeo : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hkernel : RadialNaturalKernels D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    {U : RadialUnknown} {η : ℝ}
    (hgraph : ReferenceGraph D γ M₀ M₁ U ((0 : PolarPoint → ℝ), η)) :
    referenceMode U.1 2 =ᵐ[volume.restrict (radialCore D)] fun r => η * D.phi r := by
  have hnull := referenceGraph_pure_row_mode_natural hgeo hpart hkernel hborder hγ hcore hgraph
  obtain ⟨c, hc⟩ := (hkernel.2.1 (referenceMode U.1 2)).mp hnull
  have hcrad : referenceMode U.1 2 =ᵐ[volume.restrict (radialCore D)]
      fun r => c * D.phi r := (radialHilbertMeasure_ae_iff hgeo).mp hc
  have hcio : referenceMode U.1 2 =ᵐ[volume.restrict (Ioc D.a D.b)]
      fun r => c * D.phi r := by
    simpa only [radialCore, restrict_Ioo_eq_restrict_Ioc] using hcrad
  have hrow : referenceRow D U.1 = c := by
    unfold referenceRow
    calc
      _ = ∫ r in D.a..D.b, referenceColumn D r * (c * D.phi r) := by
        rw [intervalIntegral.integral_of_le hgeo.2.1.le,
          intervalIntegral.integral_of_le hgeo.2.1.le]
        exact integral_congr_ae (hcio.mono fun r hr => by dsimp only; rw [hr])
      _ = c * ∫ r in D.a..D.b, referenceColumn D r * D.phi r := by
        rw [show (fun r => referenceColumn D r * (c * D.phi r)) =
          (fun r => c * (referenceColumn D r * D.phi r)) by funext r; ring]
        exact intervalIntegral.integral_const_mul _ _
      _ = c := by rw [hborder.2.2.2.1, mul_one]
  have hcη : c = η := hrow.symm.trans hgraph.2.2.1
  simpa only [hcη] using hcrad

end ContinuousFlexibility.Statements
