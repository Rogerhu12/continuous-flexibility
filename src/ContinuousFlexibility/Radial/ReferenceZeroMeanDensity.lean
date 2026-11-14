module

public import ContinuousFlexibility.Analysis.SmoothCompactL2MeanDensity
public import ContinuousFlexibility.Radial.ReferenceWeightedCompact
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Exact zero-mean radial source approximation

A fixed unit-integral bump repairs the ordinary zero-mode compatibility
condition after smooth weighted approximation. The integral error tends to
zero independently of the singular Hilbert weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements
open ContinuousFlexibility.Analysis

/-- A genuine smooth radial test of ordinary integral one, supported
strictly inside the open core. -/
theorem exists_reference_unitIntegral_bump {D : ReferenceData} (hab : D.a < D.b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ radialCore D ∧
      (∫ r in D.a..D.b, η r) = 1 := by
  let c : ℝ := (D.a + D.b) / 2
  let b : ContDiffBump c :=
    ⟨(D.b - D.a) / 8, (D.b - D.a) / 4, by linarith, by linarith⟩
  let η : ℝ → ℝ := b.normed volume
  have hsupp : tsupport η ⊆ radialCore D := by
    rw [show tsupport η = Metric.closedBall c b.rOut from b.tsupport_normed_eq]
    intro r hr
    have hr' := abs_le.mp (show |r - c| ≤ b.rOut by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hr)
    change D.a < r ∧ r < D.b
    dsimp [c, b] at hr'
    constructor <;> linarith
  refine ⟨η, b.contDiff_normed, b.hasCompactSupport_normed, hsupp, ?_⟩
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  change (∫ r in radialCore D, η r) = 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr =>
    image_eq_zero_of_notMem_tsupport (fun hs => hr (hsupp hs)))]
  exact b.integral_normed

/-- Weighted radial L² approximation preserving the actual ordinary
zero-integral condition exactly at every approximating term. -/
theorem exists_referenceRadial_zeroMean_approximation {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M))
    (hfi : IntervalIntegrable f volume D.a D.b)
    (hzero : (∫ r in D.a..D.b, f r) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ radialCore D ∧
      (∫ r in D.a..D.b, g r) = 0 ∧
      ∃ hg : MemLp g 2 (referenceRadialWeightedMeasure D γ M),
        ‖hg.toLp g - hf.toLp f‖ < ε := by
  have hgD : RadialProfileGeometry D := by obtain ⟨C, hC⟩ := hD; exact hC.1
  have hpart : RadialPartition D := by obtain ⟨C, hC⟩ := hD; exact hC.2.1
  let μ := referenceRadialWeightedMeasure D γ M
  let ν := volume.restrict (radialCore D)
  letI : IsFiniteMeasure ν := ⟨by
    change (volume.restrict (Ioo D.a D.b)) univ < ⊤
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  have hfiν : Integrable f ν :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hgD.2.1.le).mp hfi
  have hzeroν : (∫ r, f r ∂ν) = 0 := by
    simpa only [ν, radialCore, intervalIntegral.integral_of_le hgD.2.1.le,
      integral_Ioc_eq_integral_Ioo] using hzero
  obtain ⟨η, hη, hηc, hηs, hηi⟩ := exists_reference_unitIntegral_bump hgD.2.1
  have hημ : MemLp η 2 μ := memLp_of_continuous_compact_support_inside
    (fun K hK hcore => referenceRadialWeightedMeasure_compact_lt_top hD γ M hK hcore)
    hη.continuous hηc hηs
  have hηiν : (∫ r, η r ∂ν) = 1 := by
    simpa only [ν, radialCore, intervalIntegral.integral_of_le hgD.2.1.le,
      integral_Ioc_eq_integral_Ioo] using hηi
  let δ : ℝ := ε / (2 * (‖hημ.toLp η‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (‖hημ.toLp η‖ + 1) = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt (show 0 < ‖hημ.toLp η‖ + 1 by positivity)]
  obtain ⟨g, hg, hgc, hgs, hgμ, hnorm, hint⟩ :=
    Analysis.MemLp.exists_contDiff_compact_approximation_integral hf hfiν
      isOpen_Ioo (referenceRadialWeightedMeasure_ae_core hpart γ M)
      (ae_restrict_mem measurableSet_Ioo)
      (fun K hK hcore => referenceRadialWeightedMeasure_compact_lt_top hD γ M hK hcore) hδ
  let c : ℝ := ∫ r, g r ∂ν
  let u : ℝ → ℝ := fun r => g r - c * η r
  have hc : |c| < δ := by
    simpa only [hzeroν, sub_zero] using hint
  have hu : ContDiff ℝ ∞ u := hg.sub (contDiff_const.mul hη)
  have huc : HasCompactSupport u := by
    have heq : u = g + -((fun _ => c) * η) := by
      funext r
      simp only [u, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
    rw [heq]
    exact hgc.add ((hηc.mul_left (f := fun _ => c)).neg)
  have hus : tsupport u ⊆ radialCore D := by
    exact (tsupport_sub g (fun r => c * η r)).trans
      (union_subset hgs (tsupport_mul_subset_right.trans hηs))
  have huμ : MemLp u 2 μ := hgμ.sub (hημ.const_mul c)
  have hgiν : Integrable g ν :=
    (hg.continuous.integrable_of_hasCompactSupport hgc).restrict
  have hηintν : Integrable η ν :=
    (hη.continuous.integrable_of_hasCompactSupport hηc).restrict
  have huint : (∫ r in D.a..D.b, u r) = 0 := by
    rw [intervalIntegral.integral_of_le hgD.2.1.le, integral_Ioc_eq_integral_Ioo]
    change (∫ r, g r - c * η r ∂ν) = 0
    rw [integral_sub hgiν (hηintν.const_mul c), integral_const_mul, hηiν, mul_one]
    exact sub_self c
  have heq : huμ.toLp u = hgμ.toLp g - c • hημ.toLp η := by
    apply Lp.ext
    filter_upwards [huμ.coeFn_toLp, hgμ.coeFn_toLp, hημ.coeFn_toLp,
      Lp.coeFn_sub (hgμ.toLp g) (c • hημ.toLp η), Lp.coeFn_smul c (hημ.toLp η)]
      with r hur hgr hηr hsub hsmul
    simp only [u, hur, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hgr, hηr]
  refine ⟨u, hu, huc, hus, huint, huμ, ?_⟩
  rw [heq]
  calc
    ‖hgμ.toLp g - c • hημ.toLp η - hf.toLp f‖ =
        ‖(hgμ.toLp g - hf.toLp f) - c • hημ.toLp η‖ := by congr 1; abel
    _ ≤ ‖hgμ.toLp g - hf.toLp f‖ + |c| * ‖hημ.toLp η‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using
        norm_sub_le (hgμ.toLp g - hf.toLp f) (c • hημ.toLp η)
    _ < ε := by
      have hmul := mul_le_mul_of_nonneg_right hc.le (norm_nonneg (hημ.toLp η))
      nlinarith

end ContinuousFlexibility.Radial
