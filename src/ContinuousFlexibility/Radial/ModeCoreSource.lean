import ContinuousFlexibility.Radial.ModeCompactLocal
import ContinuousFlexibility.Radial.ModeWeakLinearity

/-!
# Normalized border and actual smooth core sources

The true border divided by the Hilbert density is an actual L² vector.
This supplies the symmetric border row, and the smooth core source for
the existing modal weak equation, including the inactive scalar identity
used to place every frequency on the same product space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchingColumn_expansion {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (r : ℝ) :
    referenceColumn D r =
      D.chi r * radialJacobi 4 D.w D.phi r +
        D.w r * deriv D.chi r * (deriv D.phi r - 4 / r * D.phi r) := by
  have hg := matchingProfileGeometry hD
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hφ : ContDiff ℝ ∞ D.phi := hg.2.2.2.1.1
  have hdφ : ContDiff ℝ ∞ (deriv D.phi) := (contDiff_infty_iff_deriv.mp hφ).2
  have hwχ : ContDiff ℝ ∞ (fun t => D.w t * D.chi t) := hw.mul hB.1
  unfold referenceColumn radialJacobi
  rw [deriv_fun_mul (hwχ.differentiable (by simp) r) (hdφ.differentiable (by simp) r),
    deriv_fun_mul (hw.differentiable (by simp) r) (hB.1.differentiable (by simp) r),
    deriv_fun_mul (hw.differentiable (by simp) r) (hdφ.differentiable (by simp) r)]
  ring

def matchingBorderTest (D : ReferenceData) (r : ℝ) : ℝ :=
  referenceColumn D r / matchingDensity D r

theorem matchingBorderTest_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) :
    MemLp (matchingBorderTest D) 2 (radialHilbertMeasure D) := by
  have hg := matchingProfileGeometry hD
  have hφ : ContDiff ℝ ∞ D.phi := hg.2.2.2.1.1
  have hdφ : ContDiff ℝ ∞ (deriv D.phi) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdχ : ContDiff ℝ ∞ (deriv D.chi) := (contDiff_infty_iff_deriv.mp hB.1).2
  have hχ : MemLp D.chi ⊤ (radialHilbertMeasure D) :=
    matching_memLp_of_continuousOn hD hB.1.continuous.measurable
      hB.1.continuous.continuousOn ⊤
  have hmain : MemLp (fun r => D.chi r * matchingJacobiTest D 2 D.phi r) 2
      (radialHilbertMeasure D) :=
    hχ.fun_mul (matchingJacobiTest_memLp hD hφ 2)
  let q : ℝ → ℝ := fun r =>
    r ^ 2 / 12 * deriv D.chi r * (deriv D.phi r - 4 / r * D.phi r)
  have hqm : Measurable q := by
    have hφm : Measurable D.phi := hφ.continuous.measurable
    have hdφm : Measurable (deriv D.phi) := hdφ.continuous.measurable
    have hdχm : Measurable (deriv D.chi) := hdχ.continuous.measurable
    dsimp only [q]
    fun_prop
  have hratio : ContinuousOn (fun r : ℝ => 4 / r) (Icc D.a D.b) := by
    apply continuous_const.continuousOn.div continuous_id.continuousOn
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le hg.1 hr.1)
  have hqc : ContinuousOn q (Icc D.a D.b) :=
    (((continuous_id.pow 2).div_const 12).mul hdχ.continuous).continuousOn.mul
      (hdφ.continuous.continuousOn.sub (hratio.mul hφ.continuous.continuousOn))
  have hq : MemLp q 2 (radialHilbertMeasure D) :=
    matching_memLp_of_continuousOn hD hqm hqc 2
  apply (memLp_congr_ae ?_).mp (hmain.add hq)
  apply (radialHilbertMeasure_ae_iff hD).mpr
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  have hw0 : D.w r ≠ 0 := (hg.2.2.2.2.1 r hr).ne'
  have hr0 : r ≠ 0 := (lt_trans hg.1 hr.1).ne'
  dsimp only [matchingBorderTest, matchingJacobiTest, q]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
  rw [matchingColumn_expansion hD hB]
  unfold matchingDensity
  field_simp [hw0, hr0]
  <;> ring

def matchingBorderVector (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) : RadialModeL2 D :=
  (matchingBorderTest_memLp hD hB).toLp (matchingBorderTest D)

theorem matchingBorderVector_coe {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) :
    (matchingBorderVector D hD hB : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      matchingBorderTest D :=
  (matchingBorderTest_memLp hD hB).coeFn_toLp

theorem matchingColumn_mode_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (U : RadialModeL2 D) :
    IntervalIntegrable (fun r => referenceColumn D r * U r) volume D.a D.b := by
  have hi := (matchingDensity_integrable_iff hD
    (fun r => U r * matchingBorderTest D r)).mp
      ((Lp.memLp U).integrable_mul (matchingBorderTest_memLp hD hB))
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (matchingProfileGeometry hD).2.1.le).mpr
  apply hi.congr
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  unfold matchingBorderTest
  field_simp [(matchingDensity_pos hD hr).ne']
  <;> ring

theorem matchingColumn_integral_eq_inner {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (U : RadialModeL2 D) :
    (∫ r in D.a..D.b, referenceColumn D r * U r) =
      ⟪U, matchingBorderVector D hD hB⟫_ℝ := by
  calc
    (∫ r in D.a..D.b, referenceColumn D r * U r) =
        ∫ r in D.a..D.b, matchingDensity D r * U r * matchingBorderTest D r := by
      apply matchingInterval_congr_ae hD
      apply (radialHilbertMeasure_ae_iff hD).mpr
      filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
        with r hr
      unfold matchingBorderTest
      field_simp [(matchingDensity_pos hD hr).ne']
      <;> ring
    _ = _ := matchingSource_integral_eq_inner hD U (matchingBorderTest_memLp hD hB)

def matchingTestInput (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) : RadialModePair D :=
  (matchingSmoothVector D hD ψ hψ, s)

/-- The inactive scalar is extended by the identity. At frequency two the
source has the genuine symmetric border column and the genuine border row. -/
def matchingTestSource (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) (j : ℕ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) : RadialModePair D :=
  (-matchingJacobiVector D hD j ψ hψ +
      (if j = 2 then s else 0) • matchingBorderVector D hD hB,
    if j = 2 then ∫ r in D.a..D.b, referenceColumn D r * ψ r else s)

theorem matchingTestInput_coe {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    ((matchingTestInput D hD ψ hψ s).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ψ :=
  (matching_memLp_of_continuousOn hD hψ.continuous.measurable
    hψ.continuous.continuousOn 2).coeFn_toLp

theorem matchingTestSource_coe {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (j : ℕ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    ((matchingTestSource D hD hB j ψ hψ s).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -radialJacobi ((j : ℝ) ^ 2) D.w ψ r / matchingDensity D r +
        (if j = 2 then s else 0) * matchingBorderTest D r) := by
  let J := matchingJacobiVector D hD j ψ hψ
  let b := matchingBorderVector D hD hB
  let c : ℝ := if j = 2 then s else 0
  have hJ : (J : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] matchingJacobiTest D j ψ :=
    (matchingJacobiTest_memLp hD hψ j).coeFn_toLp
  have hb : (b : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] matchingBorderTest D :=
    matchingBorderVector_coe hD hB
  change ((-J + c • b : RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] _
  filter_upwards [Lp.coeFn_add (-J) (c • b), Lp.coeFn_neg J,
    Lp.coeFn_smul c b, hJ, hb] with r ha hn hc hj hb'
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at ha hn hc
  rw [ha, hn, hc, hj, hb']
  dsimp only [matchingJacobiTest, c]
  ring

theorem matchingTestSource_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (j : ℕ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) (U : RadialModePair D) :
    modePairing D U (matchingTestSource D hD hB j ψ hψ s) =
      -⟪U.1, matchingJacobiVector D hD j ψ hψ⟫_ℝ +
        (if j = 2 then
          U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) +
            s * ⟪U.1, matchingBorderVector D hD hB⟫_ℝ
        else U.2 * s) := by
  by_cases hj : j = 2
  · simp only [modePairing, matchingTestSource, hj, if_pos, inner_add_right,
      inner_neg_right, real_inner_smul_right]
    ring
  · simp only [modePairing, matchingTestSource, hj, if_neg, zero_smul, add_zero,
      inner_neg_right]

end ContinuousFlexibility.Radial
