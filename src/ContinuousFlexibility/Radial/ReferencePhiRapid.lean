import ContinuousFlexibility.Radial.ReferenceModeComparison
import ContinuousFlexibility.Radial.ReferenceTestSqueeze
import ContinuousFlexibility.Radial.ReferenceGraphInterior
import ContinuousFlexibility.Radial.ReferenceModerateCoefficients

/-!
# Positive weighted decay of the actual homogeneous profile

Apply the given full inverse to the unit scalar source. Its genuine
second angular coefficient satisfies the modal graph, including the
larger endpoint-flat test class by affine squeezing. The same modal
inverse identifies that coefficient with phi. The first-normal estimate
and weak derivative uniqueness identify its normal coefficient with
phi'. Thus both weighted assertions follow from the original inverses,
without an extra cutoff-support or decay hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

/-- The unit scalar datum has zero ordinary source and is compatible at
every coefficient weight. -/
theorem sourceMember_unitBorder (D : ReferenceData) (γ M : ℝ) :
    SourceMember D γ M ((fun _ : PolarPoint => 0), 1) := by
  refine ⟨RadialCellIntegrable.zero D, ?_, (fun _ => rfl), (fun _ _ => rfl), ?_, ?_⟩
  · simpa only [sourceCellSquare, referenceCellSquare, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      radialAngularMean, intervalIntegral.integral_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · simpa only [radialAngularMean, intervalIntegral.integral_zero, mul_zero] using
      (intervalIntegrable_zero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume D.a D.b)
  · simp only [radialAngularMean, intervalIntegral.integral_zero, mul_zero]

private theorem referenceRadialCoefficient_zero_field (n : ℕ) (r : ℝ) :
    referenceRadialCoefficient (fun _ : PolarPoint => 0) n r = 0 := by
  change referenceAngularCoefficient (fun _ : ℝ => 0) n = 0
  rw [referenceAngularCoefficient_const]
  split_ifs <;> rfl

/-- The projected full graph is the genuine bordered modal graph. The
minus sign on its scalar is the frozen modal convention. -/
theorem referenceGraph_unitBorder_modeGraph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hgraph : ReferenceGraph D γ M₀ M₁ U ((fun _ : PolarPoint => 0), 1)) :
    ∃ V : RadialModeL2 D,
      (V : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] referenceRadialCoefficient U.1 1 ∧
      ModeFullGraph D 2 (V, -U.2) (0, 1) := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    dsimp only [radialCore]
    infer_instance
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨aL, hU⟩ := hgraph.1
  let u := referenceRadialCoefficient U.1 1
  have hW : ReferenceRadialWeighted D γ (-2 * M₁) u :=
    referenceRadialCoefficient_output_weighted hgeom.2.1.le hpart hU (by decide)
  have huLp : MemLp u 2 (volume.restrict (radialCore D)) :=
    ReferenceRadialWeighted.memLp hpart hγ hW
  have huI : IntegrableOn u (radialCore D) := huLp.integrable (by norm_num)
  have huH : MemLp u 2 (radialHilbertMeasure D) :=
    memLp_radialHilbertMeasure_of_memLp_core hD huLp
  let V : RadialModeL2 D := huH.toLp u
  have hV : (V : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u := huH.coeFn_toLp
  have hcolumn : ContDiff ℝ ∞ (referenceColumn D) := referenceColumn_contDiff hgeom hborder
  let v : ℝ → ℝ := fun r => -U.2 * referenceColumn D r
  have hvI : IntegrableOn v (radialCore D) :=
    (reference_memLp_radial_of_continuous D
      (continuous_const.mul hcolumn.continuous)).integrable (by norm_num)
  have hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ radialCore D →
      (∫ r in D.a..D.b, u r * radialJacobi 4 D.w ψ r) =
        ∫ r in D.a..D.b, v r * ψ r := by
    intro ψ hψ hψc hψs
    have h := referenceGraph_coefficient_equation hgeom hgraph 1 hψ hψc hψs
    have hsimp : (∫ r in D.a..D.b, u r * radialJacobi 4 D.w ψ r) +
        U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) = 0 := by
      simpa only [show (((2 * 1 : ℕ) : ℝ) ^ 2) = (4 : ℝ) by norm_num,
        ite_true, referenceRadialCoefficient_zero_field, zero_mul,
        intervalIntegral.integral_zero] using h
    simp only [v, mul_assoc, intervalIntegral.integral_const_mul]
    linarith only [hsimp]
  refine ⟨V, hV, ?_, ?_⟩
  · intro ψ hψ _hψc hψs
    have hext := radialJacobi_weak_extend_support_tests hgeom 4 huI hvI hweak hψ hψs
    have hVpair :
        (∫ r in D.a..D.b, V r * radialJacobi 4 D.w ψ r) =
          ∫ r in D.a..D.b, u r * radialJacobi 4 D.w ψ r := by
      apply matchingInterval_congr_ae hD
      filter_upwards [hV] with r hr
      rw [hr]
    have hzero : (∫ r in D.a..D.b,
        (12 * D.w r / r ^ 2) * (0 : RadialModeL2 D) r * ψ r) = 0 := by
      calc
        _ = ∫ _r in D.a..D.b, (0 : ℝ) := by
          apply matchingInterval_congr_ae hD
          filter_upwards [Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr
          simp only [hr, Pi.zero_apply, mul_zero, zero_mul]
        _ = 0 := by simp
    change (∫ r in D.a..D.b, V r * radialJacobi ((2 : ℝ) ^ 2) D.w ψ r) -
      (-U.2) * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -(∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * (0 : RadialModeL2 D) r * ψ r)
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num, hzero, hVpair, hext]
    simp only [v, mul_assoc, intervalIntegral.integral_const_mul]
    ring
  · change (∫ r in D.a..D.b, referenceColumn D r * V r) = 1
    calc
      _ = ∫ r in D.a..D.b, referenceColumn D r * u r := by
        apply matchingInterval_congr_ae hD
        filter_upwards [hV] with r hr
        rw [hr]
      _ = 1 := hgraph.2.2.1

/-- Modal uniqueness applies to the actual projected inverse output,
rather than being postulated as a relationship between two existentials. -/
theorem referenceGraph_unitBorder_coefficient_eq_phi {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hphi : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    {Gmode : RadialModePair D →L[ℝ] RadialModePair D}
    (hmode : ModeInverseProperties D 2 Gmode) {U : RadialUnknown}
    (hgraph : ReferenceGraph D γ M₀ M₁ U ((fun _ : PolarPoint => 0), 1)) :
    referenceRadialCoefficient U.1 1 =ᵐ[volume.restrict (radialCore D)] D.phi ∧ U.2 = 0 := by
  obtain ⟨V, hV, hVG⟩ := referenceGraph_unitBorder_modeGraph hD hborder hγ hgraph
  obtain ⟨hVphi, hscalar⟩ := modeFullGraph_two_zeroSource_eq_phi hD hborder hphi hmode hVG
  refine ⟨(radialHilbertMeasure_ae_iff hD).mp (hV.symm.trans hVphi), ?_⟩
  exact neg_eq_zero.mp hscalar

/-- Both phi and its first derivative inherit the same positive weighted
norm as the unit-border inverse and its first-normal derivative. -/
theorem referencePhi_weighted_of_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hphi : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    {Gmode : RadialModePair D →L[ℝ] RadialModePair D}
    (hmode : ModeInverseProperties D 2 Gmode)
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ReferenceRadialWeighted D γ (-2 * M₁) D.phi ∧
      ReferenceRadialWeighted D γ (-2 * M₁) (deriv D.phi) := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    dsimp only [radialCore]
    infer_instance
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  let F : RadialSource := ((fun _ : PolarPoint => 0), 1)
  have hF : SourceMember D γ M₀ F := sourceMember_unitBorder D γ M₀
  have hgraph := hG.1 F hF
  have hcoef := (referenceGraph_unitBorder_coefficient_eq_phi
    hD hborder hphi hγ hmode hgraph).1
  obtain ⟨aL, hU⟩ := hgraph.1
  have hweighted := referenceRadialCoefficient_output_weighted hgeom.2.1.le hpart hU
    (show (1 : ℕ) ≠ 0 by decide)
  have hphiW := hweighted.congr_ae hcoef
  obtain ⟨C, _hC, hfirst⟩ := hNormal
  have hzeroDerivative : WeakAngularDerivative D F.1 (fun _ => 0) := by
    intro ψ _hψ
    simp only [F, zero_mul, radialAngularMean, intervalIntegral.integral_zero,
      mul_zero, neg_zero]
  have hzeroMember : SourceDerivativeMember D γ M₀ (fun _ => 0) :=
    ⟨hF.1, hF.2.1⟩
  obtain ⟨ur, hur, hurW, _hbound⟩ := hfirst F (fun _ => 0) hF hzeroDerivative hzeroMember
  have hdW := referenceRadialCoefficient_output_zero_weighted hgeom.2.1.le hurW 1
  have hdI : LocallyIntegrableOn (referenceRadialCoefficient ur 1) (radialCore D) volume :=
    ((ReferenceRadialWeighted.memLp hpart hγ hdW).integrable (by norm_num)).locallyIntegrableOn
  have hdphi := reference_coefficient_normal_eq_deriv hgeom.2.1 hur 1
    hgeom.2.2.2.1.1.contDiffOn hcoef hdI
  exact ⟨hphiW, hdW.congr_ae hdphi⟩

theorem referencePhi_rapid_of_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hphi : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    {Gmode : RadialModePair D →L[ℝ] RadialModePair D}
    (hmode : ModeInverseProperties D 2 Gmode)
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ReferenceRapid D D.phi ∧ ReferenceRapid D (deriv D.phi) := by
  obtain ⟨hphiW, hdphiW⟩ :=
    referencePhi_weighted_of_inverse hD hborder hphi hγ hmode hG hNormal
  exact ⟨⟨γ, -2 * M₁, hγ, hphiW⟩, ⟨γ, -2 * M₁, hγ, hdphiW⟩⟩

end ContinuousFlexibility.Radial
