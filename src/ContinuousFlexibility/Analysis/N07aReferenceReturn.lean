module

public import ContinuousFlexibility.Analysis.N07aProfileHeight
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The actual reference characteristic return

At zero amplitude the corrected angular coefficient is the radial slope
divided by the radius. The actual reference flow therefore integrates to
the reference optical travel. Its return residual is zero in the actual
circle space, by the N02 decoder identity and decoder injectivity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

local instance n07aReferenceReturnStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
local instance n07aReferenceReturnStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
local instance n07aReferenceReturnStateAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := (inferInstance : AddCommGroup (AnnularState S)).toAddGroup
local instance n07aReferenceReturnStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := (inferInstance : Module ℝ (AnnularState S)).toSMul
local instance n07aReferenceReturnStateSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := (inferInstance : AddCommGroup (AnnularState S)).toSub

theorem n07a_polarCorrectedC_radialHeightField
    {h w : ℝ → ℝ} (hhw : ∀ r, HasDerivAt h (w r) r) {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) :
    polarCorrectedC w (Radial.radialHeightField h) p = deriv w p.1 / p.1 := by
  rw [polarCorrectedC_eq_residual_correction,
    Radial.polarCoordinateResidual_radialHeightField hhw hw]
  simp only [mul_zero, zero_div, sub_zero]
  unfold polarLinearC polarScale
  rw [Radial.heightRadial_radialHeightField hhw,
    Radial.radialPartial_radialHeightField hw, radialPartial_profileEnergy hw,
    Radial.polarDiscriminant_radialHeightField hhw]
  simp only [linearAngular, profileEnergy, radialEnergy,
    Radial.radialHeightField, inverseDThreeHalves_one, mul_one]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_originalAngularCoefficient_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).c p = deriv (stateProfile D S C x) p.1 / p.1 := by
  have hw := contDiff_stateProfile_of_n01 hS hT h01 x
  change polarCorrectedC (stateProfile D S C x) (stateHeight D S C (x, 0)) p = _
  rw [n07a_stateHeight_zero]
  exact n07a_polarCorrectedC_radialHeightField
    (n07a_stateRadialHeight_hasDerivAt hS hT h01 x) (hw.differentiable (by simp) p.1)

theorem n07a_originalCoefficients_reference
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (p : PolarPoint) :
    (originalCoefficients D S C (C.referenceState, 0)).a p = D.w p.1 ∧
      (originalCoefficients D S C (C.referenceState, 0)).b p = 0 ∧
      (originalCoefficients D S C (C.referenceState, 0)).c p = deriv D.w p.1 / p.1 := by
  rw [n07a_originalLeadingCoefficient_zero hS hT h01,
    n07a_originalMixedCoefficient_zero hS hT h01,
    n07a_originalAngularCoefficient_zero hS hT h01,
    n07a_stateProfile_reference h01.2.2.1]
  exact ⟨rfl, rfl, rfl⟩

theorem n07a_reference_mem_stateNeighborhood
    (h01 : N01Properties D T S C base loss ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  change stateGrading S base (C.referenceState - C.referenceState) < ε ∧ |(0 : ℝ)| < ε
  have hzero : stateGrading S base (0 : AnnularState S) = 0 := (stateGrading S base).map_zero'
  rw [sub_self, hzero, abs_zero]
  exact ⟨h01.2.1, h01.2.1⟩

private theorem n07a_sqrt_radial_speed {r w d : ℝ} (hr : r ≠ 0) (hw : 0 < w) :
    Real.sqrt (-(w * (d / r))) / w = Real.sqrt (-d / (r * w)) := by
  have he : -d / (r * w) = (-(w * (d / r))) / w ^ 2 := by
    field_simp [hr, hw.ne']
  rw [he, Real.sqrt_div' _ (sq_nonneg w), Real.sqrt_sq hw.le]

theorem n07a_minusCharacteristicSpeed_reference
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (θ : ℝ) :
    minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0)) (r, θ) =
      -Real.sqrt (-deriv D.w r / (r * D.w r)) := by
  have hgeom := h01.1.1.choose_spec.1
  have hcoef := n07a_originalCoefficients_reference hS hT h01 (r, θ)
  simp only [minusCharacteristicSpeed, hcoef.1, hcoef.2.1, hcoef.2.2,
    zero_div, zero_pow (by decide : 2 ≠ 0), zero_sub]
  rw [n07a_sqrt_radial_speed (hgeom.1.trans hr.1).ne'
    (hgeom.2.2.2.2.1 r hr)]

theorem n07a_referenceFlow_eq_integral
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (C.referenceState, 0) m r θ =
      θ - ∫ t in C.left m..r, Real.sqrt (-deriv D.w t / (t * D.w t)) := by
  have hgeom := h01.1.1.choose_spec.1
  have hcontrol := h01.2.2.2.1
  have hcell := hcontrol.1 m
  have hcore {t : ℝ} (ht : t ∈ Icc (C.left m) (C.right m)) : t ∈ Ioo D.a D.b :=
    ⟨hcell.1.trans_le ht.1, ht.2.trans_lt hcell.2.2⟩
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hdw : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hspeed : ContinuousOn
      (fun t => Real.sqrt (-deriv D.w t / (t * D.w t)))
      (Icc (C.left m) (C.right m)) :=
    (hdw.neg.continuousOn.div (continuousOn_id.mul hw.continuous.continuousOn)
      (fun t ht => mul_ne_zero (hgeom.1.trans (hcore ht).1).ne'
        (hgeom.2.2.2.2.1 t (hcore ht)).ne')).sqrt
  have hsub : Icc (C.left m) r ⊆ Icc (C.left m) (C.right m) :=
    fun t ht => ⟨ht.1, ht.2.trans hr.2⟩
  have hflow := h01.2.2.2.2.2.2.1 (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) m θ
  have hder (t : ℝ) (ht : t ∈ Ioo (C.left m) r) :
      HasDerivAt (fun s => C.minusFlow (C.referenceState, 0) m s θ)
        (-Real.sqrt (-deriv D.w t / (t * D.w t))) t := by
    have htcell : t ∈ Ioo (C.left m) (C.right m) := ⟨ht.1, ht.2.trans_le hr.2⟩
    simpa only [n07a_minusCharacteristicSpeed_reference hS hT h01
      (hcore (Ioo_subset_Icc_self htcell))] using hflow.2.2.1 t htcell
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
    (hflow.2.1.mono hsub) hder
    ((hspeed.mono hsub).neg.intervalIntegrable_of_Icc hr.1)
  rw [intervalIntegral.integral_neg, hflow.1] at hftc
  linarith only [hftc]

theorem n07a_referenceFlow_return
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ) :
    C.minusFlow (C.referenceState, 0) m (C.right m) θ = θ - C.travel m := by
  have hc := h01.2.2.2.1
  rw [n07a_referenceFlow_eq_integral hS hT h01 m θ ⟨(hc.1 m).2.1.le, le_rfl⟩,
    hc.2.2.2.2.2.2.2.1 m]

theorem n07a_referenceReturnInverse
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε) (m : ℕ) (θ : ℝ) :
    C.minusReturnInverse (C.referenceState, 0) m θ = θ + C.travel m := by
  have hi := (h02.1 (C.referenceState, 0) (n07a_reference_mem_stateNeighborhood h01)
    h01.2.2.1.stateSector m θ).1
  rw [n07a_referenceFlow_return hS hT h01] at hi
  linarith only [hi]

theorem n07a_referenceLeftChart
    (href : referenceStateConditions D S C) (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m θ = θ := by
  simp only [stateLeftChart, href.2.2.2.2.1, map_zero, Pi.zero_apply, add_zero]

theorem n07a_referenceReturnResidualField
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε) (m : ℕ) (θ : ℝ) :
    returnResidualField S C (C.referenceState, 0) m θ = 0 := by
  simp only [returnResidualField, evenPart, n07a_referenceLeftChart h01.2.2.1,
    n07a_referenceReturnInverse hS hT h01 h02, add_sub_cancel_right,
    add_neg_cancel, zero_div]

theorem n07a_referenceReturnResidual_eq_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε) :
    R.residual (C.referenceState, 0) = 0 := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  rw [h02.2.1 (C.referenceState, 0) (n07a_reference_mem_stateNeighborhood h01)
    h01.2.2.1.stateSector m θ, n07a_referenceReturnResidualField hS hT h01 h02]
  simp only [map_zero, Pi.zero_apply]

end ContinuousFlexibility.Analysis
