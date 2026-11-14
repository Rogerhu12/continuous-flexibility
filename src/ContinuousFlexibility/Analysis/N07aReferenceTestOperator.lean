module

public import ContinuousFlexibility.Analysis.N07aCompactEvenHeight
public import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-!
# The actual reference operator on compact even tests

The reference return residual is zero. N03 therefore removes its genuine
linear correction on a test lifted through the physical height decoder.
The explicit zero-amplitude coefficients identify the remaining operator
with the radial differential expression used by N05.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n07aReferenceTestStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
local instance n07aReferenceTestStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
local instance n07aReferenceTestStateAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := (inferInstance : AddCommGroup (AnnularState S)).toAddGroup
local instance n07aReferenceTestStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := (inferInstance : Module ℝ (AnnularState S)).toSMul
local instance n07aReferenceTestStateSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := (inferInstance : AddCommGroup (AnnularState S)).toSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_originalReference_divergence
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) φ p =
      Radial.radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2 := by
  have hgeom := h01.1.1.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hdw : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hpr : p.1 ≠ 0 := (hgeom.1.trans hp.1.1).ne'
  have hwp : DifferentiableAt ℝ (fun q : PolarPoint => D.w q.1) p :=
    (hw.comp contDiff_fst).differentiable (by simp) p
  have hdc : DifferentiableAt ℝ (fun q : PolarPoint => deriv D.w q.1) p :=
    (hdw.comp contDiff_fst).differentiable (by simp) p
  have hcp : DifferentiableAt ℝ (fun q : PolarPoint => deriv D.w q.1 / q.1) p :=
    hdc.mul ((differentiableAt_fst : DifferentiableAt ℝ (Prod.fst : PolarPoint → ℝ) p).inv hpr)
  have hφr : DifferentiableAt ℝ (radialPartial φ) p :=
    (contDiffAt_radialPartial hφ.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have hφt : DifferentiableAt ℝ (angularPartial φ) p :=
    (contDiffAt_angularPartial hφ.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have hrw : radialPartial (fun q : PolarPoint => D.w q.1) p = deriv D.w p.1 :=
    (Radial.hasDerivAt_radialSlice hwp).deriv.symm
  have htc : angularPartial (fun q : PolarPoint => deriv D.w q.1 / q.1) p = 0 := by
    have h := (Radial.hasDerivAt_angularSlice hcp).deriv
    simpa only [deriv_const] using h.symm
  have ha : (originalCoefficients D S C (C.referenceState, 0)).a =
      fun q => D.w q.1 := funext fun q => (n07a_originalCoefficients_reference hS hT h01 q).1
  have hb : (originalCoefficients D S C (C.referenceState, 0)).b =
      fun _ => 0 := funext fun q => (n07a_originalCoefficients_reference hS hT h01 q).2.1
  have hc : (originalCoefficients D S C (C.referenceState, 0)).c =
      fun q => deriv D.w q.1 / q.1 :=
    funext fun q => (n07a_originalCoefficients_reference hS hT h01 q).2.2
  simp only [divergenceOperator, ha, hb, hc, zero_mul, zero_add, add_zero]
  rw [radialPartial_mul hwp hφr, angularPartial_mul hcp hφt, hrw, htc,
    zero_mul, zero_add, Radial.radialPDE_eq_polar_jets (hw.differentiable (by simp) p.1) hφ]

/-- This is an actual consequence of N01--N03, applied to the decoded
compact test, rather than an extra reference-operator hypothesis. -/
theorem n07a_reference_divergence_even_test
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (heven : ∀ r θ, φ (r, -θ) = φ (r, θ))
    (hπ : Function.Periodic φ (0, Real.pi))
    (hsupp : HasCompactRadialSupport D φ) :
    EqOn (divergenceOperator (L.coefficients (C.referenceState, 0)) φ)
      (fun p => Radial.radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2)
      (annularOpen D) := by
  let pair := n07a_compact_even_heightPair hS hT hφ heven hπ hsupp
  let η : HeightPair S := pair.choose
  have hη : heightPairField S η = φ := pair.choose_spec
  have hz := n07a_reference_mem_stateNeighborhood h01
  have hs := h01.2.2.1.stateSector
  have hres := n07a_referenceReturnResidual_eq_zero hS hT h01 h02
  intro p hp
  have h := h03.2.2.2.2.2.1 (C.referenceState, 0) hz hs η p hp
  let E : CircleSpace S →ₗ[ℝ] (HeightPair S →ₗ[ℝ] S.Source) := L.error (C.referenceState, 0)
  have hE : E (R.residual (C.referenceState, 0)) = 0 :=
    (congrArg E hres).trans E.map_zero
  have hEη : E (R.residual (C.referenceState, 0)) η = (0 : S.Source) :=
    congrArg (fun A : HeightPair S →ₗ[ℝ] S.Source => A η) hE
  have hdecode := congrArg (fun v : S.Source => (S.height (3 / 4 : ℝ)).decode v.val p) hEη
  have hdz : (S.height (3 / 4 : ℝ)).decode (0 : (S.height (3 / 4 : ℝ)).Space) p = 0 :=
    congrFun (S.height (3 / 4 : ℝ)).decode.map_zero p
  have heq := h.trans (hdecode.trans hdz)
  have hleft := congrArg (fun v : PolarPoint → ℝ =>
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) v p -
      divergenceOperator (L.coefficients (C.referenceState, 0)) v p) hη
  have heqφ := hleft.symm.trans heq
  exact (sub_eq_zero.mp heqφ).symm.trans
    (n07a_originalReference_divergence hS hT h01 hφ hp)

end ContinuousFlexibility.Analysis
