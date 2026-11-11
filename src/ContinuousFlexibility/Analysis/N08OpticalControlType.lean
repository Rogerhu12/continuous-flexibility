import ContinuousFlexibility.Analysis.N08OpticalSquareRoot
import ContinuousFlexibility.Analysis.N08CircleReferenceDiagonal
import ContinuousFlexibility.Analysis.N08StateLinearOperations

/-!
# Relative control of the actual optical radicand

The radial derivative of the genuine zero-parameter flow is its optical
speed. The N01 directional tower makes this derivative differentiable along
every allowed weighted control line. An affine radicand cannot cross zero
inside such a line, so its control coefficient is bounded relative to the
reference radicand. No placement of the control interval in `C.cell m` is
used, and preservation of the negative type is proved rather than assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n08_affine_seminorm_lt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x v : E) {ε t : ℝ}
    (ht : |t| < ε / (1 + p v)) : p (x + t • v - x) < ε := by
  have hp : 0 < 1 + p v := by
    have := apply_nonneg p v
    linarith
  have hh := (lt_div_iff₀ hp).mp ht
  rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (by linarith : p v ≤ 1 + p v)
    (abs_nonneg t)).trans_lt hh

private theorem n08_zero_parameter_line
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x v : E) (t : ℝ) :
    (x, (0 : ℝ)) + t • (v, (0 : ℝ)) = (x + t • v, (0 : ℝ)) := by
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The spatial first derivative is computed from the actual ordinary ODE,
not from a postulated variational equation. -/
theorem n08_ordinaryFlow_radial_jet_zero_parameter
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (r θ : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m 1 0 (r, θ) (x, 0) =
      -opticalSpeed (stateProfile D S C x) r + opticalSpeed D.w r := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hdata := hN
  obtain ⟨hD, hε, href, hC, _, _, hflow, _⟩ := hdata
  obtain ⟨bounds, hbounds⟩ := hD.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hcore : r ∈ radialCore D :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hzero : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · simpa only [stateNeighborhood, sub_self, map_zero] using hε
    · simpa only [abs_zero] using hε
  have hxder := ((hflow (x, 0) hx m θ).2.2.1 r hr).congr_deriv
    (n08_minusCharacteristicSpeed_zero_parameter hg x hw r _ hcore)
  have hzeroder := ((hflow (C.referenceState, 0) hzero m θ).2.2.1 r hr).congr_deriv
    (n08_minusCharacteristicSpeed_reference hg href r _ hcore)
  have hd := (hxder.sub hzeroder).deriv
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_one,
    iteratedDeriv_zero, sub_neg_eq_add] using hd

/-- A public affine-radicand identity for the actual logarithmic control. -/
theorem n08_opticalSpeed_logPerturbation {w χ : ℝ → ℝ} {t r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    opticalSpeed (opticalLogPerturbation w χ t) r =
      Real.sqrt (-deriv w r / (r * w r) + t * (-deriv χ r / r)) := by
  have hp := (hw.hasDerivAt.mul ((hχ.hasDerivAt.const_mul t).exp)).deriv
  change deriv (fun s => w s * Real.exp (t * χ s)) r = _ at hp
  unfold opticalSpeed
  change Real.sqrt (-deriv (fun s => w s * Real.exp (t * χ s)) r /
    (r * (w r * Real.exp (t * χ r)))) = _
  rw [hp]
  congr 1
  field_simp [hr, hwr, (Real.exp_pos (t * χ r)).ne']
  ring

/-- The same weighted control basis used by the circle diagonal has an
actual relative radicand bound on its own negative component. -/
theorem n08_controlBasis_radical_relative_bound
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    (ε / (1 + stateGrading S base (0, 0, n08ControlBasis hS m, 0))) *
        |T.H (T.sample m) ^ (3 / 4 : ℝ) * (-deriv (C.control m) r / r)| ≤
      -deriv D.w r / (r * D.w r) := by
  let v : AnnularState S := (0, 0, n08ControlBasis hS m, 0)
  let A : ℝ := -deriv D.w r / (r * D.w r)
  let B : ℝ := T.H (T.sample m) ^ (3 / 4 : ℝ) * (-deriv (C.control m) r / r)
  let radius : ℝ := ε / (1 + stateGrading S base v)
  let f := ordinaryFlowFamily S C m 1 0 (r, (0 : ℝ))
  have href := hN.2.2.1
  have hC := hN.2.2.2.1
  obtain ⟨bounds, hbounds⟩ := hN.1.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hcore : r ∈ radialCore D :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hrpos : 0 < r := hg.1.trans hcore.1
  have hwpos : 0 < D.w r := hg.2.2.2.2.1 r hcore
  have hA : 0 < A :=
    div_pos (neg_pos.mpr (hC.2.2.2.1 m r hr)) (mul_pos hrpos hwpos)
  have hp : 0 < 1 + stateGrading S base v := by
    have := apply_nonneg (stateGrading S base) v
    linarith
  have hrad : 0 < radius := div_pos hN.2.1 hp
  have hmem (t : ℝ) (ht : |t| < radius) :
      (C.referenceState + n08StateSMul S t v, 0) ∈
        stateNeighborhood S C base ε :=
    ⟨n08_affine_seminorm_lt (stateGrading S base) C.referenceState v ht,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hN.2.1⟩
  have hpair (t : ℝ) :
      (C.referenceState, 0) + n08StateParameterSMul S t (v, 0) =
        (C.referenceState + n08StateSMul S t v, 0) :=
    n08_zero_parameter_line C.referenceState v t
  have hflowjets : ∃ J : SmoothDirections (stateNeighborhood S C base ε) f, True := by
    have hdata := hN
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩ := hdata
    obtain ⟨K, _, hK⟩ := hflow 1 1
    obtain ⟨J, _⟩ := hK m 1 0 (r, (0 : ℝ)) (by omega) hr
    exact ⟨J, trivial⟩
  obtain ⟨J, _⟩ := hflowjets
  apply n08_sqrtAffine_bound_of_lineDerivatives f (C.referenceState, 0) (v, 0)
    (A := A) (B := B) (K := opticalSpeed D.w r) (R := radius) hA hrad
  · intro t ht
    have hm : (C.referenceState, 0) + n08StateParameterSMul S t (v, 0) ∈
        stateNeighborhood S C base ε := (hpair t).symm ▸ hmem t ht
    exact ⟨_, J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hm (v, 0)⟩
  · intro t ht
    have hf := n08_ordinaryFlow_radial_jet_zero_parameter hS hT hN
      (C.referenceState + n08StateSMul S t v) (hmem t ht) m r 0 hr
    rw [n08_controlBasis_reference_profile hS href hC m t,
      n08_opticalSpeed_logPerturbation
        (hg.2.2.1.1.differentiable (by simp) r)
        ((hC.2.2.2.2.2.1 m).1.differentiable (by simp) r) hrpos.ne' hwpos.ne'] at hf
    exact (congrArg f (hpair t)).trans
      (by simpa only [A, B, mul_assoc, sub_eq_add_neg, add_comm] using hf)

end ContinuousFlexibility.Statements
