module

public import ContinuousFlexibility.Analysis.AngularRegularityIntegral
public import ContinuousFlexibility.Analysis.N01ReturnChartSmoothness
public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity

/-!
# Smoothness of the actual frozen displacement

The removable divided difference is written as the integral of the
derivative along its actual segment. Smoothness in the scalar chart
variable follows by repeated angular differentiation under the integral,
using the existing angular-regularity calculus. This also covers zero
residual, without dividing by the residual.

All maps in the final results are computed from the original N01 charts
and the existing decoded circle argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n02n03_angularRegular_of_contDiff {H : PolarPoint → ℝ}
    (hH : ContDiff ℝ ∞ H) (n : ℕ) :
    AngularRegular n (fun r θ => H (r, θ)) := by
  induction n generalizing H with
  | zero => exact hH.continuous
  | succ n ih =>
    have hA : ContDiff ℝ ∞ (angularPartial H) :=
      contDiff_iff_contDiffAt.mpr fun p =>
        contDiffAt_angularPartial (hH.contDiffAt (x := p)) (m := ∞) (by simp)
    have hd (r θ : ℝ) := hasDerivAt_angular_slice (hH.differentiable (by simp) (r, θ))
    refine ⟨hH.continuous, fun r θ => (hd r θ).differentiableAt, ?_⟩
    exact (ih hA).congr fun r θ => (hd r θ).deriv

theorem smooth_scalar_parameter_intervalIntegral {H : PolarPoint → ℝ}
    (hH : ContDiff ℝ ∞ H) (a b : ℝ) :
    ContDiff ℝ ∞ (fun θ => ∫ t in a..b, H (t, θ)) := by
  apply contDiff_infty.mpr
  intro n
  exact ((n02n03_angularRegular_of_contDiff hH n).radial_primitive a).contDiff b

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem returnCorrection_dslope_comp_contDiff
    {G x d : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hx : ContDiff ℝ ∞ x) (hd : ContDiff ℝ ∞ d) :
    ContDiff ℝ ∞ (fun θ => dslope G (x θ) (x θ + d θ)) := by
  let H : PolarPoint → ℝ := fun p => deriv G (x p.2 + p.1 * d p.2)
  have hDG : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.mp hG).2
  have hH : ContDiff ℝ ∞ H :=
    hDG.comp ((hx.comp contDiff_snd).add (contDiff_fst.mul (hd.comp contDiff_snd)))
  have hi := smooth_scalar_parameter_intervalIntegral hH 0 1
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact hi.contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun t =>
      returnCorrection_dslope_integral (hG.of_le (by simp)) (x t) (d t))

section ActualDisplacement

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (m : ℕ)

include hN01 hS hT hz hsector

theorem N01Properties.returnCorrectionDisplacementLinear_contDiff
    (ρ : CircleSpace S) :
    ContDiff ℝ ∞ (fun θ => returnCorrectionDisplacementLinear S C z m θ ρ) := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  let y : ℝ → ℝ := fun θ =>
    rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
  let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  let e : ℝ → ℝ := fun θ => returnResidualField S C z m (y θ)
  have hy : ContDiff ℝ ∞ y :=
    (hN01.rightChartCandidate_contDiff hS hT hz hsector m).comp
      (hN01.minusFlow_angular_contDiff hS hT hz hsector m
        ⟨(hC.1 m).2.1.le, le_rfl⟩)
  have hG : ContDiff ℝ ∞ G :=
    hN01.returnTransportInverse_contDiff hS hT hz hsector m
  have he : ContDiff ℝ ∞ e :=
    (hN01.returnResidualField_contDiff hS hT hz hsector m).comp hy
  have hquot := returnCorrection_dslope_comp_contDiff hG hy he
  have hρ := (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 ρ).1 m).1
  have h := hquot.mul (hρ.comp hy)
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact h.contDiffAt.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simp only [returnCorrectionDisplacementLinear_apply, y, G, e,
      Pi.mul_apply, Function.comp_def])

theorem N01Properties.returnCorrectionInitialMap_contDiff :
    ContDiff ℝ ∞ (returnCorrectionInitialMap S C z m) := by
  have hL := stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hG := hN01.returnTransportInverse_contDiff hS hT hz hsector m
  have h : ContDiff ℝ ∞ (fun θ => C.minusReturnInverse z m
      (C.rightChartInverse z m (stateLeftChart S z.1 m θ - C.travel m))) :=
    hG.comp (hL.sub (contDiff_const (c := C.travel m)))
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact h.contDiffAt.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simp only [returnCorrectionInitialMap_apply, Function.comp_def, Pi.sub_apply])

omit hS hT in
theorem N01Properties.returnCorrectionInitialMap_deriv_pos (θ : ℝ) :
    0 < deriv (returnCorrectionInitialMap S C z m) θ := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hleft := hN01.2.2.2.2.2.2.2.1 z hz hsector m
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  have hfpos (t : ℝ) : 0 < deriv (C.minusFlow z m (C.right m)) t :=
    ((hflow z hz m t).2.2.2 (C.right m) ⟨(hC.1 m).2.1.le, le_rfl⟩).1
  have hhpos (t : ℝ) : 0 < deriv (rightChartCandidate S C z m) t := (hI t).2.2.2.2
  have hLpos (t : ℝ) : 0 < deriv (stateLeftChart S z.1 m) t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft t).1
  let t := stateLeftChart S z.1 m θ - C.travel m
  let u := C.rightChartInverse z m t
  have hL := (differentiableAt_of_deriv_ne_zero (hLpos θ).ne').hasDerivAt.sub_const (C.travel m)
  have hh := returnChart_hasDerivAt_inverse (rightChartCandidate S C z m)
    (C.rightChartInverse z m) hhpos (fun x => (hI x).2.2.2.1)
      (fun x => (hI x).2.2.1) t
  have hf := returnChart_hasDerivAt_inverse (C.minusFlow z m (C.right m))
    (C.minusReturnInverse z m) hfpos (fun x => (hI x).2.1) (fun x => (hI x).1) u
  have h := (hf.comp θ (hh.comp θ hL)).congr_of_eventuallyEq
    (f₁ := returnCorrectionInitialMap S C z m)
    (Eventually.of_forall fun x => by
      simp only [returnCorrectionInitialMap_apply, Function.comp_def])
  rw [h.deriv]
  exact mul_pos (inv_pos.mpr (hfpos _))
    (mul_pos (inv_pos.mpr (hhpos _)) (hLpos θ))

theorem N01Properties.returnInterpolation_joint_contDiff
    (χ : ℕ → ℝ → ℝ) (hχ : ContDiff ℝ ∞ (χ m)) :
    ContDiff ℝ ∞ (fun p : PolarPoint =>
      returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m) p.2) := by
  have hK := hN01.returnCorrectionInitialMap_contDiff hS hT hz hsector m
  have h := contDiff_snd.add
    ((hχ.comp contDiff_fst).mul ((hK.comp contDiff_snd).sub contDiff_snd))
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact h.contDiffAt.congr_of_eventuallyEq (Eventually.of_forall fun q => by
    simp only [returnInterpolation_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
      Function.comp_def])

end ActualDisplacement

end ContinuousFlexibility.Statements
