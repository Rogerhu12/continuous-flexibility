import ContinuousFlexibility.Analysis.N07aProfileNu
import ContinuousFlexibility.Analysis.N07aNuSupport
import ContinuousFlexibility.Analysis.SpacesCompactHeights

/-!
# The actual border column in the existing scalar state model

On the fixed border support the optical controls vanish on a neighborhood.
Off that support both residuals are independent of the border parameter.
Thus the genuine distinguished column is the derivative of the existing
weighted scalar residual with its literal compact border-profile input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n07aNuScalarState
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D) (z : AnnularState S × ℝ) : ScalarWeightedState S :=
  (((n07aNuProfileHeight hT hS hborder scalarBeta z.1.2.1, z.1.1.1), z.1.1.2), z.2)

theorem n07aNuScalarState_profile
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D) (z : AnnularState S × ℝ) :
    scalarStateProfile D S (n07aNuScalarState hT hS hborder z) =
      fun r => D.w r * Real.exp (z.1.2.1 * D.chi r) := by
  funext r
  simp only [scalarStateProfile, n07aNuScalarState, n07aNuProfileHeight_decode,
    spaces_angularMean_const, n07aNuProfileMean]
  ring

theorem n07aNuScalarState_increment
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D) (z : AnnularState S × ℝ) :
    scalarStateIncrement S (n07aNuScalarState hT hS hborder z) = stateU S z.1 := rfl

theorem n07aNuScalarState_residual_eq_on_border
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p.1 ∈ tsupport D.chi) :
    scalarResidualField D S C z p =
      scalarStateResidual D S (n07aNuScalarState hT hS h01.1.2.2.2.1 z) p := by
  let y := n07aNuScalarState hT hS h01.1.2.2.2.1 z
  have hw := contDiff_stateProfile_of_n01 hS hT h01 z.1
  have hyw := scalarStateProfile_contDiff h01.1.1 hT hS y
  have he : stateProfile D S C z.1 =ᶠ[𝓝 p.1] scalarStateProfile D S y := by
    rw [show scalarStateProfile D S y = fun r => D.w r * Real.exp (z.1.2.1 * D.chi r)
      from n07aNuScalarState_profile hT hS h01.1.2.2.2.1 z]
    exact n07a_stateProfile_eq_nuProfile_germ h01.1.1.choose_spec.1.2.2.1.1
      h01.2.2.2.1 z.1 ((h01.1.2.2.2.1.2.2.1 hp).2)
  exact n07a_normalizedResidual_radialProfile_congr
    (stateRadialHeight_contDiff_of_contDiff hw)
    (scalarStatePrimitive_contDiff h01.1.1 hT hS y)
    (stateRadialHeight_hasDerivAt_of_contDiff hw)
    (scalarStatePrimitive_hasDerivAt h01.1.1 hT hS y)
    (hw.differentiable (by simp) p.1) (hyw.differentiable (by simp) p.1)
    (neighborhood_stateU_contDiff hT hS z.1) he.eq_of_nhds he.deriv_eq z.2

theorem n07aNuScalarState_residual_nu_eq_outside
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (ν : ℝ) {p : PolarPoint}
    (hp : p.1 ∉ tsupport D.chi) :
    scalarStateResidual D S
        (n07aNuScalarState hT hS h01.1.2.2.2.1 ((z.1.1, (ν, z.1.2.2)), z.2)) p =
      scalarStateResidual D S (n07aNuScalarState hT hS h01.1.2.2.2.1 z) p := by
  let y := n07aNuScalarState hT hS h01.1.2.2.2.1 ((z.1.1, (ν, z.1.2.2)), z.2)
  let y' := n07aNuScalarState hT hS h01.1.2.2.2.1 z
  have hw := scalarStateProfile_contDiff h01.1.1 hT hS y
  have hw' := scalarStateProfile_contDiff h01.1.1 hT hS y'
  have he : scalarStateProfile D S y =ᶠ[𝓝 p.1] scalarStateProfile D S y' := by
    have hχ : D.chi =ᶠ[𝓝 p.1] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    filter_upwards [hχ] with r hr
    simp only [Pi.zero_apply] at hr
    have hν : scalarStateProfile D S y r = D.w r * Real.exp (ν * D.chi r) :=
      congrFun (n07aNuScalarState_profile hT hS h01.1.2.2.2.1
        ((z.1.1, (ν, z.1.2.2)), z.2)) r
    have hν₀ : scalarStateProfile D S y' r = D.w r * Real.exp (z.1.2.1 * D.chi r) :=
      congrFun (n07aNuScalarState_profile hT hS h01.1.2.2.2.1 z) r
    exact hν.trans ((by rw [hr]; simp only [mul_zero] :
      D.w r * Real.exp (ν * D.chi r) = D.w r * Real.exp (z.1.2.1 * D.chi r)).trans hν₀.symm)
  exact n07a_normalizedResidual_radialProfile_congr
    (scalarStatePrimitive_contDiff h01.1.1 hT hS y)
    (scalarStatePrimitive_contDiff h01.1.1 hT hS y')
    (scalarStatePrimitive_hasDerivAt h01.1.1 hT hS y)
    (scalarStatePrimitive_hasDerivAt h01.1.1 hT hS y')
    (hw.differentiable (by simp) p.1) (hw'.differentiable (by simp) p.1)
    (neighborhood_stateU_contDiff hT hS z.1) he.eq_of_nhds he.deriv_eq z.2

theorem n07a_nuColumnField_eq_pureResidual_deriv
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    nuColumnField D S C z p =
      deriv (fun ν => scalarStateResidual D S
        (n07aNuScalarState hT hS h01.1.2.2.2.1 ((z.1.1, (ν, z.1.2.2)), z.2)) p)
        z.1.2.1 := by
  by_cases hp : p.1 ∈ tsupport D.chi
  · have he : (fun ν => scalarResidualField D S C ((z.1.1, (ν, z.1.2.2)), z.2) p) =
        fun ν => scalarStateResidual D S
          (n07aNuScalarState hT hS h01.1.2.2.2.1 ((z.1.1, (ν, z.1.2.2)), z.2)) p :=
      funext fun ν => n07aNuScalarState_residual_eq_on_border hS hT h01 _ hp
    exact congrArg (fun f : ℝ → ℝ => deriv f z.1.2.1) he
  · have hzero : nuColumnField D S C z p = 0 :=
      n07a_nuColumnField_eq_zero_outside hS hT h01 z hp
    have he : (fun ν => scalarStateResidual D S
        (n07aNuScalarState hT hS h01.1.2.2.2.1 ((z.1.1, (ν, z.1.2.2)), z.2)) p) =
        fun _ : ℝ => scalarStateResidual D S
          (n07aNuScalarState hT hS h01.1.2.2.2.1 z) p :=
      funext fun ν => n07aNuScalarState_residual_nu_eq_outside hS hT h01 z ν hp
    have hder : deriv (fun ν => scalarStateResidual D S
        (n07aNuScalarState hT hS h01.1.2.2.2.1 ((z.1.1, (ν, z.1.2.2)), z.2)) p)
        z.1.2.1 = 0 :=
      (congrArg (fun f : ℝ → ℝ => deriv f z.1.2.1) he).trans
        (deriv_const z.1.2.1 (scalarStateResidual D S
          (n07aNuScalarState hT hS h01.1.2.2.2.1 z) p))
    exact hzero.trans hder.symm

end ContinuousFlexibility.Analysis
