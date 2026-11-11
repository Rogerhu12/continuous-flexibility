import ContinuousFlexibility.Scalar.Connection

/-!
# Genuine flat germs of the height equation

These lemmas concern the actual derivatives of locally constant functions.
They allow a globally smoothly extended analytic core to be enlarged to
honest open flat collars, without identifying flat boundary jets with a
constant germ at the original endpoint itself.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem height_jets_eq_zero_of_constant_germ
    {z : PolarPoint → ℝ} {x : PolarPoint} {c : ℝ}
    (hz : z =ᶠ[𝓝 x] fun _ => c) :
    heightRadial z x = 0 ∧ heightAngular z x = 0 ∧
      radialPartial (heightRadial z) x = 0 ∧
      radialPartial (heightAngular z) x = 0 ∧
      angularPartial (heightAngular z) x = 0 := by
  have hk : heightRadial z =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hz.fderiv (𝕜 := ℝ)] with y hy
    simp [heightRadial, radialPartial, hy]
  have hp : heightAngular z =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hz.fderiv (𝕜 := ℝ)] with y hy
    simp [heightAngular, angularPartial, hy]
  refine ⟨hk.eq_of_nhds, hp.eq_of_nhds, ?_, ?_, ?_⟩
  · simp [radialPartial, hk.fderiv_eq (𝕜 := ℝ)]
  · simp [radialPartial, hp.fderiv_eq (𝕜 := ℝ)]
  · simp [angularPartial, hp.fderiv_eq (𝕜 := ℝ)]

theorem profileEnergy_eq_one_of_zero_germ
    {w : ℝ → ℝ} {x : PolarPoint} (hw : w =ᶠ[𝓝 x.1] fun _ => 0) :
    profileEnergy w =ᶠ[𝓝 x] fun _ => 1 := by
  have hwx := hw.comp_tendsto (continuous_fst.continuousAt : ContinuousAt Prod.fst x)
  filter_upwards [hwx] with y hy
  change w y.1 = 0 at hy
  simp [profileEnergy, radialEnergy, hy]

theorem flat_germ_discriminant_eq_one
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} {c : ℝ}
    (hw : w =ᶠ[𝓝 x.1] fun _ => 0) (hz : z =ᶠ[𝓝 x] fun _ => c) :
    polarDiscriminant w z x = 1 := by
  obtain ⟨hk, hp, _, _, _⟩ := height_jets_eq_zero_of_constant_germ hz
  have hE := (profileEnergy_eq_one_of_zero_germ hw).eq_of_nhds
  simp [polarDiscriminant, heightDiscriminant, hk, hp, hE]

theorem flat_germ_curvatureNumerator_eq_zero
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} {c : ℝ}
    (hw : w =ᶠ[𝓝 x.1] fun _ => 0) (hz : z =ᶠ[𝓝 x] fun _ => c) :
    polarCurvatureNumerator w z x = 0 := by
  obtain ⟨hk, hp, hkr, hpr, hpt⟩ := height_jets_eq_zero_of_constant_germ hz
  have hEr : radialPartial (profileEnergy w) x = 0 := by
    simp [radialPartial, (profileEnergy_eq_one_of_zero_germ hw).fderiv_eq (𝕜 := ℝ)]
  simp [polarCurvatureNumerator, darbouxNumerator, heightQ, hk, hp, hkr, hpr, hpt, hEr]

theorem flat_germ_residual_eq_zero
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} {c : ℝ}
    (hw : w =ᶠ[𝓝 x.1] fun _ => 0) (hz : z =ᶠ[𝓝 x] fun _ => c) :
    polarCoordinateResidual w z x = 0 := by
  simp [polarCoordinateResidual, flat_germ_curvatureNumerator_eq_zero hw hz]

end ContinuousFlexibility
