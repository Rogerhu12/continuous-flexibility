import ContinuousFlexibility.Analysis.N08CharacteristicFactors
import ContinuousFlexibility.Analysis.N08RadialFlow

/-!
# The actual height variation of the characteristic speed at a radial height

The radial square root is fixed while the height varies.  The discriminant
and `Q` have positive values at parameter zero, so their genuine ordinary
derivatives give the speed variation without a parameter variational ODE.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem n08_minusCharacteristicSpeed_eq_jacobi
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    minusCharacteristicSpeed (originalCoefficients D S C z) p =
      n08JacobiMinusSpeed (stateProfile D S C z.1) (stateHeight D S C z) p := rfl

theorem n08CharacteristicDrift_eq {w : ℝ → ℝ} {h : PolarPoint → ℝ} {p : PolarPoint}
    (hD : 0 < polarDiscriminant w h p)
    (hQ : heightQ (profileEnergy w p) (heightRadial h p)
      (angularPartial (heightAngular h) p) ≠ 0) :
    n08CharacteristicDrift w h p =
      -profileEnergy w p * radialPartial (heightAngular h) p /
        heightQ (profileEnergy w p) (heightRadial h p)
          (angularPartial (heightAngular h) p) := by
  have hs : polarScale w h p ≠ 0 := (inverseDThreeHalves_pos _ hD).ne'
  dsimp only [n08CharacteristicDrift, polarLinearA, polarLinearB, linearRadial, linearMixed]
  field_simp [hs, hQ]
  <;> ring

theorem n08JacobiMinusSpeed_eq_quotient {w : ℝ → ℝ} {h : PolarPoint → ℝ}
    {p : PolarPoint} (hw : DifferentiableAt ℝ w p.1) (hr : p.1 ≠ 0)
    (hD : 0 < polarDiscriminant w h p)
    (hQ : 0 < heightQ (profileEnergy w p) (heightRadial h p)
      (angularPartial (heightAngular h) p)) :
    n08JacobiMinusSpeed w h p =
      (-profileEnergy w p * radialPartial (heightAngular h) p -
        Real.sqrt (-w p.1 * deriv w p.1 / p.1) * Real.sqrt (polarDiscriminant w h p)) /
        heightQ (profileEnergy w p) (heightRadial h p)
          (angularPartial (heightAngular h) p) := by
  rw [n08JacobiMinusSpeed_eq_factors hw hr hD hQ, n08CharacteristicDrift_eq hD hQ.ne']
  unfold n08CharacteristicFactor
  ring

theorem n08_radialCharacteristicRoot_eq {w : ℝ → ℝ} {r : ℝ}
    (hw : 0 < w r) (hr : r ≠ 0) :
    Real.sqrt (-w r * deriv w r / r) = w r * opticalSpeed w r := by
  have he : (-w r * deriv w r / r) / (w r) ^ 2 = -deriv w r / (r * w r) := by
    field_simp [hr, hw.ne']
    <;> ring
  have hs : Real.sqrt (-w r * deriv w r / r) / w r = opticalSpeed w r := by
    calc
      _ = Real.sqrt (-w r * deriv w r / r) / Real.sqrt ((w r) ^ 2) := by
        rw [Real.sqrt_sq hw.le]
      _ = Real.sqrt ((-w r * deriv w r / r) / (w r) ^ 2) :=
        (Real.sqrt_div' _ (sq_nonneg _)).symm
      _ = _ := congrArg Real.sqrt he
  exact ((div_eq_iff hw.ne').mp hs).trans (mul_comm _ _)

def n08RadialSpeedVariation (w : ℝ → ℝ) (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (1 + w p.1 ^ 2) / w p.1 *
    (-radialPartial (heightAngular u) p +
      opticalSpeed w p.1 * (heightRadial u p + angularPartial (heightAngular u) p))

theorem n08_hasDerivAt_JacobiMinusSpeed_radial
    {w h : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) (hu : ContDiff ℝ ∞ u)
    (hhw : ∀ r, HasDerivAt h (w r) r) (p : PolarPoint)
    (hwp : 0 < w p.1) (hr : p.1 ≠ 0) :
    HasDerivAt
      (fun q => n08JacobiMinusSpeed w (heightFamily (Radial.radialHeightField h) u q) p)
      (n08RadialSpeedVariation w u p) 0 := by
  let z : PolarPoint → ℝ := Radial.radialHeightField h
  have hz : ContDiff ℝ ∞ z := Radial.contDiff_radialHeightField hh
  let d : ℝ → ℝ := fun q => polarDiscriminant w (heightFamily z u q) p
  let Q : ℝ → ℝ := fun q => heightQ (profileEnergy w p)
    (heightRadial (heightFamily z u q) p) (angularPartial (heightAngular (heightFamily z u q)) p)
  let P : ℝ → ℝ := fun q => radialPartial (heightAngular (heightFamily z u q)) p
  have hang : heightAngular z = fun _ => 0 := Radial.heightAngular_radialHeightField hhw
  have hrad : heightRadial z p = w p.1 := by
    rw [Radial.heightRadial_radialHeightField hhw]
    rfl
  have hd0 : d 0 = 1 := by
    simp only [d, heightFamily_zero, z, Radial.polarDiscriminant_radialHeightField hhw]
  have hQ0 : Q 0 = w p.1 := by
    simp only [Q, heightFamily_zero, hang, angularPartial_const, heightQ, hrad,
      mul_zero, add_zero]
  have hP0 : P 0 = 0 := by
    simp only [P, heightFamily_zero, hang, radialPartial_const]
  have hd : HasDerivAt d (-2 * w p.1 * heightRadial u p) 0 := by
    apply (hasDerivAt_polarDiscriminant_heightFamily w hz hu p).congr_deriv
    simp only [polarDiscriminantVariation, hang, hrad, mul_zero, zero_mul, zero_sub]
    ring
  have hQ : HasDerivAt Q
      (heightRadial u p + profileEnergy w p * angularPartial (heightAngular u) p) 0 :=
    (hasDerivAt_heightRadial_heightFamily hz hu p 0).add
      ((hasDerivAt_angularPartial_heightAngular_heightFamily hz hu hr 0).const_mul
        (profileEnergy w p))
  have hP : HasDerivAt P (radialPartial (heightAngular u) p) 0 :=
    hasDerivAt_radialPartial_heightAngular_heightFamily hz hu hr 0
  have hds : HasDerivAt (fun q => Real.sqrt (d q))
      ((-2 * w p.1 * heightRadial u p) / (2 * Real.sqrt (d 0))) 0 :=
    hd.sqrt (by rw [hd0]; exact one_ne_zero)
  have hder := ((hP.const_mul (-profileEnergy w p)).sub
    (hds.const_mul (Real.sqrt (-w p.1 * deriv w p.1 / p.1)))).div hQ
      (by rw [hQ0]; exact hwp.ne')
  have hformula : HasDerivAt
      (fun q => (-profileEnergy w p * P q -
        Real.sqrt (-w p.1 * deriv w p.1 / p.1) * Real.sqrt (d q)) / Q q)
      (n08RadialSpeedVariation w u p) 0 := by
    apply hder.congr_deriv
    simp only [Pi.sub_apply, hd0, hQ0, hP0, Real.sqrt_one, mul_one, mul_zero,
      zero_sub, n08RadialSpeedVariation]
    rw [n08_radialCharacteristicRoot_eq hwp hr]
    dsimp only [profileEnergy, radialEnergy]
    field_simp [hwp.ne']
    <;> ring
  apply hformula.congr_of_eventuallyEq
  have hdpos : ∀ᶠ q in 𝓝 (0 : ℝ), 0 < d q :=
    hd.continuousAt.eventually (Ioi_mem_nhds (by rw [hd0]; exact zero_lt_one))
  have hQpos : ∀ᶠ q in 𝓝 (0 : ℝ), 0 < Q q :=
    hQ.continuousAt.eventually (Ioi_mem_nhds (by rw [hQ0]; exact hwp))
  filter_upwards [hdpos, hQpos] with q hdq hQq
  exact n08JacobiMinusSpeed_eq_quotient (hw.differentiable (by simp) p.1) hr hdq hQq

theorem n08RadialSpeedVariation_heightFamily
    (w : ℝ → ℝ) {u η : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hη : ContDiff ℝ ∞ η) {p : PolarPoint}
    (hr : p.1 ≠ 0) (t : ℝ) :
    n08RadialSpeedVariation w (heightFamily u η t) p =
      n08RadialSpeedVariation w u p + t * n08RadialSpeedVariation w η p := by
  simp only [n08RadialSpeedVariation,
    heightRadial_heightFamily (hu.differentiable (by simp)) (hη.differentiable (by simp)),
    radialPartial_heightAngular_heightFamily hu hη hr,
    angularPartial_heightAngular_heightFamily hu hη hr, heightFamily]
  ring

theorem n08RadialSpeedVariation_radial
    (w : ℝ → ℝ) {h g : ℝ → ℝ} (hhg : ∀ r, HasDerivAt h (g r) r) (p : PolarPoint) :
    n08RadialSpeedVariation w (Radial.radialHeightField h) p =
      opticalSpeed w p.1 * (1 + w p.1 ^ 2) / w p.1 * g p.1 := by
  simp only [n08RadialSpeedVariation, Radial.heightAngular_radialHeightField hhg,
    Radial.heightRadial_radialHeightField hhg, radialPartial_const, angularPartial_const,
    neg_zero, zero_add, add_zero, Radial.radialHeightField]
  ring

theorem n08_minusCharacteristicSpeed_parameter_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S)
    (p : PolarPoint) (hp : p.1 ∈ radialCore D) :
    HasDerivAt (fun q => minusCharacteristicSpeed (originalCoefficients D S C (x, q)) p)
      (n08RadialSpeedVariation (stateProfile D S C x) (stateU S x) p) 0 := by
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  exact n08_hasDerivAt_JacobiMinusSpeed_radial
    (contDiff_stateProfile_of_n01 hS hT hN x) (n08_stateRadialHeight_contDiff hT hS hN x)
    (n08_stateU_contDiff hT hS x) (n08_stateRadialHeight_hasDerivAt hT hS hN x)
    p (n08_stateProfile_pos hg x hp) (hg.1.trans hp.1).ne'

end ContinuousFlexibility.Statements
