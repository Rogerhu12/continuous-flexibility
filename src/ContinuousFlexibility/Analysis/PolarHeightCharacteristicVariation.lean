import ContinuousFlexibility.Analysis.N01FlowChartIndependence
import ContinuousFlexibility.Analysis.OpticalTravelVariation

/-!
# Actual height variation of the minus characteristic speed

At a radial height the first height variation of the speed is an
explicit linear expression in the genuine spatial derivatives of the
height direction.  A direction with radial derivative equal to the
profile has response E times the optical speed; the metric profile is
held fixed during this variation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def polarMinusSpeed (w : ℝ → ℝ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  polarLinearB w f p / polarLinearA w f p -
    Real.sqrt (polarLinearB w f p ^ 2 - polarLinearA w f p * polarCorrectedC w f p) /
      polarLinearA w f p

theorem polarMinusSpeed_eq_jet_expression
    {w : ℝ → ℝ} {f : PolarPoint → ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) (hr : p.1 ≠ 0)
    (hD : 0 < polarDiscriminant w f p)
    (hQ : heightQ (profileEnergy w p) (heightRadial f p)
      (angularPartial (heightAngular f) p) ≠ 0) :
    polarMinusSpeed w f p =
      (-profileEnergy w p * radialPartial (heightAngular f) p -
        Real.sqrt (-(w p.1 * deriv w p.1 / p.1)) * Real.sqrt (polarDiscriminant w f p)) /
          heightQ (profileEnergy w p) (heightRadial f p)
            (angularPartial (heightAngular f) p) := by
  have hdet := polar_corrected_determinant f hw hr hD hQ
  have hdisc :
      polarLinearB w f p ^ 2 - polarLinearA w f p * polarCorrectedC w f p =
        -(w p.1 * deriv w p.1 / p.1) / polarDiscriminant w f p ^ 2 := by
    rw [← neg_sub, hdet, neg_div]
  unfold polarMinusSpeed
  rw [hdisc, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hD.le]
  simp only [polarLinearA, polarLinearB, linearRadial, linearMixed,
    polarScale, inverseDThreeHalves]
  field_simp [hD.ne', (Real.sqrt_pos.mpr hD).ne', hQ]

theorem sqrt_profile_radical_eq_profile_mul_opticalSpeed
    {w : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0) (hw : 0 < w r) :
    Real.sqrt (-(w r * deriv w r / r)) = w r * opticalSpeed w r := by
  have heq : -(w r * deriv w r / r) = (w r) ^ 2 * (-deriv w r / (r * w r)) := by
    field_simp [hr, hw.ne']
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw.le]
  rfl

/-- The actual linear first variation at a radial height. -/
def heightSpeedVariation (w : ℝ → ℝ) (η : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  profileEnergy w p / w p.1 *
    (opticalSpeed w p.1 *
        (heightRadial η p + angularPartial (heightAngular η) p) -
      radialPartial (heightAngular η) p)

theorem hasDerivAt_polarMinusSpeed_heightFamily_radial
    {w h : ℝ → ℝ} {η : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hhw : ∀ r, HasDerivAt h (w r) r) (hη : ContDiff ℝ ∞ η)
    {p : PolarPoint} (hr : p.1 ≠ 0) (hwp : 0 < w p.1) :
    HasDerivAt (fun q : ℝ => polarMinusSpeed w
      (heightFamily (Radial.radialHeightField h) η q) p)
      (heightSpeedVariation w η p) 0 := by
  let F : ℝ → PolarPoint → ℝ := heightFamily (Radial.radialHeightField h) η
  let d : ℝ → ℝ := fun q => polarDiscriminant w (F q) p
  let Q : ℝ → ℝ := fun q =>
    heightQ (profileEnergy w p) (heightRadial (F q) p)
      (angularPartial (heightAngular (F q)) p)
  let P : ℝ → ℝ := fun q => radialPartial (heightAngular (F q)) p
  let E : ℝ := profileEnergy w p
  let K : ℝ := Real.sqrt (-(w p.1 * deriv w p.1 / p.1))
  have hrad := Radial.heightRadial_radialHeightField hhw
  have hang := Radial.heightAngular_radialHeightField hhw
  have hheight := Radial.contDiff_radialHeightField hh
  have hd0 : d 0 = 1 := by
    dsimp only [d, F]
    rw [heightFamily_zero, Radial.polarDiscriminant_radialHeightField hhw]
  have hQ0 : Q 0 = w p.1 := by
    dsimp only [Q, F]
    rw [heightFamily_zero, hrad, hang, angularPartial_const]
    simp only [heightQ, Radial.radialHeightField, mul_zero, add_zero]
  have hP0 : P 0 = 0 := by
    dsimp only [P, F]
    rw [heightFamily_zero, hang, radialPartial_const]
  have hd : HasDerivAt d (-2 * w p.1 * heightRadial η p) 0 := by
    apply (hasDerivAt_polarDiscriminant_heightFamily w hheight hη p).congr_deriv
    simp only [polarDiscriminantVariation, hrad, hang, Radial.radialHeightField,
      mul_zero, zero_mul, zero_sub]
    ring
  have hQ : HasDerivAt Q
      (heightRadial η p + E * angularPartial (heightAngular η) p) 0 := by
    have h := (hasDerivAt_heightRadial_heightFamily hheight hη p 0).add
      ((hasDerivAt_angularPartial_heightAngular_heightFamily hheight hη hr 0).const_mul E)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun q => by
      simp only [Q, F, E, heightQ, Pi.add_apply])
  have hP : HasDerivAt P (radialPartial (heightAngular η) p) 0 :=
    hasDerivAt_radialPartial_heightAngular_heightFamily hheight hη hr 0
  have hdn : d 0 ≠ 0 := by rw [hd0]; norm_num
  have hQn : Q 0 ≠ 0 := by rw [hQ0]; exact hwp.ne'
  have hcalc := ((hP.const_mul (-E)).sub ((hd.sqrt hdn).const_mul K)).div hQ hQn
  have hformula : HasDerivAt (fun q : ℝ => (-E * P q - K * Real.sqrt (d q)) / Q q)
      (heightSpeedVariation w η p) 0 := by
    apply (hcalc.congr_of_eventuallyEq
      (Eventually.of_forall fun q => by
        simp only [Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Function.comp_def])).congr_deriv
    simp only [Pi.sub_apply]
    rw [hd0, hQ0, hP0, Real.sqrt_one]
    dsimp only [K, E, heightSpeedVariation]
    rw [sqrt_profile_radical_eq_profile_mul_opticalSpeed hr hwp]
    simp only [profileEnergy, radialEnergy]
    field_simp [hwp.ne'] <;> ring
  have hdp : ∀ᶠ q in 𝓝 (0 : ℝ), 0 < d q :=
    hd.continuousAt.eventually (Ioi_mem_nhds (by rw [hd0]; norm_num))
  have hQp : ∀ᶠ q in 𝓝 (0 : ℝ), Q q ≠ 0 := hQ.continuousAt.eventually_ne hQn
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hdp, hQp] with q hdq hQq
  exact polarMinusSpeed_eq_jet_expression (hw.differentiable (by simp) p.1) hr hdq hQq

theorem heightSpeedVariation_heightFamily
    {w : ℝ → ℝ} {u η : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hη : ContDiff ℝ ∞ η)
    {p : PolarPoint} (hr : p.1 ≠ 0) (t : ℝ) :
    heightSpeedVariation w (heightFamily u η t) p =
      heightSpeedVariation w u p + t * heightSpeedVariation w η p := by
  unfold heightSpeedVariation
  rw [heightRadial_heightFamily (hu.differentiable (by simp)) (hη.differentiable (by simp)),
    angularPartial_heightAngular_heightFamily hu hη hr,
    radialPartial_heightAngular_heightFamily hu hη hr]
  simp only [heightFamily]
  ring

/-- A local primitive direction detects the full optical travel. -/
theorem heightSpeedVariation_radialHeightField
    {w h : ℝ → ℝ} (hhw : ∀ r, HasDerivAt h (w r) r)
    {p : PolarPoint} (hwp : w p.1 ≠ 0) :
    heightSpeedVariation w (Radial.radialHeightField h) p =
      profileEnergy w p * opticalSpeed w p.1 := by
  unfold heightSpeedVariation
  rw [Radial.heightRadial_radialHeightField hhw,
    Radial.heightAngular_radialHeightField hhw,
    angularPartial_const, radialPartial_const]
  simp only [Radial.radialHeightField, add_zero, sub_zero]
  field_simp [hwp]

/-- Specialization to the actual N01 coefficient family at q = 0. -/
theorem N01Properties.hasDerivAt_minusCharacteristicSpeed_q_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (x : AnnularState S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt (fun q : ℝ => minusCharacteristicSpeed
      (originalCoefficients D S C (x, q)) p)
      (heightSpeedVariation (stateProfile D S C x) (stateU S x) p) 0 := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 x
  have hh := N01Properties.stateRadialHeight_contDiff hN01 hS hT x
  have hhw (r : ℝ) : HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r :=
    intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable D.b r)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt
  have hu : ContDiff ℝ ∞ (stateU S x) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      x.1.1 x.1.2
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr : p.1 ≠ 0 := (hgeom.1.1.trans hp.1.1).ne'
  have hwp : 0 < stateProfile D S C x p.1 :=
    mul_pos (hgeom.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have h := hasDerivAt_polarMinusSpeed_heightFamily_radial hw hh hhw hu hr hwp
  have heq (q : ℝ) : stateHeight D S C (x, q) =
      heightFamily (Radial.radialHeightField (stateRadialHeight D S C x)) (stateU S x) q := by
    funext y
    simp only [stateHeight, heightFamily, Radial.radialHeightField]
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun q => by
    change polarMinusSpeed (stateProfile D S C x) (stateHeight D S C (x, q)) p = _
    rw [heq q])

end ContinuousFlexibility.Statements
