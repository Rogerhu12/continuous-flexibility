module

public import ContinuousFlexibility.Radial.RadialHeight
public import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
public import ContinuousFlexibility.Analysis.OpticalTravelVariation

/-!
# The actual radial coefficients and ordinary flow at zero residual parameter

The height at `q = 0` is the actual primitive of the controlled profile.
Its polar jets give `a = w`, `b = 0`, and `c = w' / r`.  Consequently
the ordinary flow in N01 is the initial angle minus the actual partial
optical travel.  The last lemmas specialize this identity to an actual
single-kappa path without any assumption on its weighted norm.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Radial

open scoped ContDiff

theorem polarLinearA_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) (p : PolarPoint) :
    polarLinearA w (radialHeightField h) p = w p.1 := by
  unfold polarLinearA polarScale
  rw [heightRadial_radialHeightField hhw, heightAngular_radialHeightField hhw,
    angularPartial_const, polarDiscriminant_radialHeightField hhw,
    inverseDThreeHalves_one]
  simp only [linearRadial, heightQ, radialHeightField, mul_zero, add_zero, mul_one]

theorem polarLinearB_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) (p : PolarPoint) :
    polarLinearB w (radialHeightField h) p = 0 := by
  unfold polarLinearB
  rw [heightAngular_radialHeightField hhw, radialPartial_const]
  simp only [linearMixed, mul_zero, zero_mul]

theorem polarLinearC_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) :
    polarLinearC w (radialHeightField h) p = deriv w p.1 / p.1 := by
  unfold polarLinearC polarScale
  rw [heightRadial_radialHeightField hhw, radialPartial_radialHeightField hw,
    radialPartial_profileEnergy hw, polarDiscriminant_radialHeightField hhw,
    inverseDThreeHalves_one]
  simpa only [profileEnergy, radialHeightField, heightDiscriminant_radial,
    inverseDThreeHalves_one] using
    (radial_linear_coefficients p.1 (w p.1) (deriv w p.1)).2.2

theorem polarCorrectedC_radialHeightField {h w : ℝ → ℝ}
    (hhw : ∀ r, HasDerivAt h (w r) r) {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) :
    polarCorrectedC w (radialHeightField h) p = deriv w p.1 / p.1 := by
  rw [polarCorrectedC_eq_residual_correction,
    polarCoordinateResidual_radialHeightField hhw hw,
    mul_zero, zero_div, sub_zero, polarLinearC_radialHeightField hhw hw]

end ContinuousFlexibility.Radial

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Radial
open scoped Topology ContDiff

theorem stateHeight_zero_radial
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (x : AnnularState S) :
    stateHeight D S C (x, 0) = radialHeightField (stateRadialHeight D S C x) := by
  funext p
  simp only [stateHeight, radialHeightField, zero_mul, add_zero]

/-- These are identities of the actual coefficient functions, obtained
from the derivative of the actual radial primitive. -/
theorem originalCoefficients_radial_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (x : AnnularState S) (hw : ContDiff ℝ ∞ (stateProfile D S C x)) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).a p = stateProfile D S C x p.1 ∧
      (originalCoefficients D S C (x, 0)).b p = 0 ∧
      (originalCoefficients D S C (x, 0)).c p = deriv (stateProfile D S C x) p.1 / p.1 := by
  have hhw (r : ℝ) :
      HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r :=
    intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable D.b r)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt
  change polarLinearA _ (stateHeight D S C (x, 0)) p = _ ∧
    polarLinearB _ (stateHeight D S C (x, 0)) p = _ ∧
    polarCorrectedC _ (stateHeight D S C (x, 0)) p = _
  rw [stateHeight_zero_radial]
  exact ⟨polarLinearA_radialHeightField hhw p,
    polarLinearB_radialHeightField hhw p,
    polarCorrectedC_radialHeightField hhw (hw.differentiable (by simp) p.1)⟩

/-- Positivity of the profile is the only sign needed to identify the
minus speed; the radicand may also vanish at a turning radius. -/
theorem minusCharacteristicSpeed_of_radial_coefficients
    {L : SymmetricCoefficients} {w : ℝ → ℝ} {p : PolarPoint}
    (ha : L.a p = w p.1) (hb : L.b p = 0)
    (hc : L.c p = deriv w p.1 / p.1) (hr : p.1 ≠ 0) (hw : 0 < w p.1) :
    minusCharacteristicSpeed L p = -opticalSpeed w p.1 := by
  have hrad :
      -(w p.1 * (deriv w p.1 / p.1)) / (w p.1) ^ 2 =
        -deriv w p.1 / (p.1 * w p.1) := by
    field_simp [hr, hw.ne']
    <;> ring
  have hsqrt := congrArg Real.sqrt hrad
  rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hw.le] at hsqrt
  simp only [minusCharacteristicSpeed, ha, hb, hc, zero_div, zero_pow (by decide : 2 ≠ 0),
    zero_sub, opticalSpeed]
  exact congrArg Neg.neg hsqrt

theorem continuousOn_opticalSpeed_of_profile
    {w : ℝ → ℝ} {l h : ℝ} (hw : ContDiff ℝ ∞ w) (hl : 0 < l)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) :
    ContinuousOn (opticalSpeed w) (Icc l h) := by
  exact Real.continuous_sqrt.comp_continuousOn
    (((hw.continuous_deriv (by simp)).neg.continuousOn).div
      (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (hl.trans_le hr.1) (hpos r hr)).ne'))

/-- The radial ODE is integrated directly on the closed interval.  This
uses the actual ordinary-flow specification, including its initial value. -/
theorem ordinaryFlow_radial_zero_eq_opticalTravel
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {U : Set (AnnularState S × ℝ)} (hflow : ordinaryFlowConditions D S C U)
    {x : AnnularState S} (hx : (x, 0) ∈ U)
    (hw : ContDiff ℝ ∞ (stateProfile D S C x)) (m : ℕ)
    (hl : 0 < C.left m) (hlh : C.left m < C.right m)
    (hpos : ∀ r ∈ Icc (C.left m) (C.right m), 0 < stateProfile D S C x r)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, 0) m r θ =
      θ - opticalTravel (stateProfile D S C x) (C.left m) r := by
  have hs := continuousOn_opticalSpeed_of_profile hw hl hpos
  have hcoeff (s : ℝ) (hs' : s ∈ Icc (C.left m) (C.right m)) (φ : ℝ) :
      minusCharacteristicSpeed (originalCoefficients D S C (x, 0)) (s, φ) =
        -opticalSpeed (stateProfile D S C x) s := by
    obtain ⟨ha, hb, hc⟩ := originalCoefficients_radial_zero x hw (s, φ)
    exact minusCharacteristicSpeed_of_radial_coefficients ha hb hc
      (hl.trans_le hs'.1).ne' (hpos s hs')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s => C.minusFlow (x, 0) m s θ)
    (f' := fun s => -opticalSpeed (stateProfile D S C x) s) hr.1
    ((hflow (x, 0) hx m θ).2.1.mono (Icc_subset_Icc le_rfl hr.2))
    (fun s hs' => by
      have hsIoo : s ∈ Ioo (C.left m) (C.right m) := ⟨hs'.1, hs'.2.trans_le hr.2⟩
      simpa only [hcoeff s ⟨hsIoo.1.le, hsIoo.2.le⟩] using
        (hflow (x, 0) hx m θ).2.2.1 s hsIoo)
    ((hs.neg.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1)
  rw [intervalIntegral.integral_neg, (hflow (x, 0) hx m θ).1] at hFTC
  change -opticalTravel (stateProfile D S C x) (C.left m) r =
    C.minusFlow (x, 0) m r θ - θ at hFTC
  linarith only [hFTC]

theorem N01Properties.minusFlow_zero_eq_opticalTravel
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, 0) m r θ =
      θ - opticalTravel (stateProfile D S C x) (C.left m) r := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  apply ordinaryFlow_radial_zero_eq_opticalTravel hN.2.2.2.2.2.2.1 hx
    (contDiff_stateProfile_of_n01 hS hT hN x) m
    (hgeom.1.1.trans (hcontrol.1 m).1) (hcontrol.1 m).2.1 ?_ θ hr
  intro s hs
  apply mul_pos
  · exact hgeom.1.2.2.2.2.1 s
      ⟨(hcontrol.1 m).1.trans_le hs.1, hs.2.trans_lt (hcontrol.1 m).2.2⟩
  · exact Real.exp_pos _

/-- A genuine singleton mean sequence produces the exact logarithmic
control profile.  No summability premise is needed for a singleton. -/
theorem stateProfile_of_single_kappa
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {x : AnnularState S} {m : ℕ} {t : ℝ}
    (hν : x.2.1 = 0) (hκ : ∀ n, stateKappa S x n = if n = m then t else 0) :
    stateProfile D S C x = opticalLogPerturbation D.w (C.control m) t := by
  funext r
  have hterm : (fun n => stateKappa S x n * C.control n r) =
      fun n => if n = m then t * C.control m r else 0 := by
    funext n
    by_cases hn : n = m
    · subst n
      simp only [hκ, ite_true]
    · simp only [hκ, hn, ite_false, zero_mul]
  simp only [stateProfile, hν, zero_mul, zero_add, hterm,
    tsum_ite_eq, opticalLogPerturbation]

theorem N01Properties.originalCoefficients_zero_single_kappa
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} {m : ℕ} {t : ℝ}
    (hν : x.2.1 = 0) (hκ : ∀ n, stateKappa S x n = if n = m then t else 0)
    (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).a p =
        opticalLogPerturbation D.w (C.control m) t p.1 ∧
      (originalCoefficients D S C (x, 0)).b p = 0 ∧
      (originalCoefficients D S C (x, 0)).c p =
        deriv (opticalLogPerturbation D.w (C.control m) t) p.1 / p.1 := by
  have h := originalCoefficients_radial_zero x (contDiff_stateProfile_of_n01 hS hT hN x) p
  simpa only [stateProfile_of_single_kappa hν hκ] using h

theorem N01Properties.minusFlow_zero_single_kappa
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    {m : ℕ} {t : ℝ} (hν : x.2.1 = 0)
    (hκ : ∀ n, stateKappa S x n = if n = m then t else 0)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, 0) m r θ =
      θ - opticalTravel (opticalLogPerturbation D.w (C.control m) t) (C.left m) r := by
  rw [N01Properties.minusFlow_zero_eq_opticalTravel hN hS hT hx m θ hr,
    stateProfile_of_single_kappa hν hκ]

end ContinuousFlexibility.Statements
