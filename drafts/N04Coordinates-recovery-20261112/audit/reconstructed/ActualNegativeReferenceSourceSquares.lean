import ContinuousFlexibility.Analysis.ActualNegativePrincipalDensity
import ContinuousFlexibility.Analysis.N04bReferenceActualTravel
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity
import ContinuousFlexibility.Analysis.RootPhysicalCharacteristicFlow

/-!
# Exact cancellation in the actual negative reference source multipliers

The stored reference chart is the radial optical chart, with its actual
root reparametrization. Its unit radial principal density determines the
height normalization. The two source multipliers containing the profile
derivative have no inverse optical-speed factor after squaring. This is
an identity for the original actual atlas, not a new normalization or an
assumption about a final primitive estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem reference_source_derivative_square
    {w v s h j d : ℝ} (hw : 0 < w) (hv : 0 < v) (hs : 0 < s)
    (hj : |j| = v / s)
    (hunit : h ^ 2 / |j| * (w * j ^ 2) = 1)
    (hd : d = -w * v ^ 2) :
    (h / |j| * d) ^ 2 = w * v * s ^ 3 := by
  have hj0 : |j| ≠ 0 := by rw [hj]; exact (div_pos hv hs).ne'
  have hnorm : h ^ 2 * w * |j| = 1 := by
    apply (mul_right_cancel₀ hj0)
    calc
      (h ^ 2 * w * |j|) * |j| = h ^ 2 * (w * j ^ 2) := by
        rw [← sq_abs j]
        ring
      _ = |j| := by
        have he := congrArg (fun x : ℝ => x * |j|) hunit
        field_simp [hj0] at he
        nlinarith only [he]
      _ = 1 * |j| := (one_mul _).symm
  have hh : h ^ 2 = s / (w * v) := by
    apply (eq_div_iff (mul_pos hw hv).ne').mpr
    rw [hj] at hnorm
    have he := congrArg (fun x : ℝ => x * s) hnorm
    field_simp [hs.ne'] at he
    nlinarith only [he]
  rw [hd, mul_pow, div_pow, hh, hj]
  field_simp [hw.ne', hv.ne', hs.ne']
  <;> ring

/-- The two differentiated-profile source terms are computed from the
same actual reference chart and height on the whole negative component.
The middle source multiplier containing `w` is deliberately not bounded
by this identity. -/
theorem n04Coordinates_actual_reference_negative_source_squares
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let t := n04bTravelOrientation (C.travel m) side
      (opticalTravel D.w (C.left m) p.1)
    let a := K.height (C.referenceState, 0) k p /
      |planeJacobian (K.chart (C.referenceState, 0) k) p|
    (a * (deriv D.w p.1 / p.1)) ^ 2 =
        (3 / 2 : ℝ) * D.w p.1 * opticalSpeed D.w p.1 * t ∧
      (a * deriv D.w p.1) ^ 2 =
        (3 / 2 : ℝ) * p.1 ^ 2 * D.w p.1 * opticalSpeed D.w p.1 * t := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let F := n04bActualTravelChart S C L z₀ m
  let v := opticalSpeed D.w p.1
  let t := n04bTravelOrientation (C.travel m) side (F p).1
  let ξ := (n04bRootPhysicalChart F (C.travel m) side p).1
  let s := Real.sqrt ξ
  let j := n04bRootDifferentialScale F (C.travel m) side p * v
  have hD : RadialProfileGeometry D := n04b_profileGeometry_of_through03 hN
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have href : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hp.1.1, hp.1.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have hr : 0 < p.1 := hD.1.trans hpD.1.1
  have hw : 0 < D.w p.1 := hD.2.2.2.2.1 p.1 hpD.1
  have hv : 0 < v := n04b_referenceOpticalSpeed_pos hD hC m hp.1
  have ht : 0 < t := n04b_travelOrientation_pos_of_fullStrip side
    ((n04b_actualTravelChart_bijOn hN hS hT hfield href hsref m).mapsTo hp).1
  have hξ : 0 < ξ := n04bRootPhysicalChart_fst_pos ht
  have hs : 0 < s := Real.sqrt_pos.mpr hξ
  have htravel : F =ᶠ[𝓝 p]
      (fun q : PolarPoint => (opticalTravel D.w (C.left m) q.1, q.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact n04b_reference_actualTravelChart hN.1.1.2.2.1 hT hS hN hfield m
      ⟨hq.1.1.le, hq.1.2.le⟩ q.2
  have hd := ((n04b_referenceTravel_hasDerivAt hD hC m hp.1).comp_hasFDerivAt p
    (hasFDerivAt_fst (p := p))).prodMk (hasFDerivAt_snd (p := p))
  have hF : DifferentiableAt ℝ F p :=
    hd.differentiableAt.congr_of_eventuallyEq htravel
  have hDF (q : PolarPoint) : fderiv ℝ F p q = (v * q.1, q.2) := by
    rw [htravel.fderiv_eq, hd.fderiv]
    simp only [v, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e href hsref k m side hi hp
  have hDK (q : PolarPoint) :
      fderiv ℝ (K.chart z₀ k) p q = (j * q.1, q.2) := by
    rw [hg.1.fderiv_eq, n04b_fderiv_rootPhysicalChart_apply hF ht q, hDF q]
    apply Prod.ext
    · change _ = (n04bRootDifferentialScale F (C.travel m) side p * v) * q.1
      ring
    · rfl
  have hJ : planeJacobian (K.chart z₀ k) p = j := by
    simp only [planeJacobian, hDK, mul_one, mul_zero, sub_zero]
  have hj : |j| = v / s := by
    rw [j, abs_mul, n04bRootDifferentialScale_abs ht, abs_of_pos hv]
    change s⁻¹ * v = v / s
    rw [div_eq_mul_inv, mul_comm]
  have ha : (L.coefficients z₀).a p = D.w p.1 :=
    (hN.2.1 z₀ href hsref p).trans (hN.1.1.reference_coefficients p).1
  have hunit : K.height z₀ k p ^ 2 / |j| * (D.w p.1 * j ^ 2) = 1 := by
    have h := (n04Coordinates_actualAtlas_negativePrincipalDensity
      hT hS hN hfield e href hsref k m side hi hp).1
    simpa only [coordinatePrincipalDensity, coefficientQuadratic, hDK, hJ, ha,
      mul_one, mul_zero, zero_pow two_ne_zero, add_zero] using h
  have hv2 : v ^ 2 = -deriv D.w p.1 / (p.1 * D.w p.1) :=
    Real.sq_sqrt (div_nonneg (neg_nonneg.mpr (hC.2.2.2.1 m p.1 hp.1).le)
      (mul_nonneg hr.le hw.le))
  have hcoef : deriv D.w p.1 / p.1 = -D.w p.1 * v ^ 2 := by
    rw [hv2]
    field_simp [hr.ne', hw.ne']
    <;> ring
  have hcube : s ^ 3 = (3 / 2 : ℝ) * t := by
    have he := n04b_rootTravel_rootCoordinate ht.le
    change (2 / 3 : ℝ) * ξ ^ (3 / 2 : ℝ) = t at he
    rw [rpow_three_halves_eq_mul_sqrt hξ.le] at he
    have hs2 : s ^ 2 = ξ := Real.sq_sqrt hξ.le
    calc
      s ^ 3 = ξ * s := by rw [show s ^ 3 = s ^ 2 * s by ring, hs2]
      _ = (3 / 2 : ℝ) * t := by change ξ * Real.sqrt ξ = _; linarith only [he]
  have hthird :
      (K.height z₀ k p / |j| * (deriv D.w p.1 / p.1)) ^ 2 =
        (3 / 2 : ℝ) * D.w p.1 * v * t := by
    rw [reference_source_derivative_square hw hv hs hj hunit hcoef, hcube]
    ring
  have hfirst :
      (K.height z₀ k p / |j| * deriv D.w p.1) ^ 2 =
        (3 / 2 : ℝ) * p.1 ^ 2 * D.w p.1 * v * t := by
    calc
      _ = p.1 ^ 2 * (K.height z₀ k p / |j| * (deriv D.w p.1 / p.1)) ^ 2 := by
        field_simp [hr.ne']
        <;> ring
      _ = _ := by rw [hthird]; ring
  have htvalue : t = n04bTravelOrientation (C.travel m) side
      (opticalTravel D.w (C.left m) p.1) := by
    exact congrArg (fun q : PolarPoint => n04bTravelOrientation (C.travel m) side q.1)
      htravel.self_of_nhds
  simpa only [hJ, ← htvalue] using And.intro hthird hfirst

end ContinuousFlexibility.Analysis
