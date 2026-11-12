import ContinuousFlexibility.Analysis.N04bRootGermCollar
import ContinuousFlexibility.Analysis.N01CommonRootCharacteristicStrip
import ContinuousFlexibility.Analysis.N04bOpticalCoefficientVariation

/-!
# Actual corrected characteristic factors on a root collar

The N01 construction supplies the smooth square-root factor of the
original height operator. The actual uniform N03 coefficient collar
transfers this factor and the drift to the corrected operator.
All the functions below are constructed from the original height and
profile; the corrected characteristic identities are conclusions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- At a fixed true root and admissible state, the actual corrected speeds
have smooth periodic factors on a full two-sided strip. The displayed
characteristic equations hold on its physical nonnegative half, including
the root itself. The orientation parameter may have either sign. -/
theorem n04b_exists_corrected_root_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ σ : ℝ} (hr₀ : r₀ ∈ Ioo D.a D.b)
    (hroot : deriv D.w r₀ = 0) (hsign : σ * deriv (deriv D.w) r₀ < 0) :
    ∃ (δ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < δ ∧
      ContDiffOn ℝ ∞ d (Ioo (-δ) δ ×ˢ univ) ∧
      ContDiffOn ℝ ∞ c₀ (Ioo (-δ) δ ×ˢ univ) ∧
      Function.Periodic d (0, Real.pi) ∧
      Function.Periodic c₀ (0, Real.pi) ∧
      ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ),
        rootProfileShift r₀ σ p ∈ annularOpen D ∧ 0 < c₀ p ∧
        (0 ≤ p.1 →
          σ * minusCharacteristicSpeed (L.coefficients z) (rootProfileShift r₀ σ p) =
              d p - σ * Real.sqrt p.1 * c₀ p ∧
          σ * plusCharacteristicSpeed (L.coefficients z) (rootProfileShift r₀ σ p) =
              d p + σ * Real.sqrt p.1 * c₀ p) := by
  have hN := h03.1.1
  obtain ⟨g, ρ, _, _, hρ, _, _, hstate⟩ :=
    n01_exists_common_characteristic_root_strip hS hT hN hr₀ hroot hsign
  obtain ⟨η, hη, heq⟩ :=
    n04b_through03_root_coefficient_collar hS h03 hL hz hs hr₀ hroot
  let δ : ℝ := min ρ (η / (|σ| + 1))
  let w : ℝ → ℝ := stateProfile D S C z.1
  let H : PolarPoint → ℝ := stateHeight D S C z
  let d : PolarPoint → ℝ := orientedCharacteristicDrift w H r₀ σ
  let c₀ : PolarPoint → ℝ := factoredCharacteristicSpeed D.w g w H r₀ σ
  have hden : 0 < |σ| + 1 := by positivity
  have hδ : 0 < δ := lt_min_iff.mpr ⟨hρ, div_pos hη hden⟩
  have hsub : Ioo (-δ) δ ×ˢ (univ : Set ℝ) ⊆ Ioo (-ρ) ρ ×ˢ univ := by
    intro p hp
    exact ⟨abs_lt.mp ((abs_lt.mpr hp.1).trans_le (min_le_left _ _)), hp.2⟩
  have hdata := hstate z hz hs
  have hperiod := periodic_factoredCharacteristicField D.w g w
    (r := r₀) (σ := σ) (n04b_stateHeight_periodic (C := C) hS z)
  refine ⟨δ, d, c₀, hδ, hdata.2.1.mono hsub, hdata.1.mono hsub,
    hperiod.2, hperiod.1, ?_⟩
  intro p hp
  let y : PolarPoint := rootProfileShift r₀ σ p
  have hdist : |r₀ + σ * p.1 - r₀| < η := by
    have hsmall : |p.1| < η / (|σ| + 1) :=
      (abs_lt.mpr hp.1).trans_le (min_le_right _ _)
    have hm : |p.1| * (|σ| + 1) < η := (lt_div_iff₀ hden).mp hsmall
    calc
      |r₀ + σ * p.1 - r₀| = |σ| * |p.1| := by
        rw [add_sub_cancel_left, abs_mul]
      _ ≤ (|σ| + 1) * |p.1| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < η := by simpa only [mul_comm] using hm
  have hcoeff : y.1 ∈ Ioo D.a D.b ∧
      (L.coefficients z).a y = (originalCoefficients D S C z).a y ∧
      (L.coefficients z).b y = (originalCoefficients D S C z).b y ∧
      (L.coefficients z).c y = (originalCoefficients D S C z).c y :=
    heq (r₀ + σ * p.1) p.2 hdist
  have hy : y ∈ annularOpen D := ⟨hcoeff.1, mem_univ _⟩
  have hfactor := hdata.2.2 p (hsub hp)
  refine ⟨hy, hfactor.1, ?_⟩
  intro hx
  obtain ⟨_, hBounds⟩ := hN.1.1
  have hGeom : RadialProfileGeometry D := hBounds.1
  have hyr : 0 < y.1 := hGeom.1.trans hy.1.1
  have hwpos : 0 < w y.1 :=
    mul_pos (hGeom.2.2.2.2.1 y.1 hy.1) (Real.exp_pos _)
  have hbound := hN.2.2.2.2.2.2.2.2.2.1 z hz hs y hy
  have hQ : 0 < heightQ (profileEnergy w y) (heightRadial H y)
      (angularPartial (heightAngular H) y) := by
    have hq := (le_div_iff₀ hwpos).mp hbound.2.2.1
    nlinarith
  have hD : 0 < polarDiscriminant w H y := by
    linarith [hbound.2.2.2.2.1]
  have hdrift : (L.coefficients z).b y / (L.coefficients z).a y =
      characteristicDrift w H y := by
    rw [hcoeff.2.1, hcoeff.2.2.1]
    exact (n04b_characteristicDrift_eq_corrected_ratio
      ((n04b_contDiff_stateHeight hT hS hN z).contDiffAt.of_le (by simp))
      hyr.ne' hD hQ).symm
  have hspeed : Real.sqrt ((L.coefficients z).b y ^ 2 -
        (L.coefficients z).a y * (L.coefficients z).c y) /
        (L.coefficients z).a y = Real.sqrt p.1 * c₀ p := by
    by_cases hx0 : p.1 = 0
    · have hyroot : deriv D.w y.1 = 0 := by
        simpa only [y, rootProfileShift, hx0, mul_zero, add_zero] using hroot
      have hdet := n04b_through03_determinant_eq_zero hT hS h03 hz hs hy hyroot
      have hzero : (L.coefficients z).b y ^ 2 -
          (L.coefficients z).a y * (L.coefficients z).c y = 0 := by linarith
      simp only [hzero, Real.sqrt_zero, zero_div, hx0, zero_mul]
    · have hxp : 0 < p.1 := lt_of_le_of_ne hx (Ne.symm hx0)
      have hvpos : 0 < characteristicSpeed w H y := by
        rw [hfactor.2.2.2 hx]
        exact mul_pos (Real.sqrt_pos.mpr hxp) hfactor.1
      have hneg : deriv w y.1 < 0 := by
        by_contra hn
        have hnonneg : 0 ≤ deriv w y.1 := le_of_not_gt hn
        have hrad : -w y.1 * deriv w y.1 / y.1 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hwpos.le) hnonneg) hyr.le
        have hzero : characteristicSpeed w H y = 0 := by
          simp only [characteristicSpeed, Real.sqrt_eq_zero_of_nonpos hrad,
            zero_mul, zero_div]
        rw [hzero] at hvpos
        exact lt_irrefl _ hvpos
      have hv := n04b_characteristicSpeed_eq_corrected_ratio
        ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) y.1)
        hyr hwpos hneg hD hQ
      rw [hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2]
      exact hv.symm.trans (hfactor.2.2.2 hx)
  constructor
  · change σ * ((L.coefficients z).b y / (L.coefficients z).a y -
      Real.sqrt ((L.coefficients z).b y ^ 2 -
        (L.coefficients z).a y * (L.coefficients z).c y) /
          (L.coefficients z).a y) = _
    rw [hdrift, hspeed]
    dsimp only [d, orientedCharacteristicDrift]
    ring
  · change σ * ((L.coefficients z).b y / (L.coefficients z).a y +
      Real.sqrt ((L.coefficients z).b y ^ 2 -
        (L.coefficients z).a y * (L.coefficients z).c y) /
          (L.coefficients z).a y) = _
    rw [hdrift, hspeed]
    dsimp only [d, orientedCharacteristicDrift]
    ring

end ContinuousFlexibility.Analysis
