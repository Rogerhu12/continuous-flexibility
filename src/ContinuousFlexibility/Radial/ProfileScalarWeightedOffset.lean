import ContinuousFlexibility.Radial.ProfileScalarWeightedCaccioppoli
import ContinuousFlexibility.Radial.ProfileScalarSquareAlgebra
import ContinuousFlexibility.Radial.ProfileLeftOffsetFlux
import ContinuousFlexibility.Radial.R11bRadialCorrections

/-!
# Weighted first-normal estimate with the left-tail constant

The output remainder is used in the scalar energy estimate. Its forcing
differs by the compact flux of the true left cutoff, and the actual
derivative is recovered by adding the compact cutoff derivative. The
output exponent loss is the same uniform loss as in the estimate without
an offset; only the constant may depend on the attenuation exponent.
-/

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

namespace ContinuousFlexibility.Radial

theorem profile_scalar_weighted_caccioppoli_with_left_offset
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (M₀ M₁ : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ γ : ℝ, |γ| ≤ 1 →
      ∃ K : ℝ, 0 < K ∧
      ∀ (j a : ℝ) (u f : ℝ → ℝ) (x₀ q : ℝ),
      (j ≠ 0 → a = 0) →
      ContDiffOn ℝ 1 u (radialCore D) →
      MemLp u 2 (volume.restrict (radialCore D)) →
      MemLp f 2 (volume.restrict (radialCore D)) →
      x₀ ∈ radialCore D →
      (∀ r ∈ radialCore D, D.w r * deriv u r =
        intervalLocalPrimitive
          (fun y => f y + j ^ 2 * (deriv D.w y / y) * u y) x₀ r + q) →
      Summable (fun m =>
        exp (2 * M₀ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D f m) →
      Summable (fun m =>
        exp (-2 * M₁ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (fun r => u r - a * D.chiLeft r) m) →
      Summable (fun m =>
        exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (deriv u) m) ∧
      (∑' m,
        exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (deriv u) m) ≤
        K * ((∑' m,
          exp (2 * M₀ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            profileScalarCellSquare D f m) +
          (1 + j ^ 2) * (∑' m,
            exp (-2 * M₁ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
              profileScalarCellSquare D (fun r => u r - a * D.chiLeft r) m) + a ^ 2) := by
  obtain ⟨L, C₀, hL, hC₀, hbase⟩ := profile_scalar_weighted_caccioppoli hD M₀ M₁
  obtain ⟨C, h⟩ := hD
  have hgeom : RadialProfileGeometry D := h.1
  have hpart : RadialPartition D := h.2.1
  have hχ : ContDiff ℝ ∞ D.chiLeft := hborder.2.2.2.2.1
  have hχd : Continuous (deriv D.chiLeft) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  let χflux : ℝ → ℝ := deriv (fun t => D.w t * deriv D.chiLeft t)
  have hχflux : Continuous χflux := r11b_continuous_chiLeft_flux hgeom hborder
  refine ⟨L, hL, ?_⟩
  intro γ hγ
  let WF : ℕ → ℝ := fun n => exp (2 * M₀ * radialQ n + 2 * γ * radialS n)
  let WU : ℕ → ℝ := fun n => exp (-2 * M₁ * radialQ n + 2 * γ * radialS n)
  let WN : ℕ → ℝ := fun n => exp (-2 * (M₁ + L) * radialQ n + 2 * γ * radialS n)
  let QF : ℝ := ∑' m, WF (D.cellIndex m) * profileScalarCellSquare D χflux m
  let QD : ℝ := ∑' m, WN (D.cellIndex m) * profileScalarCellSquare D (deriv D.chiLeft) m
  have hWF (n : ℕ) : 0 ≤ WF n := (exp_pos _).le
  have hWU (n : ℕ) : 0 ≤ WU n := (exp_pos _).le
  have hWN (n : ℕ) : 0 ≤ WN n := (exp_pos _).le
  have hQF : 0 ≤ QF := tsum_nonneg (fun m =>
    mul_nonneg (hWF _) (profileScalarCellSquare_nonneg D χflux m))
  have hQD : 0 ≤ QD := tsum_nonneg (fun m =>
    mul_nonneg (hWN _) (profileScalarCellSquare_nonneg D (deriv D.chiLeft) m))
  let K : ℝ := 4 * C₀ * (QF + 1) + 2 * QD + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKf : 4 * C₀ ≤ K := by
    dsimp only [K]
    nlinarith only [mul_nonneg hC₀.le hQF, hQD]
  have hKu : 2 * C₀ ≤ K := (by linarith only [hC₀] : 2 * C₀ ≤ 4 * C₀).trans hKf
  have hKa : 4 * C₀ * QF + 2 * QD ≤ K := by dsimp only [K]; nlinarith only [hC₀]
  have hsχF : Summable (fun m =>
      WF (D.cellIndex m) * profileScalarCellSquare D χflux m) :=
    r11b_chiLeft_flux_scalar_source_summable ⟨C, h⟩ hborder γ M₀
  have hsχD : Summable (fun m =>
      WN (D.cellIndex m) * profileScalarCellSquare D (deriv D.chiLeft) m) :=
    r11b_chiLeft_deriv_scalar_output_summable ⟨C, h⟩ hborder γ (M₁ + L)
  refine ⟨K, hK, ?_⟩
  intro j a u f x₀ q ha hu huLp hfLp hx₀ hflux hsF hsR
  let v : ℝ → ℝ := fun r => u r - a * D.chiLeft r
  let g : ℝ → ℝ := fun r => f r - a * χflux r
  let q₀ : ℝ := q - D.w x₀ * (a * deriv D.chiLeft x₀)
  let SF : ℝ := ∑' m, WF (D.cellIndex m) * profileScalarCellSquare D f m
  let SR : ℝ := ∑' m, WU (D.cellIndex m) * profileScalarCellSquare D v m
  let SD : ℝ := ∑' m, WN (D.cellIndex m) * profileScalarCellSquare D (deriv v) m
  have hz : ContDiff ℝ ∞ (fun r => a * D.chiLeft r) := contDiff_const.mul hχ
  have hv : ContDiffOn ℝ 1 v (radialCore D) :=
    hu.sub (hz.of_le (by simp)).contDiffOn
  have hzLp : MemLp (fun r => a * D.chiLeft r) 2 (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous hz.continuous
  have hvLp : MemLp v 2 (volume.restrict (radialCore D)) := huLp.sub hzLp
  have haχFLp : MemLp (fun r => a * χflux r) 2 (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous (continuous_const.mul hχflux)
  have hgLp : MemLp g 2 (volume.restrict (radialCore D)) := hfLp.sub haχFLp
  have haχDLp : MemLp (fun r => a * deriv D.chiLeft r) 2
      (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous (continuous_const.mul hχd)
  obtain ⟨hsaF, hnormaF⟩ := profile_scalar_weighted_const_mul WF a hsχF
  obtain ⟨hsaD, hnormaD⟩ := profile_scalar_weighted_const_mul WN a hsχD
  obtain ⟨hsg, hgBound⟩ := profile_scalar_weighted_sub WF hWF
    (profile_memLp_localizer_mul hpart hfLp)
    (profile_memLp_localizer_mul hpart haχFLp) hsF hsaF
  have hgBound' :
      (∑' m, WF (D.cellIndex m) * profileScalarCellSquare D g m) ≤
        2 * (SF + a ^ 2 * QF) := by
    rw [hnormaF] at hgBound
    exact hgBound
  have hvflux : ∀ r ∈ radialCore D, D.w r * deriv v r =
      intervalLocalPrimitive
        (fun y => g y + j ^ 2 * (deriv D.w y / y) * v y) x₀ r + q₀ :=
    profile_flux_sub_left_offset hgeom hborder hu huLp hfLp j a x₀ q hx₀ ha hflux
  obtain ⟨hsDv, hDv⟩ := hbase γ j v g x₀ q₀ hγ hv hvLp hgLp hx₀ hvflux hsg hsR
  obtain ⟨hsAdd, hAdd⟩ := profile_scalar_weighted_add WN hWN
    (profile_memLp_localizer_deriv h hv)
    (profile_memLp_localizer_mul hpart haχDLp) hsDv hsaD
  have hder : deriv u =ᵐ[volume.restrict (radialCore D)]
      (fun r => deriv v r + a * deriv D.chiLeft r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hd := profile_deriv_left_remainder hborder hu a hr
    change deriv v r = deriv u r - a * deriv D.chiLeft r at hd
    change deriv u r = deriv v r + a * deriv D.chiLeft r
    linarith only [hd]
  have hsDu := (profile_scalar_weighted_summable_congr_ae WN hder).mpr hsAdd
  have hDu :
      (∑' m, WN (D.cellIndex m) * profileScalarCellSquare D (deriv u) m) ≤
        2 * (SD + a ^ 2 * QD) := by
    rw [profile_scalar_weighted_tsum_congr_ae WN hder]
    rw [hnormaD] at hAdd
    exact hAdd
  have hSF : 0 ≤ SF := tsum_nonneg (fun m =>
    mul_nonneg (hWF _) (profileScalarCellSquare_nonneg D f m))
  have hSR : 0 ≤ SR := tsum_nonneg (fun m =>
    mul_nonneg (hWU _) (profileScalarCellSquare_nonneg D v m))
  have hJ : 0 ≤ 1 + j ^ 2 := by positivity
  have hSD : SD ≤ C₀ * (2 * (SF + a ^ 2 * QF) + (1 + j ^ 2) * SR) :=
    hDv.trans (mul_le_mul_of_nonneg_left
      (add_le_add hgBound' le_rfl) hC₀.le)
  refine ⟨hsDu, hDu.trans ?_⟩
  calc
    2 * (SD + a ^ 2 * QD) ≤
        2 * (C₀ * (2 * (SF + a ^ 2 * QF) + (1 + j ^ 2) * SR) + a ^ 2 * QD) :=
      mul_le_mul_of_nonneg_left (add_le_add hSD le_rfl) (by norm_num)
    _ = (4 * C₀) * SF + (2 * C₀) * ((1 + j ^ 2) * SR) +
        (4 * C₀ * QF + 2 * QD) * a ^ 2 := by ring
    _ ≤ K * SF + K * ((1 + j ^ 2) * SR) + K * a ^ 2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hKf hSF)
        (mul_le_mul_of_nonneg_right hKu (mul_nonneg hJ hSR)))
        (mul_le_mul_of_nonneg_right hKa (sq_nonneg a))
    _ = K * (SF + (1 + j ^ 2) * SR + a ^ 2) := by ring

end ContinuousFlexibility.Radial
