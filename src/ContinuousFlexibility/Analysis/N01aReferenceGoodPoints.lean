import ContinuousFlexibility.Analysis.N01aReferenceGoodPointIntegral
import ContinuousFlexibility.Analysis.N01aReferenceWeightedRealizations
import ContinuousFlexibility.Analysis.N01aJacobiTransfer
import Mathlib.Topology.Order.Compact

/-!
# Actual reference energy has good points at every sufficiently large depth

The two spare-exponent output realizations give a summable weighted energy.
A minimum on each compact right band converts its integral estimate into
pointwise cubic exponential decay.  All points are taken from the actual
reference profile and the depth parameter is real.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

theorem continuous_n01aJacobiEnergy {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (n01aJacobiEnergy u) :=
  (hu.continuous.pow 2).add ((contDiff_infty_iff_deriv.mp hu).2.continuous.pow 2)

theorem n01aLocalizedDensity_energy_eq {D : ReferenceData} (hD : RadialPartition D)
    (hphi : ContDiff ℝ ∞ D.phi) (m : ℕ) :
    n01aLocalizedDensity D (n01aJacobiEnergy D.phi) m =
      referenceCellSquare D m (fun p => D.phi p.1 * Radial.cosineMode 2 p.2) +
      referenceCellSquare D m (fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2) := by
  rw [referenceCellSquare_cosine_lift D m D.phi 2 (by decide),
    referenceCellSquare_cosine_lift D m (deriv D.phi) 2 (by decide)]
  have hloc : Continuous (D.localizer m) := (hD.1 m).continuous
  have hderiv : Continuous (deriv D.phi) := (contDiff_infty_iff_deriv.mp hphi).2.continuous
  calc
    n01aLocalizedDensity D (n01aJacobiEnergy D.phi) m =
        ∫ r in D.a..D.b, (D.localizer m r * D.phi r) ^ 2 +
          (D.localizer m r * deriv D.phi r) ^ 2 := by
      unfold n01aLocalizedDensity
      apply intervalIntegral.integral_congr
      intro r _
      unfold n01aJacobiEnergy
      ring
    _ = _ := intervalIntegral.integral_add
      (((hloc.mul hphi.continuous).pow 2).intervalIntegrable D.a D.b)
      (((hloc.mul hderiv).pow 2).intervalIntegrable D.a D.b)

theorem n01a_energy_weighted_summable {D : ReferenceData} (hD : RadialPartition D)
    (hphi : ContDiff ℝ ∞ D.phi) {γ M : ℝ}
    (hvalue : OutputRealization D γ M 0
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0))
    (hderiv : OutputRealization D γ M 0
      ((fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2), 0)) :
    Summable (n01aWeightedDensity D γ M (n01aJacobiEnergy D.phi)) := by
  have hrem (f : PolarPoint → ℝ) : outputRemainder D 0 (f, 0) = f := by
    funext p
    simp only [outputRemainder, zero_mul, sub_zero]
  have hv : Summable (outputCellSquare D γ M
      (fun p => D.phi p.1 * Radial.cosineMode 2 p.2)) := by
    simpa only [hrem] using hvalue.2.1
  have hd : Summable (outputCellSquare D γ M
      (fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2)) := by
    simpa only [hrem] using hderiv.2.1
  apply (hv.add hd).congr
  intro m
  simp only [Pi.add_apply, n01aWeightedDensity,
    n01aLocalizedDensity_energy_eq hD hphi m, outputCellSquare, mul_add]

/-- Generic continuous nonnegative densities enjoy the same good-point
conclusion once their actual weighted cell integrals are summable. -/
theorem n01a_weighted_density_good_points {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) {e : ℝ → ℝ} (he : Continuous e)
    (he0 : ∀ r, 0 ≤ e r) {γ M : ℝ} (hγ : 0 < γ)
    (hs : Summable (n01aWeightedDensity D γ M e)) {p : ℝ}
    (hp : p ∈ radialCore D) :
    ∃ A c N₀ : ℝ, 0 < A ∧ 0 < c ∧ 0 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ r, r ∈ radialCore D ∧ p ≤ r ∧
        r ≤ D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) ∧
        e r ≤ A * Real.exp (-c * N ^ 3) := by
  obtain ⟨A, Nband, hA, hNband, hband⟩ :=
    n01a_weighted_density_right_band_integral hD he he0 hγ hs hp
  let c : ℝ := γ / 12
  have hc : 0 < c := by dsimp only [c]; positivity
  let N₀ : ℝ := Nband + (1 + |Real.log (D.b - p)|) + 2 / c + 1
  have hN₀ : 0 < N₀ := by dsimp only [N₀]; positivity
  refine ⟨2 * A, c / 2, N₀, by positivity, by positivity, hN₀, fun N hN => ?_⟩
  have hcut : 0 < 2 / c := by positivity
  have hNB : Nband ≤ N := by
    dsimp only [N₀] at hN
    linarith [abs_nonneg (Real.log (D.b - p))]
  have hgeo : 1 + |Real.log (D.b - p)| ≤ N := by
    dsimp only [N₀] at hN
    linarith
  have hloss : 2 / c ≤ N := by
    dsimp only [N₀] at hN
    linarith [abs_nonneg (Real.log (D.b - p))]
  let l : ℝ := D.b - Real.exp (-N ^ 2)
  let u : ℝ := D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2)
  have hlu : l < u := by dsimp only [l, u]; linarith [Real.exp_pos (-N ^ 2)]
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hlu.le) he.continuousOn
  have hmem := n01a_right_band_mem_core hp hgeo hr
  refine ⟨r, hmem.1, hmem.2, hr.2, ?_⟩
  have hminIntegral : (u - l) * e r ≤ ∫ x in l..u, e x := by
    have hi := intervalIntegral.integral_mono_on hlu.le
      ((continuous_const : Continuous (fun _ : ℝ => e r)).intervalIntegrable l u)
      (he.intervalIntegrable l u)
      (isMinOn_iff.mp hmin)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
  have hI : (∫ x in l..u, e x) ≤ A * Real.exp (-c * N ^ 3) := hband N hNB
  have hlen : u - l = (1 / 2 : ℝ) * Real.exp (-N ^ 2) := by
    dsimp only [u, l]
    ring
  have hcancel : Real.exp (N ^ 2) * Real.exp (-N ^ 2) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have havg : e r ≤ (2 * A) * Real.exp (N ^ 2 - c * N ^ 3) := by
    calc
      e r = (2 * Real.exp (N ^ 2)) * ((u - l) * e r) := by
        rw [hlen]
        calc
          e r = (Real.exp (N ^ 2) * Real.exp (-N ^ 2)) * e r := by
            rw [hcancel, one_mul]
          _ = _ := by ring
      _ ≤ (2 * Real.exp (N ^ 2)) * (A * Real.exp (-c * N ^ 3)) :=
        mul_le_mul_of_nonneg_left (hminIntegral.trans hI) (by positivity)
      _ = (2 * A) * (Real.exp (N ^ 2) * Real.exp (-c * N ^ 3)) := by ring
      _ = (2 * A) * Real.exp (N ^ 2 - c * N ^ 3) := by
        rw [← Real.exp_add, show N ^ 2 + -c * N ^ 3 = N ^ 2 - c * N ^ 3 by ring]
  exact havg.trans (mul_le_mul_of_nonneg_left (n01a_gaussian_loss_absorbed hc hloss)
    (by positivity))

theorem n01a_reference_good_points_of_weighted_realizations {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    (hvalue : OutputRealization D γ M 0
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0))
    (hderiv : OutputRealization D γ M 0
      ((fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2), 0))
    {p : ℝ} (hp : p ∈ radialCore D) :
    ∃ A c N₀ : ℝ, 0 < A ∧ 0 < c ∧ 0 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ r, r ∈ radialCore D ∧ p ≤ r ∧
        r ≤ D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) ∧
        n01aJacobiEnergy D.phi r ≤ A * Real.exp (-c * N ^ 3) := by
  obtain ⟨C, hC⟩ := hD
  have hphi : ContDiff ℝ ∞ D.phi := hC.1.2.2.2.1.1
  exact n01a_weighted_density_good_points hC (continuous_n01aJacobiEnergy hphi)
    (n01aJacobiEnergy_nonneg D.phi) hγ
    (n01a_energy_weighted_summable hC.2.1 hphi hvalue hderiv) hp

/-- The frozen reference axioms imply good points at every sufficiently
large real depth, with no additional decay or regularity hypotheses. -/
theorem exists_n01a_reference_good_points {D : ReferenceData} (hD : IsRadialReference D)
    {p : ℝ} (hp : p ∈ radialCore D) :
    ∃ A c N₀ : ℝ, 0 < A ∧ 0 < c ∧ 0 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ r, r ∈ radialCore D ∧ p ≤ r ∧
        r ≤ D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) ∧
        n01aJacobiEnergy D.phi r ≤ A * Real.exp (-c * N ^ 3) := by
  obtain ⟨ε, M, hε, _, hvalue, hderiv⟩ :=
    exists_reference_eigenfield_weighted_realizations hD
  apply n01a_reference_good_points_of_weighted_realizations hD.1
    (γ := referenceBeta + ε) (M := M) _ hvalue hderiv hp
  unfold referenceBeta
  linarith

end ContinuousFlexibility.Statements
