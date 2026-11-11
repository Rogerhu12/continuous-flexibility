import ContinuousFlexibility.Radial.MatchingOuterGreen
import ContinuousFlexibility.Radial.MatchingInnerCorePairing
import ContinuousFlexibility.Radial.MatchingBoundaryAlgebra

/-!
# Outer Poisson reciprocity for the actual smooth source

The normalized exterior trace of a smooth input is A z - B x.
The outer weak Green identity proves this from the prescribed Poisson
columns and the actual Hilbert pairing, including tests approaching the
degenerate endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchingOuter_smooth_green_boundary {D : ReferenceData}
    {M : RadialMatchingData D}
    (hscale : ∀ k, 0 < M.boundaryScale k)
    (hdiag : ∀ k n, k ≠ n → M.A k n = 0 ∧ M.B k n = 0)
    (i : Fin 2) (p ψ : ℝ → ℝ)
    (hp : ∀ k, p (matchingCut D M k) = M.A k i / sqrt (M.boundaryScale k))
    (hflux : ∀ k, matchingOuterFlux D M p k = M.B k i) :
    (p M.innerRight * (D.w M.innerRight * deriv ψ M.innerRight) -
      ψ M.innerRight * (D.w M.innerRight *
        derivWithin p (closure (matchingOuterRegion D M)) M.innerRight)) -
    (p M.innerLeft * (D.w M.innerLeft * deriv ψ M.innerLeft) -
      ψ M.innerLeft * (D.w M.innerLeft *
        derivWithin p (closure (matchingOuterRegion D M)) M.innerLeft)) =
      M.A i i * matchingSmoothBoundaryFlux D M ψ i -
        M.B i i * matchingSmoothBoundaryValue D M ψ i := by
  have hpL : p M.innerLeft = M.A 0 i / sqrt (M.boundaryScale 0) := by
    simpa only [matchingCut, if_pos rfl] using hp 0
  have hpR : p M.innerRight = M.A 1 i / sqrt (M.boundaryScale 1) := by
    simpa [matchingCut] using hp 1
  have hn0 : sqrt (M.boundaryScale 0) ≠ 0 := (sqrt_pos.mpr (hscale 0)).ne'
  have hn1 : sqrt (M.boundaryScale 1) ≠ 0 := (sqrt_pos.mpr (hscale 1)).ne'
  have he :
      (p M.innerRight * (D.w M.innerRight * deriv ψ M.innerRight) -
        ψ M.innerRight * (D.w M.innerRight *
          derivWithin p (closure (matchingOuterRegion D M)) M.innerRight)) -
      (p M.innerLeft * (D.w M.innerLeft * deriv ψ M.innerLeft) -
        ψ M.innerLeft * (D.w M.innerLeft *
          derivWithin p (closure (matchingOuterRegion D M)) M.innerLeft)) =
      (M.A 0 i * matchingSmoothBoundaryFlux D M ψ 0 -
        M.B 0 i * matchingSmoothBoundaryValue D M ψ 0) +
      (M.A 1 i * matchingSmoothBoundaryFlux D M ψ 1 -
        M.B 1 i * matchingSmoothBoundaryValue D M ψ 1) := by
    rw [hpL, hpR, ← hflux 0, ← hflux 1]
    simp [matchingSmoothBoundaryValue, matchingSmoothBoundaryFlux,
      matchingOuterFlux, matchingCut, bufferSign] <;>
      field_simp [hn0, hn1] <;> ring
  rw [he]
  fin_cases i
  · rw [(hdiag 1 0 (by decide)).1, (hdiag 1 0 (by decide)).2]
    ring
  · rw [(hdiag 0 1 (by decide)).1, (hdiag 0 1 (by decide)).2]
    ring

theorem matchingOuterPoisson_testSource_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k)
    (hdiag : ∀ k n, k ≠ n → M.A k n = 0 ∧ M.B k n = 0)
    (hM : MatchingLocalRealizations D M)
    (i : Fin 2) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : Function.support ψ ⊆ radialCore D) (s : ℝ) :
    modePairing D (M.outerPoisson i)
      (M.sourceOuter (matchingTestSource D hD hB M.frequency ψ hψ s)) =
      M.A i i * matchingSmoothBoundaryFlux D M ψ i -
        M.B i i * matchingSmoothBoundaryValue D M ψ i := by
  rcases hM.2.2.2.2.2 i with
    ⟨_, hrep, _, _, _, hreg, hscalar, _, hEq, _, htrace⟩
  have hfix := matching_sourceOuter_outerPoisson hM i
  have hrow : ⟪(M.outerPoisson i).1, matchingBorderVector D hD hB⟫_ℝ = 0 := by
    rw [← matchingColumn_integral_eq_inner hD hB]
    exact matching_outerPoisson_borderRow_zero hD hM hcolumn i
  have hpair :
      modePairing D (M.outerPoisson i)
        (M.sourceOuter (matchingTestSource D hD hB M.frequency ψ hψ s)) =
      -(∫ x in D.a..D.b, (M.outerPoisson i).1 x *
        radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ x) := by
    rw [matchingSourceOuter_pairing_of_fixed D M hM _ _ hfix,
      matchingTestSource_pairing,
      matchingJacobi_integral_eq_inner hD (M.outerPoisson i).1 hψ M.frequency]
    simp only [hscalar, hrow, zero_mul, mul_zero, add_zero, ite_self]
  have hg := matchingOuter_green_test hD hB hM ha hm hb hfix hEq hrep
    (hreg.of_le (by norm_num)) hψ hcψ hsψ
  rw [hpair, hg]
  have ht := matchingOuter_smooth_green_boundary hscale hdiag i
    (M.outerFunction i) ψ (fun k => (htrace k).2.2.1)
      (fun k => (htrace k).2.2.2)
  linarith only [ht]

end ContinuousFlexibility.Radial
