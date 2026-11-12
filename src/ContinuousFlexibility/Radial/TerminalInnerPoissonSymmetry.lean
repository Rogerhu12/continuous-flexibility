import ContinuousFlexibility.Radial.ModeWeakGreen
import ContinuousFlexibility.Radial.ModeRegionalPairing
import ContinuousFlexibility.Radial.MatchingTraceCalculus

/-!
# Symmetry of the actual inner Poisson fluxes

The finite weak Green identity and the actual homogeneous scalar row
annihilate the alternating boundary form. Inserting normalized Poisson
values proves symmetry of the measured conormal-flux matrix, before any
MatchingLocalRealizations object is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def terminalInnerBoundaryForm (w : ℝ → ℝ) (l h : ℝ) (u v : ℝ → ℝ) : ℝ :=
  (u h * (w h * derivWithin v (Icc l h) h) -
    v h * (w h * derivWithin u (Icc l h) h)) -
  (u l * (w l * derivWithin v (Icc l h) l) -
    v l * (w l * derivWithin u (Icc l h) l))

/-- Homogeneous solutions in the genuine bordered graph have zero
alternating boundary form when their actual scalar rows vanish. -/
theorem modeInnerHomogeneous_boundary_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {l h : ℝ} (hlh : l < h) (hsub : Icc l h ⊆ radialCore D)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo l h)
    {U V : RadialModePair D} {u v : ℝ → ℝ}
    (hEqU : ModeLocalEquation D j (Ioo l h) U 0)
    (hEqV : ModeLocalEquation D j (Ioo l h) V 0)
    (hrepU : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hrepV : (V.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] v)
    (hu : ContDiffOn ℝ 1 u (Icc l h))
    (hv : ContDiffOn ℝ 1 v (Icc l h))
    (hrowU : if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * u r) = 0 else U.2 = 0)
    (hrowV : if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * v r) = 0 else V.2 = 0) :
    terminalInnerBoundaryForm D.w l h u v = 0 := by
  have hgreen := modeLocalEquation_green_pair_on_compact hD hB hEqU hEqV
    hrepU hrepV hlh hsub (fun _ hx => hx) hu hv
  have hsub' : Icc l h ⊆ Icc D.a D.b := hsub.trans Ioo_subset_Icc_self
  have hiu : IntervalIntegrable (fun r => referenceColumn D r * u r) volume l h := by
    change IntervalIntegrable (referenceColumn D * u) volume l h
    exact (((matchingColumn_continuousOn hD hB).mono hsub').mul
      hu.continuousOn).intervalIntegrable_of_Icc hlh.le
  have hiv : IntervalIntegrable (fun r => referenceColumn D r * v r) volume l h := by
    change IntervalIntegrable (referenceColumn D * v) volume l h
    exact (((matchingColumn_continuousOn hD hB).mono hsub').mul
      hv.continuousOn).intervalIntegrable_of_Icc hlh.le
  have hrestrict (p : ℝ → ℝ) :
      (∫ r in D.a..D.b, referenceColumn D r * p r) =
        ∫ r in l..h, referenceColumn D r * p r := by
    apply matchingInterval_eq_subinterval (Ioo_subset_Icc_self.trans hsub)
    intro r hr
    exact hcolumn (mul_ne_zero_iff.mp hr).1
  have hI :
      (∫ x in l..h,
        u x * (V.2 * referenceColumn D x -
          matchingDensity D x * (0 : RadialModePair D).1 x) -
        v x * (U.2 * referenceColumn D x -
          matchingDensity D x * (0 : RadialModePair D).1 x)) =
      V.2 * (∫ x in l..h, referenceColumn D x * u x) -
        U.2 * (∫ x in l..h, referenceColumn D x * v x) := by
    calc
      _ = ∫ x in l..h,
          V.2 * (referenceColumn D x * u x) -
            U.2 * (referenceColumn D x * v x) := by
        apply matchingSubinterval_congr_ae hD hlh.le hsub
        filter_upwards [(Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D) :
          ⇑(0 : RadialModeL2 D) =ᵐ[radialHilbertMeasure D] 0)] with r hr
        simp only [Prod.fst_zero, hr, Pi.zero_apply, mul_zero, sub_zero]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hiu.const_mul V.2) (hiv.const_mul U.2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hI] at hgreen
  change _ = terminalInnerBoundaryForm D.w l h u v at hgreen
  apply hgreen.symm.trans
  by_cases hj : j = 2
  · have hU : (∫ r in l..h, referenceColumn D r * u r) = 0 := by
      rw [← hrestrict u]
      simpa only [hj, ite_true] using hrowU
    have hV : (∫ r in l..h, referenceColumn D r * v r) = 0 := by
      rw [← hrestrict v]
      simpa only [hj, ite_true] using hrowV
    rw [hU, hV, mul_zero, mul_zero, sub_self]
  · have hU : U.2 = 0 := by simpa only [if_neg hj] using hrowU
    have hV : V.2 = 0 := by simpa only [if_neg hj] using hrowV
    rw [hU, hV, zero_mul, zero_mul, sub_self]

/-- The normalization turns the actual boundary form into the difference
of the two transposed measured flux entries. -/
theorem terminalInnerBoundaryForm_poisson {D : ReferenceData}
    (M : RadialMatchingData D) (p : Fin 2 → ℝ → ℝ)
    (htrace : ∀ i k, p i (matchingCut D M k) =
      (if i = k then 1 else 0) / sqrt (M.boundaryScale k)) (i k : Fin 2) :
    terminalInnerBoundaryForm D.w M.innerLeft M.innerRight (p i) (p k) =
      matchingInnerFlux D M (p k) i - matchingInnerFlux D M (p i) k := by
  have hleft (n : Fin 2) : p n M.innerLeft =
      (if n = 0 then 1 else 0) / sqrt (M.boundaryScale 0) := by
    simpa only [matchingCut, ite_true] using htrace n 0
  have hright (n : Fin 2) : p n M.innerRight =
      (if n = 1 then 1 else 0) / sqrt (M.boundaryScale 1) := by
    simpa only [matchingCut, show (1 : Fin 2) ≠ 0 by decide, ite_false] using htrace n 1
  unfold terminalInnerBoundaryForm
  rw [hleft i, hleft k, hright i, hright k]
  fin_cases i <;> fin_cases k <;>
    simp [matchingInnerFlux, matchingCut, bufferSign] <;> ring

theorem terminalInnerPoisson_flux_symmetric {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (M : RadialMatchingData D) (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (P : Fin 2 → RadialModePair D) (p : Fin 2 → ℝ → ℝ)
    (hEq : ∀ i, ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (P i) 0)
    (hrep : ∀ i, ((P i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p i)
    (hp : ∀ i, ContDiffOn ℝ 1 (p i) (Icc M.innerLeft M.innerRight))
    (hrow : ∀ i, if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * p i r) = 0 else (P i).2 = 0)
    (htrace : ∀ i k, p i (matchingCut D M k) =
      (if i = k then 1 else 0) / sqrt (M.boundaryScale k)) :
    ∀ i k, matchingInnerFlux D M (p k) i = matchingInnerFlux D M (p i) k := by
  intro i k
  have hzero := modeInnerHomogeneous_boundary_zero hD hB hlh hsub hcolumn
    (hEq i) (hEq k) (hrep i) (hrep k) (hp i) (hp k) (hrow i) (hrow k)
  rw [terminalInnerBoundaryForm_poisson M p htrace i k] at hzero
  exact sub_eq_zero.mp hzero

end ContinuousFlexibility.Radial
