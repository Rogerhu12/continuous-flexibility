module

public import ContinuousFlexibility.Radial.TerminalInnerPoissonSymmetry
public import ContinuousFlexibility.Radial.TerminalPoissonCorrection
public import ContinuousFlexibility.Radial.ModeInnerSourcePairing

/-!
# The actual Poisson flux correction identity

The weak Green identity between a homogeneous corrected column and an
actual cutoff lift identifies the measured conormal flux.  Substituting
P = L - G F then exposes one source factor on each side of the inverse.
No abstract energy matrix is substituted for the physical flux matrix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem terminalInnerBoundaryForm_mixed_normalized {D : ReferenceData}
    (M : RadialMatchingData D) (p q : ℝ → ℝ) (i k : Fin 2)
    (hp : ∀ n, p (matchingCut D M n) =
      (if i = n then 1 else 0) / sqrt (M.boundaryScale n))
    (hq : ∀ n, q (matchingCut D M n) =
      (if k = n then 1 else 0) / sqrt (M.boundaryScale n)) :
    terminalInnerBoundaryForm D.w M.innerLeft M.innerRight p q =
      matchingInnerFlux D M q i - matchingInnerFlux D M p k := by
  have hpl : p M.innerLeft =
      (if i = 0 then 1 else 0) / sqrt (M.boundaryScale 0) := by
    simpa only [matchingCut, ite_true] using hp 0
  have hpr : p M.innerRight =
      (if i = 1 then 1 else 0) / sqrt (M.boundaryScale 1) := by
    simpa only [matchingCut, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hp 1
  have hql : q M.innerLeft =
      (if k = 0 then 1 else 0) / sqrt (M.boundaryScale 0) := by
    simpa only [matchingCut, ite_true] using hq 0
  have hqr : q M.innerRight =
      (if k = 1 then 1 else 0) / sqrt (M.boundaryScale 1) := by
    simpa only [matchingCut, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hq 1
  unfold terminalInnerBoundaryForm
  rw [hpl, hpr, hql, hqr]
  fin_cases i <;> fin_cases k <;>
    simp [matchingInnerFlux, matchingCut, bufferSign] <;> ring

/-- Pairing with the actual terminal lift measures a Poisson flux entry. -/
theorem terminalInnerPoisson_flux_lift {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (M : RadialMatchingData D) (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    {P L F : RadialModePair D} {p ell : ℝ → ℝ} (i k : Fin 2)
    (hP : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) P 0)
    (hL : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) L F)
    (hprep : (P.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p)
    (hlrep : (L.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell)
    (hp : ContDiffOn ℝ 1 p (Icc M.innerLeft M.innerRight))
    (hell : ContDiffOn ℝ 1 ell (Icc M.innerLeft M.innerRight))
    (hLscalar : L.2 = 0) (hFscalar : F.2 = 0)
    (hFfix : modeInnerSource D M.innerLeft M.innerRight F = F)
    (horth : ∀ r ∈ Icc M.innerLeft M.innerRight,
      referenceColumn D r * ell r = 0)
    (hptrace : ∀ n, p (matchingCut D M n) =
      (if i = n then 1 else 0) / sqrt (M.boundaryScale n))
    (hltrace : ∀ n, ell (matchingCut D M n) =
      (if k = n then 1 else 0) / sqrt (M.boundaryScale n)) :
    matchingInnerFlux D M p k = matchingInnerFlux D M ell i + modePairing D P F := by
  have hgreen := modeLocalEquation_green_pair_on_compact hD hB hP hL hprep hlrep
    hlh hsub (fun _ hx => hx) hp hell
  have hz : ∀ᵐ r ∂volume, r ∈ Icc M.innerLeft M.innerRight →
      (0 : RadialModeL2 D) r = 0 := by
    apply (ae_restrict_iff' measurableSet_Icc).mp
    exact matchingSubinterval_ae hD hsub
      (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D))
  have hI :
      (∫ r in M.innerLeft..M.innerRight,
        p r * (L.2 * referenceColumn D r - matchingDensity D r * F.1 r) -
          ell r * (P.2 * referenceColumn D r -
            matchingDensity D r * (0 : RadialModePair D).1 r)) =
        -modePairing D P F := by
    rw [modeInnerSource_pairing_eq_integral hD hlh.le hsub P F hFfix hFscalar hprep,
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hz] with r hr hri
    have hrc : r ∈ Icc M.innerLeft M.innerRight := by
      simpa only [uIcc_of_le hlh.le] using uIoc_subset_uIcc hri
    simp only [hLscalar, zero_mul, zero_sub, Prod.fst_zero, hr hrc, mul_zero, sub_zero]
    have hcross : ell r * (P.2 * referenceColumn D r) = 0 := by
      calc
        _ = P.2 * (referenceColumn D r * ell r) := by ring
        _ = 0 := by rw [horth r hrc, mul_zero]
    rw [hcross, sub_zero]
    ring
  rw [hI] at hgreen
  change -modePairing D P F =
    terminalInnerBoundaryForm D.w M.innerLeft M.innerRight p ell at hgreen
  rw [terminalInnerBoundaryForm_mixed_normalized M p ell i k hptrace hltrace] at hgreen
  linarith only [hgreen]

/-- Subtracting the actual Dirichlet correction produces the physical
flux identity with two independent residual factors. -/
theorem terminalInnerPoisson_flux_correction {D : ReferenceData}
    (M : RadialMatchingData D) (G : RadialModePair D →L[ℝ] RadialModePair D)
    (L F : Fin 2 → RadialModePair D) (p ell : Fin 2 → ℝ → ℝ)
    (hflux : ∀ i k, matchingInnerFlux D M (p i) k =
      matchingInnerFlux D M (ell k) i + modePairing D (L i - G (F i)) (F k)) :
    ∀ i k, matchingInnerFlux D M (p i) k =
      matchingInnerFlux D M (ell k) i + modePairing D (L i) (F k) -
        modePairing D (G (F i)) (F k) := by
  intro i k
  rw [hflux i k, modePairing_sub_left]
  ring

end ContinuousFlexibility.Radial
