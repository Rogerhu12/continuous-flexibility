import ContinuousFlexibility.Radial.TerminalLiftBoundaryTrace

/-!
# The actual inner Poisson matrix and its two-factor error

The columns are formed by the genuine Dirichlet correction L-GF.
Green's identity measures their physical conormal flux. The exact
lift-source pairing is supplied by the proved cutoff-energy identity
and support separation, not by prescribing a new energy matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Assemble genuine Poisson representatives, their symmetric physical
fluxes, and the entrywise error estimate. The exact lift-flux and
lift-source identities are outputs of the boundary-germ and cutoff
energy theorems for the same L and F. -/
theorem terminalInnerPoisson_matrix_estimate {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (M : RadialMatchingData D) (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (L F : Fin 2 → RadialModePair D) (ell : Fin 2 → ℝ → ℝ)
    (d energyError sigma : Fin 2 → ℝ) (sourceCost energyCost inverseCost eps : ℝ)
    (hL : ∀ i, ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L i) (F i))
    (hG : ∀ i, ModeInnerDirichletGraph D M (G (F i)) (F i))
    (hlrep : ∀ i, ((L i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell i)
    (hell : ∀ i, ContDiffOn ℝ 1 (ell i) (Icc M.innerLeft M.innerRight))
    (houtside : ∀ i r, r ∈ matchingOuterRegion D M → ell i r = 0)
    (hLscalar : ∀ i, (L i).2 = 0) (hFscalar : ∀ i, (F i).2 = 0)
    (hFfix : ∀ i, modeInnerSource D M.innerLeft M.innerRight (F i) = F i)
    (horth : ∀ i r, r ∈ Icc M.innerLeft M.innerRight → referenceColumn D r * ell i r = 0)
    (hltrace : ∀ i k, ell i (matchingCut D M k) =
      (if i = k then 1 else 0) / sqrt (M.boundaryScale k))
    (hfluxLift : ∀ i k, matchingInnerFlux D M (ell k) i = if i = k then d i else 0)
    (hpair : ∀ i k, modePairing D (L i) (F k) = if i = k then energyError i else 0)
    (hd : ∀ i, 0 ≤ d i) (hsourceCost : 0 ≤ sourceCost) (henergyCost : 0 ≤ energyCost)
    (hsource : ∀ i, ‖F i‖ ≤ (sourceCost * sqrt (d i)) * exp (-sigma i))
    (henergy : ∀ i, |energyError i| ≤ energyCost * d i * exp (-2 * sigma i))
    (hinverse : ‖G‖ ≤ inverseCost)
    (hbudget : ∀ i k, (energyCost + inverseCost * sourceCost ^ 2) *
      exp (-sigma i - sigma k) ≤ eps) :
    ∃ p : Fin 2 → ℝ → ℝ,
      (∀ i, (((L i - G (F i)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p i)) ∧
      (∀ i, ContDiffOn ℝ 1 (p i) (Icc M.innerLeft M.innerRight)) ∧
      (∀ i r, r ∈ matchingOuterRegion D M → p i r = 0) ∧
      (∀ i k, p i (matchingCut D M k) =
        (if i = k then 1 else 0) / sqrt (M.boundaryScale k)) ∧
      (∀ i, ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L i - G (F i)) 0) ∧
      (∀ i, if M.frequency = 2 then
        (∫ r in D.a..D.b, referenceColumn D r * p i r) = 0 else (L i - G (F i)).2 = 0) ∧
      (∀ i k, matchingInnerFlux D M (p i) k = matchingInnerFlux D M (p k) i) ∧
      (∀ i k, |matchingInnerFlux D M (p i) k - (if i = k then d i else 0)| ≤
        (energyCost + inverseCost * sourceCost ^ 2) * sqrt (d i) * sqrt (d k) *
          exp (-sigma i - sigma k)) ∧
      (∀ i k, |matchingInnerFlux D M (p i) k - (if i = k then d i else 0)| ≤
        eps * sqrt (d i) * sqrt (d k)) := by
  classical
  have horthall (i : Fin 2) (r : ℝ) : referenceColumn D r * ell i r = 0 := by
    by_cases hr : r ∈ Ioo M.innerLeft M.innerRight
    · exact horth i r (Ioo_subset_Icc_self hr)
    · have hzero : referenceColumn D r = 0 := by
        by_contra hn
        exact hr (hcolumn hn)
      rw [hzero, zero_mul]
  have hrowLift (i : Fin 2) : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * ell i r) = 0 else (L i).2 = 0 := by
    by_cases hj : M.frequency = 2
    · simp only [hj, ite_true]
      simp_rw [horthall i]
      exact intervalIntegral.integral_zero
    · simpa only [if_neg hj] using hLscalar i
  have hcolumns (i : Fin 2) := terminalInnerPoisson_correction hD hB M G (L i) (F i) (ell i)
    (hL i) (hG i) (hlrep i) (hell i) (houtside i) (hFscalar i) (hrowLift i)
  choose p hprep hp hpout hptrace hEq hrow using hcolumns
  have htrace (i k : Fin 2) : p i (matchingCut D M k) =
      (if i = k then 1 else 0) / sqrt (M.boundaryScale k) := by
    rw [hptrace i k]
    exact hltrace i k
  have hsym (i k : Fin 2) : matchingInnerFlux D M (p i) k = matchingInnerFlux D M (p k) i :=
    (terminalInnerPoisson_flux_symmetric hD hB M hlh hsub hcolumn
      (fun i => L i - G (F i)) p hEq hprep hp hrow htrace i k).symm
  have hflux (i k : Fin 2) : matchingInnerFlux D M (p i) k =
      matchingInnerFlux D M (ell k) i + modePairing D (L i - G (F i)) (F k) :=
    terminalInnerPoisson_flux_lift hD hB M hlh hsub i k (hEq i) (hL k)
      (hprep i) (hlrep k) (hp i) (hell k) (hLscalar k) (hFscalar k)
      (hFfix k) (horth k) (htrace i) (hltrace k)
  have hcorrection := terminalInnerPoisson_flux_correction M G L F p ell hflux
  have hdiagonal (i k : Fin 2) :
      |if i = k then energyError i else 0| ≤
        energyCost * sqrt (d i) * sqrt (d k) * exp (-sigma i - sigma k) := by
    by_cases hik : i = k
    · subst k
      rw [if_pos rfl]
      calc
        _ ≤ energyCost * d i * exp (-2 * sigma i) := henergy i
        _ = energyCost * (sqrt (d i) * sqrt (d i)) * exp (-2 * sigma i) := by
          rw [mul_self_sqrt (hd i)]
        _ = _ := by
          rw [show -2 * sigma i = -sigma i - sigma i by ring]
          ring
    · rw [if_neg hik, abs_zero]
      positivity
  have hcorrectionBound (i k : Fin 2) :
      |modePairing D (G (F i)) (F k)| ≤
        (inverseCost * sourceCost ^ 2) * sqrt (d i) * sqrt (d k) *
          exp (-sigma i - sigma k) := by
    have hc := terminalPoisson_correction_two_attenuations G (F i) (F k)
      (hFscalar k) (hsource i) (hsource k)
    calc
      _ ≤ (‖G‖ * (sourceCost * sqrt (d i)) * (sourceCost * sqrt (d k))) *
          exp (-sigma i - sigma k) := hc
      _ ≤ (inverseCost * (sourceCost * sqrt (d i)) * (sourceCost * sqrt (d k))) *
          exp (-sigma i - sigma k) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hinverse (mul_nonneg hsourceCost (sqrt_nonneg _)))
            (mul_nonneg hsourceCost (sqrt_nonneg _))) (exp_pos _).le
      _ = _ := by ring
  have hbound (i k : Fin 2) :
      |matchingInnerFlux D M (p i) k - (if i = k then d i else 0)| ≤
        (energyCost + inverseCost * sourceCost ^ 2) * sqrt (d i) * sqrt (d k) *
          exp (-sigma i - sigma k) := by
    have heq : matchingInnerFlux D M (p i) k - (if i = k then d i else 0) =
        (if i = k then energyError i else 0) - modePairing D (G (F i)) (F k) := by
      rw [hcorrection i k, hfluxLift i k, hpair i k]
      ring
    rw [heq]
    calc
      _ ≤ |if i = k then energyError i else 0| + |modePairing D (G (F i)) (F k)| := abs_sub _ _
      _ ≤ energyCost * sqrt (d i) * sqrt (d k) * exp (-sigma i - sigma k) +
          (inverseCost * sourceCost ^ 2) * sqrt (d i) * sqrt (d k) *
            exp (-sigma i - sigma k) := add_le_add (hdiagonal i k) (hcorrectionBound i k)
      _ = _ := by ring
  refine ⟨p, hprep, hp, hpout, htrace, hEq, hrow, hsym, hbound, ?_⟩
  intro i k
  calc
    _ ≤ (energyCost + inverseCost * sourceCost ^ 2) * sqrt (d i) * sqrt (d k) *
        exp (-sigma i - sigma k) := hbound i k
    _ = ((energyCost + inverseCost * sourceCost ^ 2) * exp (-sigma i - sigma k)) *
        (sqrt (d i) * sqrt (d k)) := by ring
    _ ≤ eps * (sqrt (d i) * sqrt (d k)) :=
      mul_le_mul_of_nonneg_right (hbudget i k) (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    _ = _ := by ring

end ContinuousFlexibility.Radial

