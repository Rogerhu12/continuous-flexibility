module

public import ContinuousFlexibility.Radial.TerminalPoissonMatrixEstimate
public import ContinuousFlexibility.Radial.ModeHomogeneousRegularity
public import ContinuousFlexibility.Radial.MatchedPiecesAssembly

/-!
# The complete inner Poisson companion for one matching geometry

The actual Dirichlet correction constructs the columns. Their same
representatives gain C² regularity from the homogeneous weak equation.
The flux matrix is measured from those representatives. These three
outputs fill exactly the final block of MatchingInnerRealizations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Exactly the inner Poisson clauses, before assigning the three
constructed fields of the single matching datum. -/
def TerminalInnerPoissonColumns (D : ReferenceData) (M : RadialMatchingData D)
    (P : Fin 2 → RadialModePair D) (p : Fin 2 → ℝ → ℝ) (Db : RadialMatrix) : Prop :=
  ∀ i,
    ((P i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p i ∧
    ((P i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] (fun _ => 0) ∧
    ContDiffOn ℝ 2 (p i) (Icc M.innerLeft M.innerRight) ∧
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (P i) 0 ∧
    (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * p i r) = 0 else (P i).2 = 0) ∧
    (∀ k, p i (matchingCut D M k) = (if i = k then 1 else 0) /
      sqrt (M.boundaryScale k) ∧ Db k i = matchingInnerFlux D M (p i) k)

/-- Actual cutoff data and the actual inner inverse produce every
Poisson field needed by the frozen matching predicate. -/
theorem terminalInnerPoisson_columns_exists {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (M : RadialMatchingData D) (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (L F : Fin 2 → RadialModePair D) (ell : Fin 2 → ℝ → ℝ)
    (d energyError sigma : Fin 2 → ℝ) (sourceCost energyCost inverseCost eps : ℝ)
    (hL : ∀ i, ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L i) (F i))
    (hG : ∀ i, ModeInnerDirichletGraph D M (M.innerInverse (F i)) (F i))
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
    (hinverse : ‖M.innerInverse‖ ≤ inverseCost)
    (hbudget : ∀ i k, (energyCost + inverseCost * sourceCost ^ 2) *
      exp (-sigma i - sigma k) ≤ eps) :
    ∃ (P : Fin 2 → RadialModePair D) (p : Fin 2 → ℝ → ℝ) (Db : RadialMatrix),
      (∀ i, P i = L i - M.innerInverse (F i)) ∧
      (∀ i k, Db k i = matchingInnerFlux D M (p i) k) ∧
      TerminalInnerPoissonColumns D M P p Db ∧
      (∀ i k, Db i k = Db k i) ∧
      (∀ i k, |Db i k - (if i = k then d i else 0)| ≤ eps * sqrt (d i) * sqrt (d k)) := by
  obtain ⟨p, hprep, hp, hpout, htrace, hEq, hrow, hsym, _, hestimate⟩ :=
    terminalInnerPoisson_matrix_estimate hD hB M hlh hsub hcolumn M.innerInverse L F ell
      d energyError sigma sourceCost energyCost inverseCost eps hL hG hlrep hell houtside
      hLscalar hFscalar hFfix horth hltrace hfluxLift hpair hd hsourceCost henergyCost
      hsource henergy hinverse hbudget
  let P : Fin 2 → RadialModePair D := fun i => L i - M.innerInverse (F i)
  let Db : RadialMatrix := fun k i => matchingInnerFlux D M (p i) k
  have hp₂ (i : Fin 2) : ContDiffOn ℝ 2 (p i) (Icc M.innerLeft M.innerRight) :=
    modeLocalHomogeneous_contDiffOn_two hD hB (hEq i) (hprep i) hlh hsub (fun _ hx => hx) (hp i)
  have houter (i : Fin 2) :
      ((P i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
        (matchingOuterRegion D M)] (fun _ => 0) := by
    have hm : MeasurableSet (matchingOuterRegion D M) :=
      measurableSet_Ioo.union measurableSet_Ioo
    filter_upwards [ae_restrict_of_ae (hprep i), ae_restrict_mem hm] with r hr hri
    exact hr.trans (hpout i r hri)
  refine ⟨P, p, Db, fun _ => rfl, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hprep i, houter i, hp₂ i, hEq i, hrow i, fun k => ⟨htrace i k, rfl⟩⟩
  · intro i k
    exact (hsym i k).symm
  · intro i k
    have hh := hestimate k i
    by_cases hik : i = k
    · subst k
      exact hh
    · simpa only [Db, if_neg hik, if_neg (Ne.symm hik), mul_comm, mul_left_comm, mul_assoc] using hh

/-- The three constructed fields are assigned to the same matching
datum. All remaining inner clauses are the original actual inverse
and source clauses; the public record is not changed or weakened. -/
theorem matchingInnerRealizations_of_terminal_columns {D : ReferenceData}
    (M : RadialMatchingData D)
    (hsolve : ∀ F, (M.frequency ≠ 2 → F.2 = 0) →
      ModeInnerDirichletGraph D M (M.innerInverse (M.sourceInner F)) (M.sourceInner F))
    (hunique : ∀ U F, ModeInnerDirichletGraph D M U F → M.innerInverse F = U)
    (hsource : ∀ F, (M.sourceInner F).2 = F.2 ∧
      ((M.sourceInner F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        (fun r => if r ∈ Ioo M.innerLeft M.innerRight then F.1 r else 0))
    (hrepresentative : ∀ F,
      ((M.innerInverse (M.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] M.innerRepresentative F ∧
      ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
        (M.innerInverse (M.sourceInner F)) (M.sourceInner F) ∧
      ContDiffOn ℝ 1 (M.innerRepresentative F) (Icc M.innerLeft M.innerRight) ∧
      (∀ r ∈ matchingOuterRegion D M, M.innerRepresentative F r = 0) ∧
      (if M.frequency = 2 then
        (∫ r in D.a..D.b, referenceColumn D r * M.innerRepresentative F r) = F.2
       else (M.innerInverse (M.sourceInner F)).2 = 0) ∧
      (∀ i, M.innerRepresentative F (matchingCut D M i) = 0))
    (P : Fin 2 → RadialModePair D) (p : Fin 2 → ℝ → ℝ) (Db : RadialMatrix)
    (hcolumns : TerminalInnerPoissonColumns D M P p Db)
    (hPfield : M.innerPoisson = P) (hpfield : M.innerFunction = p) (hDbfield : M.Db = Db) :
    MatchingInnerRealizations D M := by
  refine ⟨hsolve, hunique, hsource, hrepresentative, ?_⟩
  intro i
  simpa only [hPfield, hpfield, hDbfield] using hcolumns i

end ContinuousFlexibility.Radial

