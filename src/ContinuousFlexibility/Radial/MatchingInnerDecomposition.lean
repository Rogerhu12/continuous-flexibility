import ContinuousFlexibility.Radial.MatchingGraphRepresentatives
import ContinuousFlexibility.Radial.ModeGraphAlgebra
import Mathlib.Tactic.FieldSimp

/-!
# Local inverse decomposition by the Poisson columns

Subtracting the normalized boundary values from an inner local solution
gives the exact frozen Dirichlet graph. Local inverse uniqueness then
identifies the remaining part with the supplied local inverse.
The source is arbitrary, so the result applies both to kernel vectors
and to the smooth core used in the global inverse argument.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open ContinuousFlexibility.Statements

theorem matching_pair_sum_ae_restrict {D : ReferenceData} {S : Set ℝ}
    (P : Fin 2 → RadialModePair D) (p : Fin 2 → ℝ → ℝ) (x : Fin 2 → ℝ)
    (hP : ∀ i, ((P i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict S] p i) :
    (((∑ i, x i • P i).1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict S] fun r => ∑ i, x i * p i r := by
  simp only [Prod.fst_sum, Prod.smul_fst]
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => x i • (P i).1)).restrict.trans ?_
  have hall : ∀ᵐ r ∂(radialHilbertMeasure D).restrict S,
      ∀ i, (x i • (P i).1 : RadialModeL2 D) r = x i * p i r := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(Lp.coeFn_smul (x i) (P i).1).restrict, hP i] with r hs hp
    rw [hs, Pi.smul_apply, hp, smul_eq_mul]
  filter_upwards [hall] with r hr
  exact Finset.sum_congr rfl (fun i _ => hr i)

theorem matching_pair_sub_ae_restrict {D : ReferenceData} {S : Set ℝ}
    {U V : RadialModePair D} {u v : ℝ → ℝ}
    (hu : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict S] u)
    (hv : (V.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict S] v) :
    (((U - V).1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict S] fun r => u r - v r := by
  simp only [Prod.fst_sub]
  filter_upwards [(Lp.coeFn_sub U.1 V.1).restrict, hu, hv] with r hs hu' hv'
  rw [hs, Pi.sub_apply, hu', hv']

theorem matching_modeRow_finset_sum {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {ι : Type*} {j : ℕ} (s : Finset ι) (U F : ι → RadialModePair D)
    (h : ∀ i ∈ s, if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (U i).1 r) = (F i).2
      else (U i).2 = 0 ∧ (F i).2 = 0) :
    if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (∑ i ∈ s, U i).1 r) = (∑ i ∈ s, F i).2
    else (∑ i ∈ s, U i).2 = 0 ∧ (∑ i ∈ s, F i).2 = 0 := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simpa only [Finset.sum_empty, Prod.fst_zero, Prod.snd_zero] using matchingModeRow_zero hD hB j
  | @insert i s hi ih =>
      intro h
      simp only [Finset.sum_insert hi]
      exact matchingModeRow_add hD hB (h i (Finset.mem_insert_self i s))
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem matching_innerInverse_eq_sub_poisson {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hm : M.innerLeft < M.innerRight) (hscale : ∀ i, 0 < M.boundaryScale i)
    {U F : RadialModePair D} {u : ℝ → ℝ}
    (hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) U F)
    (hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
      else U.2 = 0 ∧ F.2 = 0)
    (hu : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] u)
    (hz : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0)
    (hreg : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight)) :
    M.innerInverse F = U - ∑ i,
      (Real.sqrt (M.boundaryScale i) * u (matchingCut D M i)) • M.innerPoisson i := by
  classical
  let x : Fin 2 → ℝ := fun i => Real.sqrt (M.boundaryScale i) * u (matchingCut D M i)
  let P : RadialModePair D := ∑ i, x i • M.innerPoisson i
  let p : ℝ → ℝ := fun r => ∑ i, x i * M.innerFunction i r
  have hdata := hM.2.2.2.2.2
  have hPa : (P.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] p :=
    matching_pair_sum_ae_restrict M.innerPoisson M.innerFunction x
      (fun i => (hdata i).1.restrict)
  have hPzero : (P.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0 := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      (matching_pair_sum_ae_restrict M.innerPoisson (fun _ _ => 0) x
        (fun i => (hdata i).2.2.1))
  have hps : ContDiffOn ℝ 1 p (Icc M.innerLeft M.innerRight) := by
    apply ContDiffOn.sum
    intro i hi
    exact contDiffOn_const.mul ((hdata i).2.2.2.2.1.of_le (by norm_num))
  have hpvalue : ∀ k, p (matchingCut D M k) = u (matchingCut D M k) := by
    intro k
    have hsqrt : Real.sqrt (M.boundaryScale k) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hscale k))
    calc
      p (matchingCut D M k) =
          ∑ i, x i * ((if i = k then 1 else 0) / Real.sqrt (M.boundaryScale k)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [((hdata i).2.2.2.2.2.2.2.2.2.2 k).1]
      _ = x k / Real.sqrt (M.boundaryScale k) := by
        rw [Finset.sum_eq_single k]
        · simp [div_eq_mul_inv]
        · intro i hi hik
          simp [hik]
        · intro hk
          exact (hk (Finset.mem_univ k)).elim
      _ = u (matchingCut D M k) := by
        dsimp only [x]
        field_simp [hsqrt]
  have hPeq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) P 0 := by
    have he := modeLocalEquation_finset_sum hD Finset.univ
      (fun i => x i • M.innerPoisson i) (fun i => x i • (0 : RadialModePair D))
      (fun i _ => modeLocalEquation_smul hD (hdata i).2.2.2.2.2.2.2.1 (x i))
    simpa only [P, smul_zero, Finset.sum_const_zero] using he
  have hProwEach : ∀ i, if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (M.innerPoisson i).1 r) =
        (0 : RadialModePair D).2
      else (M.innerPoisson i).2 = 0 ∧ (0 : RadialModePair D).2 = 0 := by
    intro i
    rcases hdata i with ⟨hae, _, _, _, _, _, _, _, _, hirow, _⟩
    by_cases hj : M.frequency = 2
    · simp only [if_pos hj]
      rw [matchingInterval_congr_ae hD
        (hae.mono (fun r hr => congrArg (fun t => referenceColumn D r * t) hr))]
      simpa only [if_pos hj, Prod.snd_zero] using hirow
    · simp only [if_neg hj]
      exact ⟨by simpa only [if_neg hj] using hirow, rfl⟩
  have hProw : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * P.1 r) = (0 : RadialModePair D).2
      else P.2 = 0 ∧ (0 : RadialModePair D).2 = 0 := by
    have he := matching_modeRow_finset_sum hD hB Finset.univ
      (fun i => x i • M.innerPoisson i) (fun i => x i • (0 : RadialModePair D))
      (fun i _ => matchingModeRow_smul hD hB (hProwEach i) (x i))
    simpa only [P, smul_zero, Finset.sum_const_zero] using he
  have hReq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (U - P) F := by
    simpa only [sub_zero] using modeLocalEquation_sub hD hEq hPeq
  have hRrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (U - P).1 r) = F.2
      else (U - P).2 = 0 ∧ F.2 = 0 := by
    have he := matchingModeRow_add hD hB hrow (matchingModeRow_smul hD hB hProw (-1))
    simpa only [neg_one_smul, neg_zero, add_zero, sub_eq_add_neg] using he
  have hRa := matching_pair_sub_ae_restrict hu hPa
  have hRzero : (((U - P).1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (matchingOuterRegion D M)] fun _ => 0 := by
    simpa only [sub_self] using matching_pair_sub_ae_restrict hz hPzero
  have hleft : (fun r => u r - p r) M.innerLeft = 0 := by
    simpa [matchingCut] using sub_eq_zero.mpr (hpvalue 0).symm
  have hright : (fun r => u r - p r) M.innerRight = 0 := by
    simpa [matchingCut] using sub_eq_zero.mpr (hpvalue 1).symm
  have hgraph := matching_innerGraph_of_representative hD hm hReq hRrow hRa hRzero
    (hreg.sub hps) hleft hright
  exact hM.2.1 (U - P) F hgraph

/-- Apply the local decomposition directly to a full modal graph. -/
theorem matching_innerInverse_source_eq_sub_poisson {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ i, 0 < M.boundaryScale i)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    {U F : RadialModePair D} {u : ℝ → ℝ}
    (hU : ModeFullGraph D M.frequency U F)
    (hreg : ContDiffOn ℝ 1 u (radialCore D))
    (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    M.innerInverse (M.sourceInner F) = M.sourceInner U - ∑ i,
      (Real.sqrt (M.boundaryScale i) * u (matchingCut D M i)) • M.innerPoisson i := by
  have hEq := (matching_modeLocalEquation_innerSource_iff hD hM).mpr
    (matching_modeLocalEquation_sourceInner hD hM ha hb hU.1)
  have hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (M.sourceInner U).1 r) = (M.sourceInner F).2
      else (M.sourceInner U).2 = 0 ∧ (M.sourceInner F).2 = 0 := by
    have h := hU.2
    by_cases hj : M.frequency = 2
    · simp only [if_pos hj] at h ⊢
      rw [matching_sourceInner_borderRow_eq hD hM hcolumn U, (hM.2.2.2.1 F).1]
      exact h
    · simp only [if_neg hj] at h ⊢
      rw [(hM.2.2.2.1 U).1, (hM.2.2.2.1 F).1]
      exact h
  have hreps := matching_sourceInner_representative hM hu
  exact matching_innerInverse_eq_sub_poisson hD hB hM hm hscale hEq hrow
    hreps.1 hreps.2 (hreg.mono (fun r hr =>
      ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩))

end ContinuousFlexibility.Radial
