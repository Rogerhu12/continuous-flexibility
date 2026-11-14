module

public import ContinuousFlexibility.Radial.MatchingInnerDecomposition
public import Mathlib.Tactic.Abel

/-!
# The actual external inner Poisson column from its leading buffer

A leading field with the one normalized external boundary value and its
actual local residual determine the original column in the matching
data. Frozen inner uniqueness proves the subtraction identity. This
does not identify the two external columns with the finite chain's
internal-interface Poisson map.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- The leading field and its local residual give the actual external
column. The subtraction identity is a conclusion of the original
inner Dirichlet uniqueness, including the scalar row. -/
theorem matchedInnerPoisson_eq_leading_sub_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hm : M.innerLeft < M.innerRight) (hscale : ∀ k, 0 < M.boundaryScale k)
    (i : Fin 2) (L f : RadialModeL2 D) (u : ℝ → ℝ)
    (hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L, 0) (f, 0))
    (hrow : (∫ r in D.a..D.b, referenceColumn D r * L r) = 0)
    (hu : (L : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] u)
    (hz : (L : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0)
    (hreg : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight))
    (htrace : ∀ k, u (matchingCut D M k) =
      (if i = k then 1 else 0) / Real.sqrt (M.boundaryScale k)) :
    M.innerPoisson i = (L, 0) - M.innerInverse (M.sourceInner (f, 0)) := by
  classical
  have heq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
      (L, 0) (M.sourceInner (f, 0)) :=
    (matching_modeLocalEquation_innerSource_iff hD hM).mpr hEq
  have hs : (M.sourceInner ((f, 0) : RadialModePair D)).2 = 0 :=
    (hM.2.2.2.1 (f, 0)).1
  have hrow' : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * ((L, 0) : RadialModePair D).1 r) =
        (M.sourceInner (f, 0)).2
      else ((L, 0) : RadialModePair D).2 = 0 ∧ (M.sourceInner (f, 0)).2 = 0 := by
    rw [hs]
    split_ifs
    · exact hrow
    · exact ⟨rfl, rfl⟩
  have hcoef (k : Fin 2) :
      Real.sqrt (M.boundaryScale k) * u (matchingCut D M k) =
        if i = k then 1 else 0 := by
    rw [htrace]
    field_simp [(Real.sqrt_pos.mpr (hscale k)).ne']
  have hsum :
      (∑ k : Fin 2, (Real.sqrt (M.boundaryScale k) * u (matchingCut D M k)) •
        M.innerPoisson k) = M.innerPoisson i := by
    rw [Finset.sum_eq_single i]
    · simp only [hcoef, if_pos rfl, ite_true, one_smul]
    · intro k _ hki
      rw [hcoef, if_neg (Ne.symm hki), zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hid := matching_innerInverse_eq_sub_poisson hD hB hM hm hscale
    heq hrow' hu hz hreg
  rw [hsum] at hid
  rw [hid]
  abel

end ContinuousFlexibility.Radial
