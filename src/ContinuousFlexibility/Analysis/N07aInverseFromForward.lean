module

public import ContinuousFlexibility.Analysis.N07aNormalizedInverseMap
public import ContinuousFlexibility.Analysis.N07aInverseContinuity
public import ContinuousFlexibility.Analysis.SolveReturnEquations
public import ContinuousFlexibility.Statements.N07aRegularity

/-!
# Closing the smooth inverse from the actual physical forward map

The linear inverse hypotheses are the first three clauses of the final
target. The forward premise in this internal assembly lemma is a genuine
source-valued continuous linear family with the actual physical decoder.
The concrete forward construction supplies it in the smooth subnode.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n07a_source_ext_core (hS : IsPhysicalSpaces D T S)
    {f g : S.Source}
    (h : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode f.val p = (S.height (3 / 4 : ℝ)).decode g.val p) :
    f = g := by
  apply Subtype.ext
  apply (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext p
  by_cases hp : p ∈ annularOpen D
  · exact h p hp
  · rw [((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).2.2.2.1 p hp,
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 g.val).2.2.2.1 p hp]

theorem n07a_scalarInverse_smooth_of_actualForward
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {G : ScalarInverseData S} {base : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hLinear : ScalarLinearInverseProperties D S C L G base ε)
    (F : (StateDirections S × ℝ) → N07aNormalizedUnknown hD hT hS →L[ℝ] S.Source)
    (hF : SmoothTameOn (n07aParameterNormalizedGrading hD hT hS) S.sourceGrading
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS => F z.1 z.2))
    (hdecode : ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ u : N07aNormalizedUnknown hD hT hS, ∀ p ∈ annularOpen D,
        (S.height (3 / 4 : ℝ)).decode (F z u).val p =
          divergenceOperator (L.coefficients (liftSectorParameter S C z))
            (heightPairField S u.val.1) p +
            u.val.2 * nuColumnField D S C (liftSectorParameter S C z) p) :
    ScalarInverseProperties D S C L G base ε := by
  let U := sectorNeighborhood S base ε ε
  have hrow (z : StateDirections S × ℝ) (hz : z ∈ U) (f : S.Source) :
      referenceRow D (heightPairField S (G.G (liftSectorParameter S C z) f).1) = 0 :=
    (hLinear.1 _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (href.liftSectorParameter_sector z) f).1
  let V := n07aNormalizedInverse hD hT hS C U G hrow
  have hVcoe (z : StateDirections S × ℝ) (hz : z ∈ U) (f : S.Source) :
      (V z f).val = G.G (liftSectorParameter S C z) f :=
    n07aNormalizedInverse_apply_coe hD hT hS C U G hrow z hz f
  have hleft : ∀ z ∈ U, ∀ u, V z (F z u) = u := by
    intro z hz u
    apply Subtype.ext
    exact (hVcoe z hz (F z u)).trans
      (hLinear.2.1 _ (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
        (href.liftSectorParameter_sector z) u.val.1 u.val.2 (F z u)
        (n07aNormalizedUnknown_row hD hT hS u)
        (fun p hp => (hdecode z hz u p hp).symm))
  have hright : ∀ z ∈ U, ∀ f, F z (V z f) = f := by
    intro z hz f
    apply n07a_source_ext_core hS
    intro p hp
    exact (hdecode z hz (V z f) p hp).trans
      ((congrArg (fun u : HeightPair S × ℝ =>
        divergenceOperator (L.coefficients (liftSectorParameter S C z))
          (heightPairField S u.1) p + u.2 * nuColumnField D S C
            (liftSectorParameter S C z) p) (hVcoe z hz f)).trans
        ((hLinear.1 _ (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
          (href.liftSectorParameter_sector z) f).2 p hp))
  have hVTame : LinearFamilyTame (n07aParameterGrading S)
      (n07aNormalizedGrading hD hT hS) S.sourceGrading U V := by
    let d : ℕ := hLinear.2.2.choose
    let n : ℕ := hLinear.2.2.choose_spec.choose
    have hb := hLinear.2.2.choose_spec.choose_spec
    refine ⟨d, n, ?_⟩
    intro s hs
    let data := hb s hs
    refine ⟨data.choose, data.choose_spec.1, ?_⟩
    intro z hz f
    have hgrade : n07aNormalizedGrading hD hT hS s (V z f) =
        n07aOutputGrading S s (G.G (liftSectorParameter S C z) f) :=
      (n07aNormalizedGrading_apply hD hT hS s (V z f)).trans
        (congrArg (fun u : HeightPair S × ℝ => n07aOutputGrading S s u) (hVcoe z hz f))
    exact hgrade.le.trans (data.choose_spec.2 z hz f)
  have hVcont := n07a_inverseFamily_continuousOn_of_linearFamilyTame
    (n07aParameterGrading_withSeminorms S)
    (n07aNormalizedGrading_withSeminorms hD hT hS)
    (n07aSourceGrading_withSeminorms S)
    (n07aNormalizedGrading_monotone hD hT hS)
    (fun z => (F z).toLinearMap) V hF.choose.continuousOn hleft hright hVTame
  have hsmooth := n07a_normalizedInverse_smoothTame hD hT hS
    (n07a_sectorNeighborhood_isOpen S base ε ε) F V hF hleft hright hVcont hVTame
  refine ⟨hLinear.1, hLinear.2.1, hLinear.2.2, ?_⟩
  exact smoothTameOn_congr hsmooth (fun z hz => hVcoe z.1 hz.1 z.2)

end ContinuousFlexibility.Analysis
