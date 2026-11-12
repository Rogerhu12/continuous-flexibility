import ContinuousFlexibility.Analysis.N04RealizationAtomJets
import ContinuousFlexibility.Analysis.N04RealizationPrimitiveNormalization
import ContinuousFlexibility.Analysis.CanonicalCoordinateCompletion
import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# Completing the quantitative coordinate clause from its primitive jets

Potential and the three positive divided fields are already actual atoms of
the primitive construction. Their bounds therefore follow from the same
reference and current jet certificates. Negative-piece divided fields and
off-sector potentials are normalized only where the canonical identities do
not use them. No final estimate is assumed for these fields.

The resulting loss can be chosen above any previously fixed loss, while the
coordinate data and state neighborhood remain the same.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
  CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

private theorem n04Realization_dividedComponent_unit_identity
    (z : AnnularState S × ℝ) (m : ℕ) (hm : K.positive m = true) (i : Fin 3) :
    EqOn ((canonicalCoefficientComponent i (K.dividedDifference z m)) ∘
        canonicalUnitPoint K m)
      (atom D T S C L K z m
        (if i = 0 then .dividedA else if i = 1 then .dividedB else .dividedC))
      unitStrip := by
  intro p _
  fin_cases i <;> simp [Function.comp_apply, canonicalCoefficientComponent, atom, hm]

private theorem n04Realization_sectorJetBound_fixed_order
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    {d s : ℕ} {B : ℝ} (hB : 0 < B)
    (hb : N04RealizationCanonicalAtomBoundAtOrder D T S C L K base d ε s B) :
    ∃ Q : ℝ, 0 < Q ∧ SectorCanonicalJetBoundAtOrder T S C K base d ε s Q := by
  obtain ⟨Q, hQ, hcost⟩ := coefficientEnvelope_pack (4 * B) B
  refine ⟨Q, hQ, fun z hz hs m p hp i j hij => ?_⟩
  let E : ℝ := T.E0 (T.sample (K.cell m))
  let rho : ℝ := 1 + stateGrading S (s + d) (z.1 - C.referenceState) + |z.2|
  have hrho : 0 ≤ rho :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  have hpotential : |mixedDerivative i j (K.potential z m) p| ≤ B * E ^ B * rho :=
    hb z hz hs m .potential (K.potential z m) (fun _ _ => rfl) i j hij p hp
  have hweight : 0 ≤ B * E ^ B * rho :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hfloor m)) _)) hrho
  have hfinal : (4 * B) * E ^ B * rho ≤ Q * E ^ Q * rho :=
    mul_le_mul_of_nonneg_right (hcost E (hfloor m)) hrho
  by_cases hm : K.positive m = true
  · have hdiv (v : Fin 3) :
        |mixedDerivative i j (canonicalCoefficientComponent v (K.dividedDifference z m)) p| ≤
          B * E ^ B * rho :=
      hb z hz hs m
        (if v = 0 then .dividedA else if v = 1 then .dividedB else .dividedC)
        (canonicalCoefficientComponent v (K.dividedDifference z m))
        (n04Realization_dividedComponent_unit_identity z m hm v) i j hij p hp
    have ha : |mixedDerivative i j (K.dividedDifference z m).a p| ≤ B * E ^ B * rho := by
      simpa [canonicalCoefficientComponent] using hdiv 0
    have hb' : |mixedDerivative i j (K.dividedDifference z m).b p| ≤ B * E ^ B * rho := by
      simpa [canonicalCoefficientComponent] using hdiv 1
    have hc : |mixedDerivative i j (K.dividedDifference z m).c p| ≤ B * E ^ B * rho := by
      simpa [canonicalCoefficientComponent] using hdiv 2
    simp only [hm, ite_true]
    apply le_trans _ hfinal
    linarith only [hpotential, ha, hb', hc]
  · simp only [hm, Bool.false_eq_true, ite_false, add_zero]
    apply le_trans _ hfinal
    linarith only [hpotential, hweight]

/-- The exact sector estimate is a consequence of the two required
primitive jet certificates, at one fixed loss and on their same neighborhood. -/
theorem n04Realization_sectorCanonicalJetBounds_of_primitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hlen : ∀ m, K.left m < K.right m)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ d : ℕ, SectorCanonicalJetBounds T S C K base d ε := by
  obtain ⟨d, hbounds⟩ :=
    n04Realization_canonicalAtom_jet_bounds hD hT hrefState href hcur hlen hfloor
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hbounds s
  exact n04Realization_sectorJetBound_fixed_order hfloor hB hb

/-- Increasing the fixed loss leaves the atlas and neighborhood intact. -/
theorem n04Realization_sectorJetBounds_loss_mono
    (hE0 : ∀ m, 0 ≤ T.E0 (T.sample (K.cell m)))
    {d d' : ℕ} (hdd : d ≤ d')
    (h : SectorCanonicalJetBounds T S C K base d ε) :
    SectorCanonicalJetBounds T S C K base d' ε := by
  intro s
  obtain ⟨B, hB, hb⟩ := h s
  refine ⟨B, hB, fun z hz hs m p hp i j hij => ?_⟩
  have hgrade := stateGrading_monotone S (Nat.add_le_add_left hdd s)
    (z.1 - C.referenceState)
  have hE : 0 ≤ T.E0 (T.sample (K.cell m)) ^ B := Real.rpow_nonneg (hE0 m) _
  exact (hb z hz hs m p hp i j hij).trans
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hgrade) le_rfl)
      (mul_nonneg hB.le hE))

/-- The quantitative N04 clause and source pairing follow from the actual
qualitative parts and the same primitive jets. The caller may retain any
previous loss by choosing this output above it. -/
theorem n04Realization_exists_normalized_properties_of_primitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) (previousLoss : ℕ) :
    ∃ d : ℕ, previousLoss ≤ d ∧
      N04Properties D T S C L (normalizedCanonicalData S K) base d ε := by
  obtain ⟨d, hbound⟩ := n04Realization_sectorCanonicalJetBounds_of_primitive
    hD hT hrefState href hcur (fun m => (hA.referenceBounds m).2.1) hfloor
  exact ⟨max previousLoss d, le_max_left _ _,
    n04Properties_normalized_of_sector_jetBounds hT hD hA hB
      (n04Realization_sectorJetBounds_loss_mono (fun m => zero_le_one.trans (hfloor m))
        (le_max_right previousLoss d) hbound)⟩

end ContinuousFlexibility.Analysis
