import ContinuousFlexibility.Analysis.N06Neighborhood
import ContinuousFlexibility.Analysis.N06RelativeConstruction

/-!
# Choosing the one neighborhood for the relative inverse

A linear smallness estimate in one fixed state seminorm determines a positive
radius and a single low order. All preceding properties and the Neumann inverse
then hold on that same neighborhood and on the source and graph selected by N05.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem n06_exists_on_smaller_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T)
    (hthrough : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (order : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hphysical : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
        (V.forget (3 / 4 : ℝ) 0 b (P z u)))
    (hbound : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ‖n06RelativeOperator P z‖ ≤
        M * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ Relative : RelativeInverseData S K V b B,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
        NonlinearPropertiesThrough06 D T S C R L K V b B Relative base' loss ε' := by
  have hε : 0 < ε := hthrough.1.1.1.1.2.1
  let base' := max base order
  let ε' := min ε (1 / (8 * (M + 1)))
  have hbase : base ≤ base' := le_max_left base order
  have horder : order ≤ base' := le_max_right base order
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hεle : ε' ≤ ε := min_le_left _ _
  have hεM : M * ε' ≤ (1 / 8 : ℝ) := by
    have hden : M + 1 ≠ 0 := ne_of_gt (by linarith)
    calc
      M * ε' ≤ (M + 1) * ε' :=
        mul_le_mul_of_nonneg_right (by linarith) hε'.le
      _ ≤ (M + 1) * (1 / (8 * (M + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      _ = 1 / 8 := by field_simp
  have hU := n06_stateNeighborhood_mono (C := C) hbase hεle
  have hsmall : ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ‖n06RelativeOperator P z‖ < (1 / 2 : ℝ) := by
    intro z hz hsector
    have hs : stateGrading S order (z.1 - C.referenceState) ≤ ε' :=
      (solve_stateGrading_monotone S horder _).trans hz.1.le
    have hq : |z.2| ≤ ε' := hz.2.le
    have hb := (hbound z (hU hz) hsector).trans
      (mul_le_mul_of_nonneg_left (add_le_add hs hq) hM)
    nlinarith only [hb, hεM]
  obtain ⟨Relative, hRelative⟩ := n06_exists_relativeData D T C L base' ε'
    hthrough.2 P hε' (fun z hz => hphysical z (hU hz)) hsmall
  refine ⟨base', ε', Relative, hbase, hε', hεle, ?_⟩
  exact ⟨n06_NonlinearPropertiesThrough05_mono hT hthrough hbase hε' hεle,
    hRelative⟩

end ContinuousFlexibility.Statements
