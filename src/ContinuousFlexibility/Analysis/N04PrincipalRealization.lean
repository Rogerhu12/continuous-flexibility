import ContinuousFlexibility.Analysis.N04PrincipalAuxiliaryQuantifiers
import ContinuousFlexibility.Analysis.N04PrincipalAssemblePairs
import ContinuousFlexibility.Analysis.N04PrincipalNegativeHeightPairs
import ContinuousFlexibility.Analysis.N04PrincipalCorePeriodicity

/-!
# The principal realization obligation

One reciprocal-height neighborhood, one positive determinant neighborhood,
and one principal-A neighborhood suffice for all eight actual atoms.
Their finite maximum is taken before all jet orders. Auxiliary-column
independence then restores the quantifier order of the frozen statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

theorem n04Principal_fixedAuxiliary : N04PrincipalFixedAuxiliaryObligation := by
  intro G b ε h η hg hf href
  have hheight := G.n04PrincipalNegative_height_inverse_pairs h η href hg
  let bH : ℕ := hheight.choose
  have hbH : b ≤ bH := hheight.choose_spec.1
  let εH : ℝ := hheight.choose_spec.2.choose
  have hheightinfo := hheight.choose_spec.2.choose_spec
  have hεH : 0 < εH := hheightinfo.1
  have hεHε : εH ≤ ε := hheightinfo.2.1
  have hH := G.admissible_mono h hbH hεH hεHε
  have hgH := G.geometryData_mono η hg (fun _ ht => ht) hbH hεHε
  have hfH := G.fieldData_mono η hf hbH hεHε
  have hcore := G.n04Principal_core_pairs hH η href hgH hfH
    hheightinfo.2.2.2.1 hheightinfo.2.2.2.2
  let bC : ℕ := hcore.choose
  have hbC : bH ≤ bC := hcore.choose_spec.1
  let εC : ℝ := hcore.choose_spec.2.choose
  have hcoreinfo := hcore.choose_spec.2.choose_spec
  have hεC : 0 < εC := hcoreinfo.1
  have hεCεH : εC ≤ εH := hcoreinfo.2.1
  have hC := G.admissible_mono hH hbC hεC hεCεH
  have hgC := G.geometryData_mono η hgH (fun _ ht => ht) hbC hεCεH
  have hfC := G.fieldData_mono η hfH hbC hεCεH
  have hperiodic := G.n04Principal_core_periodic hC η href hgC hfC hcoreinfo.2.2
  have hdata := G.n04Principal_data_from_core_pairs hC η href hcoreinfo.2.2 hperiodic
  let b' : ℕ := hdata.choose
  have hb' : bC ≤ b' := hdata.choose_spec.1
  let ε' : ℝ := hdata.choose_spec.2.choose
  have hdatainfo := hdata.choose_spec.2.choose_spec
  exact ⟨b', ε', (hbH.trans hbC).trans hb', hdatainfo.1,
    (hdatainfo.2.1.trans hεCεH).trans hεHε, hdatainfo.2.2⟩

theorem n04Principal_realization : N04RealizationPrincipalObligation :=
  n04Principal_obligation_of_fixedAuxiliary n04Principal_fixedAuxiliary

end ContinuousFlexibility.Analysis
