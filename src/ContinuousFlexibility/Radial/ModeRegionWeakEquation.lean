import ContinuousFlexibility.Radial.ModeRegionSources

/-!
# Weak equations for the constructed regional sources

These identities concern the concrete indicator operators. They do not
assume any clause of MatchingLocalRealizations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem modeInnerSource_testIntegral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (l h : ℝ) (F : RadialModePair D)
    {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Ioo l h) :
    (∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * (modeInnerSource D l h F).1 r * ψ r) =
      ∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r := by
  apply matchingInterval_congr_ae hD
  filter_upwards [(modeRegionSources_spec D l h F).2.2.1] with r hr
  by_cases hi : r ∈ Ioo l h
  · rw [hr, if_pos hi]
  · have hz : ψ r = 0 := by
      by_contra hz
      exact hi (hsupp hz)
    simp only [hz, mul_zero]

theorem modeLocalEquation_modeInnerSource_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {l h : ℝ} {U F : RadialModePair D} :
    ModeLocalEquation D j (Ioo l h) U (modeInnerSource D l h F) ↔
      ModeLocalEquation D j (Ioo l h) U F := by
  constructor
  · intro hEq ψ hψ hc hs
    have he := hEq ψ hψ hc hs
    rwa [modeInnerSource_testIntegral hD l h F hs] at he
  · intro hEq ψ hψ hc hs
    rw [modeInnerSource_testIntegral hD l h F hs]
    exact hEq ψ hψ hc hs

/-- Restrict the actual unknown, retaining its scalar component. The
possible jumps at the two cuts do not affect tests supported in the
open inner interval; endpoint null sets are handled explicitly. -/
theorem modeLocalEquation_modeInnerRestriction {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {l h : ℝ} {U F : RadialModePair D}
    (hEq : ModeLocalEquation D j (Ioo l h) U F) :
    ModeLocalEquation D j (Ioo l h) (modeInnerSource D l h U)
      (modeInnerSource D l h F) := by
  apply (modeLocalEquation_modeInnerSource_iff hD).mpr
  intro ψ hψ hc hsupp
  have heq := hEq ψ hψ hc hsupp
  have htsupp : tsupport ψ ⊆ Icc l h :=
    closure_minimal (hsupp.trans Ioo_subset_Icc_self) isClosed_Icc
  have hi :
      (∫ r in D.a..D.b,
        (modeInnerSource D l h U).1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
      ∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
    apply matchingInterval_congr_ae hD
    filter_upwards [(modeRegionSources_spec D l h U).2.2.1,
      matching_ae_ne hD l, matching_ae_ne hD h] with r hr hL hR
    by_cases hin : r ∈ Ioo l h
    · rw [hr, if_pos hin]
    · have hout : r ∉ Icc l h := by
        intro hx
        exact hin ⟨lt_of_le_of_ne hx.1 hL.symm, lt_of_le_of_ne hx.2 hR⟩
      have hz := matching_radialJacobi_eq_zero_of_notMem_tsupport
        (fun ht => hout (htsupp ht)) D.w ((j : ℝ) ^ 2)
      simp only [hz, mul_zero]
  rw [hi, (modeRegionSources_spec D l h U).1]
  exact heq

/-- The true border row is unchanged by the concrete inner restriction
whenever its actual column is supported between the cuts. -/
theorem modeInnerSource_borderRow {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h : ℝ}
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo l h)
    (U : RadialModePair D) :
    (∫ r in D.a..D.b, referenceColumn D r * (modeInnerSource D l h U).1 r) =
      ∫ r in D.a..D.b, referenceColumn D r * U.1 r := by
  apply matchingInterval_congr_ae hD
  filter_upwards [(modeRegionSources_spec D l h U).2.2.1] with r hr
  by_cases hi : r ∈ Ioo l h
  · rw [hr, if_pos hi]
  · have hz : referenceColumn D r = 0 := by
      by_contra hz
      exact hi (hcolumn hz)
    simp only [hz, zero_mul]

end ContinuousFlexibility.Radial
