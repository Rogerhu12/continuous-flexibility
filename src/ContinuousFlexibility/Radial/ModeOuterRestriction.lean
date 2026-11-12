import ContinuousFlexibility.Radial.ModeRegionWeakEquation

/-!
# Actual exterior restrictions of modal weak solutions

These are statements about the constructed indicator operators. In particular,
no local inverse or matching realization is assumed. The exterior extension
keeps the two cut values and is zero on the open inner interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem modeOuterSource_testIntegral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (l h : ℝ) (F : RadialModePair D)
    {ψ : ℝ → ℝ}
    (hsupp : Function.support ψ ⊆ Ioo D.a l ∪ Ioo h D.b) :
    (∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * (modeOuterSource D l h F).1 r * ψ r) =
      ∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r := by
  apply matchingInterval_congr_ae hD
  filter_upwards [(modeRegionSources_spec D l h F).2.2.2] with r hr
  by_cases hi : r ∈ Ioo l h
  · have hz : ψ r = 0 := by
      by_contra hz
      rcases hsupp hz with hL | hR
      · exact lt_asymm hi.1 hL.2
      · exact lt_asymm hi.2 hR.1
    simp only [hz, mul_zero]
  · rw [hr, if_neg hi]

theorem modeLocalEquation_modeOuterSource_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {l h : ℝ} {U F : RadialModePair D} :
    ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b) U (modeOuterSource D l h F) ↔
      ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b) U F := by
  constructor
  · intro hEq ψ hψ hc hs
    have he := hEq ψ hψ hc hs
    rwa [modeOuterSource_testIntegral hD l h F hs] at he
  · intro hEq ψ hψ hc hs
    rw [modeOuterSource_testIntegral hD l h F hs]
    exact hEq ψ hψ hc hs

/-- A zero-scalar solution on the two open outer components may be
restricted by the actual exterior indicator. -/
theorem modeLocalEquation_modeOuterRestriction {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {l h : ℝ} {U F : RadialModePair D}
    (hscalar : U.2 = 0)
    (hEq : ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b) U F) :
    ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b)
      (modeOuterSource D l h U) (modeOuterSource D l h F) := by
  apply (modeLocalEquation_modeOuterSource_iff hD).mpr
  intro ψ hψ hc hsupp
  have heq := hEq ψ hψ hc hsupp
  have htsupp : tsupport ψ ⊆ Iic l ∪ Ici h := by
    apply closure_minimal ?_ (isClosed_Iic.union isClosed_Ici)
    intro r hr
    rcases hsupp hr with hL | hR
    · exact Or.inl hL.2.le
    · exact Or.inr hR.1.le
  have hi :
      (∫ r in D.a..D.b,
        (modeOuterSource D l h U).1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
      ∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
    apply matchingInterval_congr_ae hD
    filter_upwards [(modeRegionSources_spec D l h U).2.2.2] with r hr
    by_cases hin : r ∈ Ioo l h
    · have hout : r ∉ Iic l ∪ Ici h := by
        rintro (hL | hR)
        · exact (not_le.mpr hin.1) hL
        · exact (not_le.mpr hin.2) hR
      have hz := matching_radialJacobi_eq_zero_of_notMem_tsupport
        (fun ht => hout (htsupp ht)) D.w ((j : ℝ) ^ 2)
      simp only [hz, mul_zero]
    · rw [hr, if_neg hin]
  rw [hi, (modeRegionSources_spec D l h U).2.1]
  simpa only [hscalar, zero_mul, sub_zero] using heq

/-- Preserve the exterior cut traces while extending by zero inside. -/
def modeOuterExtension (l h : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  ((Ioo l h)ᶜ).indicator u

theorem modeOuterExtension_eqOn {l h : ℝ} (u : ℝ → ℝ) :
    EqOn (modeOuterExtension l h u) u (Ioo l h)ᶜ := by
  intro r hr
  exact Set.indicator_of_mem hr u

theorem modeOuterExtension_zero_inside {l h r : ℝ} (u : ℝ → ℝ)
    (hr : r ∈ Ioo l h) : modeOuterExtension l h u r = 0 :=
  Set.indicator_of_notMem (not_not.mpr hr) u

theorem modeOuterExtension_eqOn_oneSided {a b l h : ℝ} (u : ℝ → ℝ) :
    EqOn (modeOuterExtension l h u) u (Ioc a l ∪ Ico h b) := by
  intro r hr
  apply modeOuterExtension_eqOn u
  intro hi
  rcases hr with hL | hR
  · exact (not_le.mpr hi.1) hL.2
  · exact (not_le.mpr hi.2) hR.1

theorem modeOuterExtension_contDiffOn {a b l h : ℝ} {u : ℝ → ℝ} {n : ℕ∞ω}
    (hu : ContDiffOn ℝ n u (Ioc a l ∪ Ico h b)) :
    ContDiffOn ℝ n (modeOuterExtension l h u) (Ioc a l ∪ Ico h b) :=
  hu.congr (modeOuterExtension_eqOn_oneSided u)

theorem modeOuterSource_extension_ae {D : ReferenceData} (l h : ℝ)
    (F : RadialModePair D) {u : ℝ → ℝ}
    (hu : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    ((modeOuterSource D l h F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      modeOuterExtension l h u := by
  classical
  filter_upwards [(modeRegionSources_spec D l h F).2.2.2, hu] with r hs hr
  by_cases hi : r ∈ Ioo l h
  · rw [hs, if_pos hi, modeOuterExtension_zero_inside u hi]
  · rw [hs, if_neg hi, hr]
    exact (modeOuterExtension_eqOn u hi).symm

end ContinuousFlexibility.Radial
