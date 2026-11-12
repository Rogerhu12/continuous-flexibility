import ContinuousFlexibility.Statements.Analysis

/-!
# Explicit whole-component exits with ambient-distance caps

Each interior endpoint uses the smaller of one quarter of the component
length and half its distance to the ambient boundary. An ambient endpoint
uses the quarter length; its actual endpoint field is handled by the
separate identity construction. The two exits always leave a nonempty
middle interval, and their choice does not depend on the state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

def positiveMaterialLeftWidth (D : ReferenceData) (l r : ℝ) : ℝ :=
  if l = D.a then (r - l) / 4
  else min ((r - l) / 4) (Statements.endpointDistance D l / 2)

def positiveMaterialRightWidth (D : ReferenceData) (l r : ℝ) : ℝ :=
  if r = D.b then (r - l) / 4
  else min ((r - l) / 4) (Statements.endpointDistance D r / 2)

def positiveMaterialLeftExit (D : ReferenceData) (l r : ℝ) : ℝ :=
  l + positiveMaterialLeftWidth D l r

def positiveMaterialRightExit (D : ReferenceData) (l r : ℝ) : ℝ :=
  r - positiveMaterialRightWidth D l r

theorem positiveMaterialWidths_spec {D : ReferenceData} {l r : ℝ}
    (ha : D.a ≤ l) (hlr : l < r) (hb : r ≤ D.b) :
    0 < positiveMaterialLeftWidth D l r ∧
      0 < positiveMaterialRightWidth D l r ∧
      positiveMaterialLeftWidth D l r ≤ (r - l) / 4 ∧
      positiveMaterialRightWidth D l r ≤ (r - l) / 4 ∧
      (l ≠ D.a → positiveMaterialLeftWidth D l r ≤ Statements.endpointDistance D l / 2) ∧
      (r ≠ D.b → positiveMaterialRightWidth D l r ≤ Statements.endpointDistance D r / 2) := by
  have hgap : 0 < (r - l) / 4 := div_pos (sub_pos.mpr hlr) (by norm_num)
  have hleft : 0 < positiveMaterialLeftWidth D l r ∧
      positiveMaterialLeftWidth D l r ≤ (r - l) / 4 := by
    by_cases h : l = D.a
    · simpa only [positiveMaterialLeftWidth, if_pos h] using
        And.intro hgap (show (r - l) / 4 ≤ (r - l) / 4 from le_rfl)
    · have hc : l ∈ Ioo D.a D.b :=
        ⟨lt_of_le_of_ne ha h.symm, hlr.trans_le hb⟩
      have hd : 0 < Statements.endpointDistance D l :=
        lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
      simpa only [positiveMaterialLeftWidth, if_neg h] using
        And.intro (lt_min hgap (half_pos hd))
          (min_le_left ((r - l) / 4) (Statements.endpointDistance D l / 2))
  have hright : 0 < positiveMaterialRightWidth D l r ∧
      positiveMaterialRightWidth D l r ≤ (r - l) / 4 := by
    by_cases h : r = D.b
    · simpa only [positiveMaterialRightWidth, if_pos h] using
        And.intro hgap (show (r - l) / 4 ≤ (r - l) / 4 from le_rfl)
    · have hc : r ∈ Ioo D.a D.b :=
        ⟨ha.trans_lt hlr, lt_of_le_of_ne hb h⟩
      have hd : 0 < Statements.endpointDistance D r :=
        lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
      simpa only [positiveMaterialRightWidth, if_neg h] using
        And.intro (lt_min hgap (half_pos hd))
          (min_le_left ((r - l) / 4) (Statements.endpointDistance D r / 2))
  refine ⟨hleft.1, hright.1, hleft.2, hright.2, ?_, ?_⟩
  · intro h
    simpa only [positiveMaterialLeftWidth, if_neg h] using
      min_le_right ((r - l) / 4) (Statements.endpointDistance D l / 2)
  · intro h
    simpa only [positiveMaterialRightWidth, if_neg h] using
      min_le_right ((r - l) / 4) (Statements.endpointDistance D r / 2)

theorem positiveMaterialExits_spec {D : ReferenceData} {l r : ℝ}
    (ha : D.a ≤ l) (hlr : l < r) (hb : r ≤ D.b) :
    l < positiveMaterialLeftExit D l r ∧
      positiveMaterialLeftExit D l r < positiveMaterialRightExit D l r ∧
      positiveMaterialRightExit D l r < r ∧
      (l ≠ D.a → positiveMaterialLeftExit D l r - l ≤ Statements.endpointDistance D l / 2) ∧
      (r ≠ D.b → r - positiveMaterialRightExit D l r ≤ Statements.endpointDistance D r / 2) := by
  obtain ⟨hL, hR, hLcap, hRcap, hLdist, hRdist⟩ := positiveMaterialWidths_spec ha hlr hb
  dsimp only [positiveMaterialLeftExit, positiveMaterialRightExit]
  refine ⟨by linarith only [hL], by linarith only [hLcap, hRcap, hlr],
    by linarith only [hR], ?_, ?_⟩
  · intro h
    linarith only [hLdist h]
  · intro h
    linarith only [hRdist h]

end ContinuousFlexibility.Analysis
