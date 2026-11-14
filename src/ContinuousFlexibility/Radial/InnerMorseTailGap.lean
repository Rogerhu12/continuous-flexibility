module

public import ContinuousFlexibility.Radial.InnerMorseTailGeometry
public import ContinuousFlexibility.Radial.MorseRealizedConnectorBounds

/-!
# Complete positive gaps in either actual Morse tail

A gap contains the remaining right cap of its departure model, the
whole realized join, and the remaining left cap of its arrival model.
Departure and arrival are ordered by increasing physical radius, so a
single construction treats both tails. The coercivity constant is
fixed before the frequency and the finite inner truncation are chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

def innerMorseOuterCapStart (A B : ℝ) (right : Bool) : ℝ :=
  if right then innerMorseBufferRightCut A B else morseCellLeftCut

def innerMorseOuterCapEnd (A B : ℝ) (right : Bool) : ℝ :=
  if right then morseRightCapEnd A B (1 / 100) else innerMorseBufferLeftCut

theorem innerMorseOuterCap_order {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (right : Bool) : innerMorseOuterCapStart A B right < innerMorseOuterCapEnd A B right := by
  have hc := innerMorseBuffer_cut_order hB hAB
  cases right with
  | false => simpa only [innerMorseOuterCapStart, innerMorseOuterCapEnd,
      Bool.false_eq_true, ite_false] using hc.1
  | true => simpa only [innerMorseOuterCapStart, innerMorseOuterCapEnd, ite_true] using hc.2.2

theorem innerMorseOuterCap_subset {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hsmall : A ≤ 1 / 1000) (right : Bool) :
    Icc (innerMorseOuterCapStart A B right) (innerMorseOuterCapEnd A B right) ⊆
      innerMorseCapInterval A B right := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hshort := morseCellLeftCut_lt_shortLeftCapCut
  have hlong := innerMorseBuffer_long_fit hA (hsmall.trans (by norm_num))
  have hlog := log_pos (by norm_num : (1 : ℝ) < 4)
  intro x hx
  cases right with
  | false =>
    simp only [innerMorseOuterCapStart, innerMorseOuterCapEnd, innerMorseCapInterval,
      Bool.false_eq_true, ite_false] at hx ⊢
    refine ⟨hx.1, ?_⟩
    dsimp only [innerMorseBufferLeftCut] at hx
    linarith only [hx.2, hshort]
  | true =>
    simp only [innerMorseOuterCapStart, innerMorseOuterCapEnd, innerMorseCapInterval,
      ite_true] at hx ⊢
    refine ⟨?_, hx.2⟩
    dsimp only [innerMorseBufferRightCut] at hx
    linarith only [hx.1, hlong, hlog]

/-- The actual physical remaining cap satisfies the fixed slope bound.
This also covers the two terminal caps at the inner-domain boundary. -/
theorem innerMorseChain_outerCap_logSlope {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {m : ℕ} (hindex : 10 ≤ T.index) (hm : T.index ≤ m)
    (right : Bool) {r : ℝ}
    (hr : r ∈ Icc
      (T.radius side m (innerMorseOuterCapStart (morseChainA T m) (morseChainB T m) right))
      (T.radius side m (innerMorseOuterCapEnd (morseChainA T m) (morseChainB T m) right))) :
    innerMorseTailSlope ≤ r * deriv D.w r / D.w r := by
  obtain ⟨hB, hAB, _, _, _, _, _⟩ := h.retained_data side m hm
  obtain ⟨hl, hh⟩ := innerMorseChain_retained_endpoints h side hm
  have hsub := innerMorseOuterCap_subset hB hAB (innerMorseChain_parameter_tiny h hindex hm) right
  have hwhole : Icc
      (innerMorseOuterCapStart (morseChainA T m) (morseChainB T m) right)
      (innerMorseOuterCapEnd (morseChainA T m) (morseChainB T m) right) ⊆
      Icc (T.leftX side m) (T.rightX side m) := by
    intro x hx
    simpa only [hl, hh] using innerMorseCapInterval_subset hB hAB right (hsub hx)
  have hinv := morseCellModelCoordinate_right (innerMorseOuterCap_order hB hAB right).le
    (h.radius_smooth side m hm) ((h.radius_strictMonoOn side m hm).mono hwhole) hr
  have hslope := innerMorseChain_cap_logSlope h side hindex hm right (hsub hinv.1)
  simpa only [hinv.2] using hslope

def innerMorseTailDeparture (side : Bool) (k : ℕ) : ℕ := if side then k else k + 1

def innerMorseTailArrival (side : Bool) (k : ℕ) : ℕ := if side then k + 1 else k

def innerMorseTailGapLeft (T : MorseChainData) (side : Bool) (k : ℕ) : ℝ :=
  innerMorseChainCut T side (innerMorseTailDeparture side k) 1

def innerMorseTailGapRight (T : MorseChainData) (side : Bool) (k : ℕ) : ℝ :=
  innerMorseChainCut T side (innerMorseTailArrival side k) 0

/-- The complete gap has strictly ordered cuts and lies in the actual
positive radial core; no connector width estimate is needed. -/
theorem innerMorseTailGap_geometry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {k : ℕ} (hk : T.index ≤ k) :
    innerMorseTailGapLeft T side k < T.joinLeft side k ∧
      T.joinLeft side k < T.joinRight side k ∧
      T.joinRight side k < innerMorseTailGapRight T side k ∧
      Icc (innerMorseTailGapLeft T side k) (innerMorseTailGapRight T side k) ⊆ radialCore D := by
  have he := morseRealizedJoin_endpoints h side k hk
  rcases he with ⟨hd, ha, _, hl, hr, _⟩
  have hdep := innerMorseChainCut_geometry h side hd
  have harr := innerMorseChainCut_geometry h side ha
  refine ⟨hdep.2.2.1.trans_eq hl.symm, (h.join_data side k hk).1,
    hr.trans_lt harr.1, ?_⟩
  intro r hr'
  exact ⟨(hdep.2.2.2 1).1.trans_le hr'.1, hr'.2.trans_lt (harr.2.2.2 0).2⟩

/-- The given join slope is valid on the closed join, not only in its
open interior. This supplies the exact join coercivity constant 1/6. -/
theorem innerMorseChain_join_logSlope {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {k : ℕ} (hk : T.index ≤ k) :
    ∀ r ∈ Icc (T.joinLeft side k) (T.joinRight side k),
      2 ≤ r * deriv D.w r / D.w r := by
  have hg := innerMorseTailGap_geometry h side hk
  have hc : Icc (T.joinLeft side k) (T.joinRight side k) ⊆ radialCore D :=
    (Icc_subset_Icc hg.1.le hg.2.2.1.le).trans hg.2.2.2
  apply innerPositiveGap_closed_slope hg.2.1 h.geometry.2.2.1.1
    (fun r hr => h.geometry.2.2.2.2.1 r (hc hr))
  intro r hr
  have hrp : 0 < r := h.geometry.1.trans (hc (Ioo_subset_Icc_self hr)).1
  have hslope := (h.join_data side k hk).2.2.2.2 r hr
  calc
    2 = r * (2 / r) := by field_simp [hrp.ne']
    _ ≤ r * (deriv D.w r / D.w r) := mul_le_mul_of_nonneg_left hslope hrp.le
    _ = r * deriv D.w r / D.w r := by ring

/-- Every complete actual tail gap, including both cap remnants and
the full positive connector, has the same fixed logarithmic slope. -/
theorem innerMorseTailGap_logSlope {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {k : ℕ} (hindex : 10 ≤ T.index) (hk : T.index ≤ k) :
    ∀ r ∈ Icc (innerMorseTailGapLeft T side k) (innerMorseTailGapRight T side k),
      innerMorseTailSlope ≤ r * deriv D.w r / D.w r := by
  have he := morseRealizedJoin_endpoints h side k hk
  rcases he with ⟨hd, ha, _, hl, hr, _⟩
  obtain ⟨_, hdend⟩ := innerMorseChain_retained_endpoints h side hd
  obtain ⟨hastart, _⟩ := innerMorseChain_retained_endpoints h side ha
  intro r hrg
  by_cases hleft : r ≤ T.joinLeft side k
  · apply innerMorseChain_outerCap_logSlope h side hindex hd true
    refine ⟨?_, ?_⟩
    · simpa only [innerMorseOuterCapStart, ite_true, innerMorseTailGapLeft,
        innerMorseTailDeparture, innerMorseChainCut_one] using hrg.1
    · simpa only [innerMorseOuterCapEnd, ite_true, ← hdend, ← hl] using hleft
  by_cases hright : T.joinRight side k ≤ r
  · apply innerMorseChain_outerCap_logSlope h side hindex ha false
    refine ⟨?_, ?_⟩
    · simpa only [innerMorseOuterCapStart, Bool.false_eq_true, ite_false, ← hastart, ← hr]
        using hright
    · simpa only [innerMorseOuterCapEnd, Bool.false_eq_true, ite_false,
        innerMorseTailGapRight, innerMorseTailArrival, innerMorseChainCut_zero] using hrg.2
  exact innerMorseTailSlope_le_two.trans (innerMorseChain_join_logSlope h side hk r
    ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩)

/-- The manuscript's physical L² coercivity on the entire gap follows
from its constructed slope. The constant has no n- or j-dependence. -/
theorem innerMorseTailGap_coercive {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {k : ℕ} (hindex : 10 ≤ T.index) (hk : T.index ≤ k)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (j : ℝ) :
    (innerMorseTailSlope / 12) * j ^ 2 * innerRadialGapMass D.w u
      (innerMorseTailGapLeft T side k) (innerMorseTailGapRight T side k) ≤
      innerRadialGapEnergy D.w u j
        (innerMorseTailGapLeft T side k) (innerMorseTailGapRight T side k) := by
  have hg := innerMorseTailGap_geometry h side hk
  have hab := (hg.1.trans (hg.2.1.trans hg.2.2.1)).le
  have ha := h.geometry.1.trans (hg.2.2.2 (left_mem_Icc.mpr hab)).1
  exact innerRadialGap_coercive hab ha h.geometry.2.2.1.1 hu
    (fun r hr => h.geometry.2.2.2.2.1 r (hg.2.2.2 hr))
    (innerMorseTailGap_logSlope h side hindex hk) j

end ContinuousFlexibility.Radial
