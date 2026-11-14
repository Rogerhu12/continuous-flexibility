module

public import ContinuousFlexibility.Analysis.N06MorseJoinFloor
public import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# A physical two-root lower bound on every positive Morse gap

The endpoints are the actual right turn of the departure model and the
actual left turn of the arrival model, in increasing physical radius.
The entire interval consists of the departure cap, the original join,
and the arrival cap. Their proved physical estimates combine into one
coefficient-power lower bound times the product of the two distances.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n06MorsePositiveLeft (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  let i := if side then n else n + 1
  T.radius side i (morseRightTurn (morseChainA T i) (morseChainB T i))

def n06MorsePositiveRight (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  let i := if side then n + 1 else n
  T.radius side i (morseLeftTurn (morseChainA T i) (morseChainB T i))

/-- The physical orientation fixes the departure and arrival indices.
All four dividing points lie in their actual order inside the annulus. -/
theorem n06_morsePositive_gap_geometry
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    D.a < n06MorsePositiveLeft T side n ∧
      n06MorsePositiveLeft T side n < T.joinLeft side n ∧
      T.joinLeft side n < T.joinRight side n ∧
      T.joinRight side n < n06MorsePositiveRight T side n ∧
      n06MorsePositiveRight T side n < D.b := by
  let d : ℕ := if side then n else n + 1
  let a : ℕ := if side then n + 1 else n
  have hd : T.index ≤ d := by
    cases side
    · exact hn.trans (Nat.le_succ n)
    · exact hn
  have ha : T.index ≤ a := by
    cases side
    · exact hn
    · exact hn.trans (Nat.le_succ n)
  have hj := hreal.join_data side n hn
  have hjL : T.joinLeft side n = T.radius side d (T.rightX side d) := by
    cases side <;> exact hj.2.1
  have hjR : T.joinRight side n = T.radius side a (T.leftX side a) := by
    cases side <;> exact hj.2.2.1
  obtain ⟨hdL, hdLR, hdR⟩ := morseRealization_turns_retained hreal side hd
  obtain ⟨haL, haLR, haR⟩ := morseRealization_turns_retained hreal side ha
  have hdroot : morseRightTurn (morseChainA T d) (morseChainB T d) ∈
      Icc (T.leftX side d) (T.rightX side d) := ⟨(hdL.trans hdLR).le, hdR.le⟩
  have haroot : morseLeftTurn (morseChainA T a) (morseChainB T a) ∈
      Icc (T.leftX side a) (T.rightX side a) := ⟨haL.le, (haLR.trans haR).le⟩
  have hdcore := hreal.radius_mem_core side d hd _ hdroot
  have hacore := hreal.radius_mem_core side a ha _ haroot
  have hdend : T.rightX side d ∈ Icc (T.leftX side d) (T.rightX side d) :=
    ⟨(hdL.trans (hdLR.trans hdR)).le, le_rfl⟩
  have haend : T.leftX side a ∈ Icc (T.leftX side a) (T.rightX side a) :=
    ⟨le_rfl, (haL.trans (haLR.trans haR)).le⟩
  have hbefore := hreal.radius_strictMonoOn side d hd hdroot hdend hdR
  have hafter := hreal.radius_strictMonoOn side a ha haend haroot haL
  change D.a < T.radius side d _ ∧ T.radius side d _ < T.joinLeft side n ∧
    T.joinLeft side n < T.joinRight side n ∧
    T.joinRight side n < T.radius side a _ ∧ T.radius side a _ < D.b
  exact ⟨hdcore.1, hjL.symm ▸ hbefore, hj.1, hjR.symm ▸ hafter, hacore.2⟩

/-- The already proved model-cap estimate is an estimate at every
physical radius in the two cap intervals. The intermediate value theorem
uses the original smooth radius map, without an assumed inverse. -/
theorem n06_morseRealization_positive_cap_physical_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (side : Bool) (n : ℕ), T.index ≤ n →
      (∀ r ∈ Icc (T.radius side n
          (morseRightTurn (morseChainA T n) (morseChainB T n)))
        (T.radius side n (T.rightX side n)),
        c * radialE n ^ (-12 : ℝ) *
            (r - T.radius side n (morseRightTurn (morseChainA T n) (morseChainB T n))) ≤
          deriv D.w r / r) ∧
      (∀ r ∈ Icc (T.radius side n (T.leftX side n))
        (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n))),
        c * radialE n ^ (-12 : ℝ) *
            (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)) - r) ≤
          deriv D.w r / r) := by
  obtain ⟨c, hc, hcap⟩ := n06_morseRealization_positive_cap_distance_lower hreal hσ
  refine ⟨c, hc, ?_⟩
  intro side n hn
  obtain ⟨hl, hlr, hh⟩ := morseRealization_turns_retained hreal side hn
  have hR : Continuous (T.radius side n) := (hreal.radius_smooth side n hn).continuous
  constructor
  · intro r hr
    obtain ⟨x, hx, hxr⟩ := intermediate_value_Icc hh.le hR.continuousOn hr
    have hfull : x ∈ Icc (T.leftX side n) (T.rightX side n) :=
      ⟨(hl.trans hlr).le.trans hx.1, hx.2⟩
    have ht : 0 ≤ x - morseRightTurn (morseChainA T n) (morseChainB T n) :=
      sub_nonneg.mpr hx.1
    have he : n06MorseOuterPoint (morseChainA T n) (morseChainB T n) true
        (x - morseRightTurn (morseChainA T n) (morseChainB T n)) = x := by
      simp only [n06MorseOuterPoint, n06MorseOuterRoot, ↓reduceIte]
      ring
    have hx' : n06MorseOuterPoint (morseChainA T n) (morseChainB T n) true
        (x - morseRightTurn (morseChainA T n) (morseChainB T n)) ∈
        Icc (T.leftX side n) (T.rightX side n) := by rwa [he]
    have hc' := hcap side n hn true
      (x - morseRightTurn (morseChainA T n) (morseChainB T n)) ht hx'
    simpa only [he, n06MorseOuterRoot, ↓reduceIte, hxr,
      abs_of_nonneg (sub_nonneg.mpr hr.1)] using hc'
  · intro r hr
    obtain ⟨x, hx, hxr⟩ := intermediate_value_Icc hl.le hR.continuousOn hr
    have hfull : x ∈ Icc (T.leftX side n) (T.rightX side n) :=
      ⟨hx.1, hx.2.trans (hlr.trans hh).le⟩
    have ht : 0 ≤ morseLeftTurn (morseChainA T n) (morseChainB T n) - x :=
      sub_nonneg.mpr hx.2
    have he : n06MorseOuterPoint (morseChainA T n) (morseChainB T n) false
        (morseLeftTurn (morseChainA T n) (morseChainB T n) - x) = x := by
      simp only [n06MorseOuterPoint, n06MorseOuterRoot, Bool.false_eq_true, ↓reduceIte]
      ring
    have hx' : n06MorseOuterPoint (morseChainA T n) (morseChainB T n) false
        (morseLeftTurn (morseChainA T n) (morseChainB T n) - x) ∈
        Icc (T.leftX side n) (T.rightX side n) := by rwa [he]
    have hc' := hcap side n hn false
      (morseLeftTurn (morseChainA T n) (morseChainB T n) - x) ht hx'
    simpa only [he, n06MorseOuterRoot, Bool.false_eq_true, ↓reduceIte, hxr,
      abs_of_nonpos (sub_nonpos.mpr hr.2), neg_sub] using hc'

/-- Uniform two-root product lower bounds for the same actual physical
profile on all positive gaps between adjacent retained models. -/
theorem n06_morseRealization_positive_gap_product_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
      ∀ (side : Bool) (n : ℕ), T.index ≤ n →
        ∀ r ∈ Icc (n06MorsePositiveLeft T side n) (n06MorsePositiveRight T side n),
          c * radialE (n + 1) ^ (-A) *
              (r - n06MorsePositiveLeft T side n) *
              (n06MorsePositiveRight T side n - r) ≤ deriv D.w r / r := by
  obtain ⟨ccap, hccap, hcap⟩ := n06_morseRealization_positive_cap_physical_bounds hreal hσ
  let L : ℝ := max 1 (D.b - D.a)
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  have hspan : D.b - D.a ≤ L := le_max_right _ _
  have hbp : 0 < D.b := hreal.geometry.1.trans hreal.geometry.2.1
  let cjoin : ℝ := 2 / (C 0 * D.b ^ 2)
  have hcjoin : 0 < cjoin := div_pos (by norm_num)
    (mul_pos (hreal.constants_pos 0) (sq_pos_of_pos hbp))
  let c : ℝ := min (ccap / L) (cjoin / L ^ 2)
  have hc : 0 < c := lt_min (div_pos hccap hL) (div_pos hcjoin (sq_pos_of_pos hL))
  let A : ℝ := max 12 (C 0)
  have hA : 0 < A := (by norm_num : (0 : ℝ) < 12).trans_le (le_max_left _ _)
  have hcL : c * L ≤ ccap := (le_div_iff₀ hL).mp (min_le_left _ _)
  have hcL2 : c * L ^ 2 ≤ cjoin := (le_div_iff₀ (sq_pos_of_pos hL)).mp (min_le_right _ _)
  refine ⟨c, A, hc, hA, ?_⟩
  intro side n hn r hr
  let d : ℕ := if side then n else n + 1
  let a : ℕ := if side then n + 1 else n
  let l : ℝ := n06MorsePositiveLeft T side n
  let u : ℝ := n06MorsePositiveRight T side n
  let p : ℝ := radialE (n + 1) ^ (-A)
  have hp : 0 ≤ p := Real.rpow_nonneg (exp_pos _).le _
  have hd : T.index ≤ d := by
    cases side
    · exact hn.trans (Nat.le_succ n)
    · exact hn
  have ha : T.index ≤ a := by
    cases side
    · exact hn
    · exact hn.trans (Nat.le_succ n)
  have hdN : d ≤ n + 1 := by
    cases side
    · exact le_rfl
    · exact Nat.le_succ n
  have haN : a ≤ n + 1 := by
    cases side
    · exact Nat.le_succ n
    · exact le_rfl
  have hp_le (k : ℕ) (hk : k ≤ n + 1) (t : ℝ) (ht : 0 ≤ t) (htA : t ≤ A) :
      p ≤ radialE k ^ (-t) := by
    have hE : 1 ≤ radialE (n + 1) := one_le_exp_iff.mpr (radialQ_nonneg _)
    have hmono : radialE k ≤ radialE (n + 1) := exp_le_exp.mpr (radialQ_monotone hk)
    exact (Real.rpow_le_rpow_of_exponent_le hE (neg_le_neg htA)).trans
      (Real.rpow_le_rpow_of_nonpos (exp_pos _) hmono (neg_nonpos.mpr ht))
  have hpD : p ≤ radialE d ^ (-12 : ℝ) := hp_le d hdN 12 (by norm_num) (le_max_left _ _)
  have hpA : p ≤ radialE a ^ (-12 : ℝ) := hp_le a haN 12 (by norm_num) (le_max_left _ _)
  have hpJ : p ≤ radialE n ^ (-C 0) :=
    hp_le n (Nat.le_succ n) (C 0) (hreal.constants_pos 0).le (le_max_right _ _)
  have hgeom := n06_morsePositive_gap_geometry hreal side hn
  have hla : D.a < l := hgeom.1
  have hub : u < D.b := hgeom.2.2.2.2
  have hrl : 0 ≤ r - l := sub_nonneg.mpr hr.1
  have hur : 0 ≤ u - r := sub_nonneg.mpr hr.2
  have hrlL : r - l ≤ L := by
    have hh : r - l ≤ D.b - D.a := by linarith only [hr.2, hla, hub]
    exact hh.trans hspan
  have hurL : u - r ≤ L := by
    have hh : u - r ≤ D.b - D.a := by linarith only [hr.1, hla, hub]
    exact hh.trans hspan
  have hj := hreal.join_data side n hn
  have hjL : T.joinLeft side n = T.radius side d (T.rightX side d) := by
    cases side <;> exact hj.2.1
  have hjR : T.joinRight side n = T.radius side a (T.leftX side a) := by
    cases side <;> exact hj.2.2.1
  change c * p * (r - l) * (u - r) ≤ deriv D.w r / r
  by_cases hleft : r ≤ T.joinLeft side n
  · have hcapr : r ∈ Icc (T.radius side d
        (morseRightTurn (morseChainA T d) (morseChainB T d)))
        (T.radius side d (T.rightX side d)) := ⟨hr.1, hjL ▸ hleft⟩
    have hbound : ccap * radialE d ^ (-12 : ℝ) * (r - l) ≤ deriv D.w r / r :=
      (hcap side d hd).1 r hcapr
    have hcoef : c * (u - r) ≤ ccap :=
      (mul_le_mul_of_nonneg_left hurL hc.le).trans hcL
    calc
      c * p * (r - l) * (u - r) = (c * (u - r)) * p * (r - l) := by ring
      _ ≤ ccap * radialE d ^ (-12 : ℝ) * (r - l) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hcoef hpD hp hccap.le) hrl
      _ ≤ deriv D.w r / r := hbound
  · by_cases hright : T.joinRight side n ≤ r
    · have hcapr : r ∈ Icc (T.radius side a (T.leftX side a))
          (T.radius side a (morseLeftTurn (morseChainA T a) (morseChainB T a))) :=
        ⟨hjR ▸ hright, hr.2⟩
      have hbound : ccap * radialE a ^ (-12 : ℝ) * (u - r) ≤ deriv D.w r / r :=
        (hcap side a ha).2 r hcapr
      have hcoef : c * (r - l) ≤ ccap :=
        (mul_le_mul_of_nonneg_left hrlL hc.le).trans hcL
      calc
        c * p * (r - l) * (u - r) = (c * (r - l)) * p * (u - r) := by ring
        _ ≤ ccap * radialE a ^ (-12 : ℝ) * (u - r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hcoef hpA hp hccap.le) hur
        _ ≤ deriv D.w r / r := hbound
    · have hjoin : r ∈ Icc (T.joinLeft side n) (T.joinRight side n) :=
        ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩
      have hcoef : c * ((r - l) * (u - r)) ≤ cjoin := by
        have hdist : (r - l) * (u - r) ≤ L ^ 2 := by
          simpa only [pow_two] using mul_le_mul hrlL hurL hur hL.le
        exact (mul_le_mul_of_nonneg_left hdist hc.le).trans hcL2
      calc
        c * p * (r - l) * (u - r) = (c * ((r - l) * (u - r))) * p := by ring
        _ ≤ cjoin * radialE n ^ (-C 0) := mul_le_mul hcoef hpJ hp hcjoin.le
        _ ≤ deriv D.w r / r := n06_morseRealization_join_coefficient_lower hreal side hn hjoin

end ContinuousFlexibility.Analysis
