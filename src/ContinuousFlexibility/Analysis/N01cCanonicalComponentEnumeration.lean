import ContinuousFlexibility.Analysis.N01aNegativeComponentGeometry
import ContinuousFlexibility.Analysis.N01cMorseComponentClassification
import ContinuousFlexibility.Analysis.N01cOpticalCellComparison
import ContinuousFlexibility.Radial.SeedCentralReturn
import ContinuousFlexibility.Radial.MorseChainPartitionData
import ContinuousFlexibility.Radial.MorseSecondModeGeometry

/-!
# Enumerating the actual retained components with their original labels

The central turning interval occupies slot zero.  The two original
Morse chains occupy the same Bool-times-Nat slots as the reference
partition.  A control's actual containing cell may differ from the
model cell, but their shared interior point bounds the index difference.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real
open ContinuousFlexibility.Radial

/-- The concrete two-tail gluing admits the canonical component
enumeration.  Every actual containing-cell choice has bounded additive
index displacement; no weight-sorting permutation is used. -/
theorem exists_n01c_canonical_component_enumeration
    {T : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    {uL uR : ℝ → ℝ} {K : SeedCentralCutoff} {q c d : ℝ}
    (G : SeedGluedPair D c d uL uR K q)
    (hc : c = morseChainSeam T false T.index)
    (hd : d = morseChainSeam T true T.index)
    (hq : 0 < q) (hE : IsAccumulatingProfile E)
    (ha : E.a = G.radiusL * D.a) (hb : E.b = G.radiusR * D.b)
    (hw : E.w = G.profile)
    (hseams : ∀ side n, T.index ≤ n →
      if side then morseChainSeam T side T.index ≤ morseChainSeam T side n
      else morseChainSeam T side n ≤ morseChainSeam T side T.index)
    (hlabels : D.cellIndex = morseTwoTailAt T.index (fun _ k => T.index + k))
    (N : ℕ) (hindex : ∀ m, E.cellIndex m = max (D.cellIndex m) N)
    (hcells : ∀ side m r,
      r ∈ radialTailInterval D side (morseChainSeam T side T.index) →
      r ∈ D.cells m → (if side then G.radiusR else G.radiusL) * r ∈ E.cells m)
    (host : N01aNegativeComponent E → ℕ)
    (hhost : ∀ J, J.interval ⊆ E.cells (host J)) :
    ∃ e : ℕ ≃ N01aNegativeComponent E, ∃ B : ℝ, 0 < B ∧
      ∀ m, |(E.cellIndex (host (e m)) : ℝ) - E.cellIndex m| ≤ B := by
  classical
  subst c
  subst d
  let scale (side : Bool) : ℝ := if side then G.radiusR else G.radiusL
  let height (side : Bool) : ℝ := if side then G.heightR else G.heightL
  have hscale (side : Bool) : 0 < scale side := by
    cases side
    · exact G.radiusL_pos
    · exact G.radiusL_pos.trans_le G.radius_order
  have hheight (side : Bool) : 0 < height side := by
    cases side
    · exact G.heightL_pos
    · exact G.heightR_pos
  let old (side : Bool) (k : ℕ) : N01aNegativeComponent D :=
    ⟨(T.radius side (T.index + k)
        (morseLeftTurn (morseChainA T (T.index + k)) (morseChainB T (T.index + k))),
      T.radius side (T.index + k) (morseChainRightTurn T (T.index + k))),
      (morseRealization_model_return hreal hσ side (Nat.le_add_right _ _)).1⟩
  have hclosed (side : Bool) (k : ℕ) :
      Icc (old side k).left (old side k).right ⊆
        radialTailInterval D side (morseChainSeam T side T.index) := by
    have hn : T.index ≤ T.index + k := Nat.le_add_right _ _
    obtain ⟨hl, hlr, hr⟩ := morseRealization_turns_retained hreal side hn
    have hm := hreal.radius_strictMonoOn side (T.index + k) hn
    have hab := (hreal.2.2.1 side (T.index + k) hn).2.1
    have hleft := hm (left_mem_Icc.mpr hab.le) ⟨hl.le, hlr.le.trans hr.le⟩ hl
    have hright := hm ⟨hl.le.trans hlr.le, hr.le⟩ (right_mem_Icc.mpr hab.le) hr
    have hs := hseams side (T.index + k) hn
    intro r hri
    cases side
    · exact ⟨(old false k).property.1.trans_le hri.1,
        hri.2.trans_lt (hright.trans_le hs)⟩
    · exact ⟨(hs.trans_lt hleft).trans_le hri.1,
        hri.2.trans_lt (old true k).property.2.2.1⟩
  have hentry (side : Bool) : morseChainSeam T side T.index ∈ radialCore D := by
    apply hreal.radius_mem_core side T.index le_rfl
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact right_mem_Icc.mpr (hreal.2.2.1 false T.index le_rfl).2.1.le
    · exact left_mem_Icc.mpr (hreal.2.2.1 true T.index le_rfl).2.1.le
  have hcore (side : Bool) (r : ℝ)
      (hr : r ∈ radialTailInterval D side (morseChainSeam T side T.index)) :
      scale side * r ∈ radialCore E := by
    have he := hentry side
    rw [radialCore, ha, hb]
    cases side
    · exact ⟨mul_lt_mul_of_pos_left hr.1 G.radiusL_pos,
        (mul_lt_mul_of_pos_left (hr.2.trans he.2) G.radiusL_pos).trans_le
          (mul_le_mul_of_nonneg_right G.radius_order
            (hreal.geometry.1.trans hreal.geometry.2.1).le)⟩
    · exact ⟨(mul_le_mul_of_nonneg_right G.radius_order hreal.geometry.1.le).trans_lt
        (mul_lt_mul_of_pos_left (he.1.trans hr.1) (hscale true)),
        mul_lt_mul_of_pos_left hr.2 (hscale true)⟩
  have hprofile (side : Bool) (r : ℝ)
      (hr : r ∈ radialTailInterval D side (morseChainSeam T side T.index)) :
      E.w (scale side * r) = height side * scale side * D.w r := by
    rw [hw]
    cases side
    · exact (G.left_tail r hr).1
    · exact (G.right_tail r hr).1
  have hcomponent (side : Bool) (k : ℕ) :
      NegativeRadialComponent E (scale side * (old side k).left)
        (scale side * (old side k).right) := by
    have hl := hclosed side k (left_mem_Icc.mpr (old side k).left_lt_right.le)
    have hr := hclosed side k (right_mem_Icc.mpr (old side k).left_lt_right.le)
    have ht : radialTailInterval D side (morseChainSeam T side T.index) =
        Ioo (if side then morseChainSeam T side T.index else D.a)
          (if side then D.b else morseChainSeam T side T.index) := by
      cases side <;> rfl
    exact (negativeRadialComponent_travel_of_tail_identity (hscale side) (hheight side)
      (old side k).property (hcore side _ hl).1 (hcore side _ hr).2
      hreal.geometry.2.2.1.1 hE.choose_spec.1.2.2.1.1
      (by simpa only [ht] using hclosed side k)
      (by simpa only [ht] using hprofile side)).1
  let tail (side : Bool) (k : ℕ) : N01aNegativeComponent E :=
    ⟨(scale side * (old side k).left, scale side * (old side k).right), hcomponent side k⟩
  let middle : N01aNegativeComponent E :=
    ⟨(centralRadius (-sqrt centralOscillatorA), centralRadius (sqrt centralOscillatorA)), by
      simpa only [NegativeRadialComponent, ha, hb, hw] using
        (G.central_model_return hq (hentry false) (hentry true)).1⟩
  have hsepL (k : ℕ) : (tail false k).right < middle.left := by
    have hh := (hclosed false k (right_mem_Icc.mpr (old false k).left_lt_right.le)).2
    exact ((mul_lt_mul_of_pos_left hh G.radiusL_pos).trans G.left_entry).trans
      ((exp_lt_exp.mpr (by linarith only [hq])).trans
        ((lt_log_iff_exp_lt (centralRadius_pos _)).mp K.left_turn))
  have hsepR (k : ℕ) : middle.right < (tail true k).left := by
    have hl := (hclosed true k (left_mem_Icc.mpr (old true k).left_lt_right.le)).1
    exact (((log_lt_iff_lt_exp (centralRadius_pos _)).mp K.right_turn).trans
      ((exp_lt_exp.mpr (by linarith only [hq])).trans G.right_entry)).trans
      (mul_lt_mul_of_pos_left hl (hscale true))
  have hnotmiddle (side : Bool) (k : ℕ) : tail side k ≠ middle := by
    intro he
    cases side
    · have hh := hsepL k
      rw [he] at hh
      exact (not_lt_of_ge middle.left_lt_right.le) hh
    · have hh := hsepR k
      rw [he] at hh
      exact (not_lt_of_ge middle.left_lt_right.le) hh
  have hrightL : StrictAnti (fun k => (old false k).right) := by
    apply strictAnti_nat_of_succ_lt
    intro k
    exact (morseSecondMode_gapOrder hreal (Nat.le_add_right T.index k) false).trans
      (morseSecondMode_modelOrder hreal false (Nat.le_add_right T.index k)).1
  have hrightR : StrictMono (fun k => (old true k).right) := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (morseSecondMode_gapOrder hreal (Nat.le_add_right T.index k) true).trans
      (morseSecondMode_modelOrder hreal true (Nat.le_add_right T.index (k + 1))).1
  have hcross (i j : ℕ) : tail false i ≠ tail true j := by
    intro he
    have hh := ((tail false i).left_lt_right.trans (hsepL i)).trans
      (middle.left_lt_right.trans (hsepR j))
    rw [he] at hh
    exact lt_irrefl _ hh
  have htailinj : Function.Injective (fun p : Bool × ℕ => tail p.1 p.2) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ he
    have hh := congrArg N01aNegativeComponent.right he
    cases a <;> cases b
    · have hij := hrightL.injective (mul_left_cancel₀ (hscale false).ne' hh)
      exact Prod.ext rfl hij
    · exact False.elim (hcross i j he)
    · exact False.elim (hcross j i he.symm)
    · have hij := hrightR.injective (mul_left_cancel₀ (hscale true).ne' hh)
      exact Prod.ext rfl hij
  let f := morseTwoTailAt middle tail
  have hinj : Function.Injective f := by
    intro i j he
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact False.elim (hnotmiddle _ _ he.symm)
    | succ i =>
      cases j with
      | zero => exact False.elim (hnotmiddle _ _ he)
      | succ j =>
        have hp := @htailinj (Equiv.boolProdNatEquivNat.symm i)
          (Equiv.boolProdNatEquivNat.symm j) he
        exact congrArg Nat.succ (Equiv.boolProdNatEquivNat.symm.injective hp)
  have htailcover (side : Bool) (r : ℝ)
      (hr : r ∈ radialTailInterval D side (morseChainSeam T side T.index))
      (hneg : deriv D.w r < 0) : ∃ k, scale side * r ∈ (tail side k).interval := by
    obtain ⟨n, hn, hmem, _⟩ :=
      n01c_morse_negative_tail_model_component hreal hσ side le_rfl hr hneg
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨k, mul_lt_mul_of_pos_left hmem.1 (hscale side),
      mul_lt_mul_of_pos_left hmem.2 (hscale side)⟩
  have hsurj : Function.Surjective f := by
    intro J
    let r : ℝ := (J.left + J.right) / 2
    have hr : r ∈ J.interval := by
      dsimp only [r, N01aNegativeComponent.interval]
      constructor <;> linarith only [J.left_lt_right]
    have hrG : r ∈ Ioo (G.radiusL * D.a) (G.radiusR * D.b) := by
      simpa only [radialCore, ha, hb] using J.mem_core hr
    have hneg : deriv G.profile r < 0 := by simpa only [hw] using J.negative hr
    rcases G.negative_deriv_cases hq hrG hneg with hleft | hmiddle | hright
    · obtain ⟨s, hs, hrs, hsn⟩ := hleft
      obtain ⟨k, hk⟩ := htailcover false s hs hsn
      refine ⟨morseTailIndex false k, ?_⟩
      change morseTwoTailAt middle tail (morseTailIndex false k) = J
      rw [morseTwoTailAt_tail]
      exact N01aNegativeComponent.eq_of_mem hk (hrs ▸ hr)
    · have hrpos : 0 < r := (exp_pos K.left).trans hmiddle.1.1
      have hx : centralModelCoordinate r ^ 2 < centralOscillatorA := by
        apply (centralRadialProfile_deriv_neg_iff (by norm_num : (0 : ℝ) < 1) _).mp
        rw [centralRadius_modelCoordinate hrpos]
        exact hmiddle.2
      have hm : r ∈ middle.interval :=
        ⟨(strictMono_centralRadius (sq_lt.mp hx).1).trans_eq
          (centralRadius_modelCoordinate hrpos),
          (centralRadius_modelCoordinate hrpos).symm.trans_lt
            (strictMono_centralRadius (sq_lt.mp hx).2)⟩
      exact ⟨0, N01aNegativeComponent.eq_of_mem hm hr⟩
    · obtain ⟨s, hs, hrs, hsn⟩ := hright
      obtain ⟨k, hk⟩ := htailcover true s hs hsn
      refine ⟨morseTailIndex true k, ?_⟩
      change morseTwoTailAt middle tail (morseTailIndex true k) = J
      rw [morseTwoTailAt_tail]
      exact N01aNegativeComponent.eq_of_mem hk (hrs ▸ hr)
  let e : ℕ ≃ N01aNegativeComponent E := Equiv.ofBijective f ⟨hinj, hsurj⟩
  obtain ⟨B, hB, hcompare⟩ := exists_n01c_overlappingCell_indexBound hE
  let B₀ : ℝ := |(E.cellIndex (host middle) : ℝ) - E.cellIndex 0|
  refine ⟨e, max B B₀, hB.trans_le (le_max_left _ _), ?_⟩
  intro m
  cases m with
  | zero => exact le_max_right _ _
  | succ m =>
    let p := Equiv.boolProdNatEquivNat.symm m
    let r : ℝ := ((old p.1 p.2).left + (old p.1 p.2).right) / 2
    have hr : r ∈ (old p.1 p.2).interval := by
      dsimp only [r, N01aNegativeComponent.interval]
      constructor <;> linarith only [(old p.1 p.2).left_lt_right]
    obtain ⟨i, hi, hri⟩ :=
      (morseRealization_model_return hreal hσ p.1 (Nat.le_add_right T.index p.2)).2.2 r hr
    have hnew : scale p.1 * r ∈ E.cells i :=
      hcells p.1 i r (hclosed p.1 p.2 (Ioo_subset_Icc_self hr)) hri
    have hmem : scale p.1 * r ∈ (e (m + 1)).interval :=
      ⟨mul_lt_mul_of_pos_left hr.1 (hscale p.1),
        mul_lt_mul_of_pos_left hr.2 (hscale p.1)⟩
    have hi' : E.cellIndex i = E.cellIndex (m + 1) := by
      rw [hindex i, hi, hindex (m + 1), hlabels] <;> rfl
    have hh := hcompare (host (e (m + 1))) i (scale p.1 * r)
      (hhost _ hmem) hnew
    rw [hi'] at hh
    exact hh.trans (le_max_left _ _)

end ContinuousFlexibility.Statements
