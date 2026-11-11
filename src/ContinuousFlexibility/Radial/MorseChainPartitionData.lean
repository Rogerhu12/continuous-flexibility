import ContinuousFlexibility.Radial.MorseChainGeometry
import ContinuousFlexibility.Radial.MorseChainOverlapPartition
import Mathlib.Logic.Equiv.Nat

/-!
# One indexing of the two genuine overlapping partitions

The middle term occupies index zero. The remaining indices enumerate
the two outward chains by the actual Bool-times-Nat equivalence.
-/

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped BigOperators ContDiff Topology

def morseTailIndex (side : Bool) (k : ℕ) : ℕ :=
  Equiv.boolProdNatEquivNat (side, k) + 1

def morseTwoTailAt {F : Type*} (middle : F) (tail : Bool → ℕ → F) : ℕ → F
  | 0 => middle
  | k + 1 => tail (Equiv.boolProdNatEquivNat.symm k).1 (Equiv.boolProdNatEquivNat.symm k).2

@[simp]
theorem morseTwoTailAt_middle {F : Type*} (middle : F) (tail : Bool → ℕ → F) :
    morseTwoTailAt middle tail 0 = middle := rfl

@[simp]
theorem morseTwoTailAt_tail {F : Type*} (middle : F) (tail : Bool → ℕ → F) (side : Bool) (k : ℕ) :
    morseTwoTailAt middle tail (morseTailIndex side k) = tail side k := by
  simp [morseTailIndex, morseTwoTailAt]

private theorem morseTwoTail_support_subset (middle : ℝ) (tail : Bool → ℕ → ℝ) :
    Function.support (morseTwoTailAt middle tail) ⊆
      ({0} : Set ℕ) ∪ ((morseTailIndex false) '' Function.support (tail false) ∪
        (morseTailIndex true) '' Function.support (tail true)) := by
  intro n hn
  cases n with
  | zero => exact Or.inl (by simp)
  | succ n =>
      let p := Equiv.boolProdNatEquivNat.symm n
      change tail p.1 p.2 ≠ 0 at hn
      have he : morseTailIndex p.1 p.2 = n + 1 := by
        unfold morseTailIndex
        rw [Prod.eta p]
        exact congrArg (· + 1) (Equiv.boolProdNatEquivNat.apply_symm_apply n)
      cases hp : p.1
      · exact Or.inr (Or.inl ⟨p.2, by simpa only [Function.mem_support, hp] using hn,
          by simpa only [hp] using he⟩)
      · exact Or.inr (Or.inr ⟨p.2, by simpa only [Function.mem_support, hp] using hn,
          by simpa only [hp] using he⟩)

theorem morseTwoTail_support_bound {middle : ℝ} {tail : Bool → ℕ → ℝ}
    (hL : (Function.support (tail false)).Finite)
    (hR : (Function.support (tail true)).Finite)
    (hcL : (Function.support (tail false)).ncard ≤ 2)
    (hcR : (Function.support (tail true)).ncard ≤ 2) :
    (Function.support (morseTwoTailAt middle tail)).Finite ∧
      (Function.support (morseTwoTailAt middle tail)).ncard ≤ 5 := by
  let L := (morseTailIndex false) '' Function.support (tail false)
  let R := (morseTailIndex true) '' Function.support (tail true)
  have hF : (({0} : Set ℕ) ∪ (L ∪ R)).Finite :=
    (finite_singleton _).union ((hL.image _).union (hR.image _))
  have hSub := morseTwoTail_support_subset middle tail
  have hL' : L.ncard ≤ 2 := (ncard_image_le hL).trans hcL
  have hR' : R.ncard ≤ 2 := (ncard_image_le hR).trans hcR
  refine ⟨hF.subset hSub, (ncard_le_ncard hSub hF).trans ?_⟩
  change (({0} : Set ℕ) ∪ (L ∪ R)).ncard ≤ 5
  have hU := ncard_union_le L R
  have hV := ncard_union_le ({0} : Set ℕ) (L ∪ R)
  rw [ncard_singleton] at hV
  omega

theorem morseTwoTail_tsum {middle : ℝ} {tail : Bool → ℕ → ℝ}
    (hL : (Function.support (tail false)).Finite)
    (hR : (Function.support (tail true)).Finite) :
    Summable (morseTwoTailAt middle tail) ∧
      (∑' n, morseTwoTailAt middle tail n) =
        middle + (∑' n, tail false n) + (∑' n, tail true n) := by
  let L := Function.support (tail false)
  let R := Function.support (tail true)
  let f : Bool × ℕ → ℝ := fun p => tail p.1 p.2
  have hP : (Function.support f).Finite := by
    apply (((finite_singleton false).prod hL).union ((finite_singleton true).prod hR)).subset
    rintro ⟨side, k⟩ hk
    cases side
    · exact Or.inl ⟨by simp, hk⟩
    · exact Or.inr ⟨by simp, hk⟩
  have hS : Summable f := summable_of_hasFiniteSupport hP
  have hST (side : Bool) : Summable (tail side) := by
    cases side
    · exact summable_of_hasFiniteSupport hL
    · exact summable_of_hasFiniteSupport hR
  have hF : Summable (morseTwoTailAt middle tail) := by
    apply (summable_nat_add_iff 1).mp
    exact hS.comp_injective Equiv.boolProdNatEquivNat.symm.injective
  refine ⟨hF, ?_⟩
  have hsumT : (∑' n, morseTwoTailAt middle tail (n + 1)) = ∑' p, f p :=
    Equiv.boolProdNatEquivNat.symm.tsum_eq f
  have hSumP : (∑' p, f p) = (∑' n, tail false n) + (∑' n, tail true n) := by
    rw [hS.tsum_prod' hST, tsum_fintype, Fintype.sum_bool]
    change (∑' c, tail true c) + (∑' c, tail false c) =
      (∑' c, tail false c) + (∑' c, tail true c)
    exact add_comm _ _
  rw [← hF.sum_add_tsum_nat_add 1, Finset.sum_range_one, morseTwoTailAt_middle, hsumT, hSumP]
  ring

/-- The genuine outward seam coordinates use r on the right and -r
on the left. The underlying physical points are the contract's seams. -/
noncomputable def morsePartitionSeam (T : Statements.MorseChainData) (side : Bool) (k : ℕ) : ℝ :=
  if side then Statements.morseChainSeam T true (T.index + k)
  else -Statements.morseChainSeam T false (T.index + k)

private theorem morseGeometry_seam_limit_lt {s : ℕ → ℝ} {e : ℝ}
    (hs : StrictMono s) (hT : Tendsto s atTop (𝓝 e)) (n : ℕ) : s n < e := by
  have hbound : s (n + 1) ≤ e := by
    apply ge_of_tendsto hT
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    exact hs.monotone hm
  exact (hs (Nat.lt_succ_self n)).trans_le hbound

theorem morsePartitionSeam_data {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T) :
    let sR := morsePartitionSeam T true
    let sL := morsePartitionSeam T false
    StrictMono sR ∧ StrictMono sL ∧
    Tendsto sR atTop (𝓝 G.rightEnd) ∧ Tendsto sL atTop (𝓝 (-1)) ∧
    (∀ k, sR k ∈ Ioo 1 G.rightEnd) ∧ (∀ k, sL k ∈ Ioo (-G.rightEnd) (-1)) ∧
    0 < sR 0 + sL 0 := by
  let L (side : Bool) (k : ℕ) := T.radius side (T.index + k) (T.leftX side (T.index + k))
  let U (side : Bool) (k : ℕ) := T.radius side (T.index + k) (T.rightX side (T.index + k))
  let sR := morsePartitionSeam T true
  let sL := morsePartitionSeam T false
  have hd (k : ℕ) : (2 : ℝ) ≤ T.d (T.index + k) := by
    rw [G.d_exact]
    exact_mod_cast morseChainInteger_ge_two (T.index + k)
  have hA (k : ℕ) : 0 < Statements.morseChainA T (T.index + k) := by
    have h := morseChainParameters_pos T (T.index + k) (hd k)
    exact (mul_pos (by norm_num) h.2).trans h.1
  have hLU (side : Bool) (k : ℕ) : 0 < L side k ∧ L side k < U side k := by
    let A := Statements.morseChainA T (T.index + k)
    let B := Statements.morseChainB T (T.index + k)
    have h := morseChainParameters_pos T (T.index + k) (hd k)
    have hnorm := (G.model k).left_half morseCellLeftCut
      (left_mem_Icc.mpr (morseCellLeftCut_lt_rightTurn h.2 h.1).le)
    have hlt : G.normal k morseCellLeftCut <
        G.normal k (morseRightCapEnd A B (1 / 100)) :=
      sub_pos.mp ((mul_pos (by norm_num : (0 : ℝ) < 9 / 10) (hA k)).trans_le (G.model k).span.1)
    change 0 < T.radius side (T.index + k) (T.leftX side (T.index + k)) ∧
      T.radius side (T.index + k) (T.leftX side (T.index + k)) <
        T.radius side (T.index + k) (T.rightX side (T.index + k))
    rw [G.radius_eq, G.leftX_eq, G.rightX_eq]
    exact ⟨mul_pos (G.factor_pos side k) hnorm.2.1, mul_lt_mul_of_pos_left hlt (G.factor_pos side k)⟩
  have hJoinPos (side : Bool) (k : ℕ) :
      0 < T.joinRight side (T.index + k) - T.joinLeft side (T.index + k) := by
    have hc : 0 < morseChainJoinFraction
        (fun j => Statements.morseChainA T (T.index + j)) (1 / 100) k :=
      mul_pos (by norm_num) (pow_pos (lt_min (hA k) (hA (k + 1))) 12)
    rw [G.join_width]
    apply mul_pos _ hc
    cases side
    · rw [(G.joins k).2.2.1]
      exact (hLU false (k + 1)).1.trans (hLU false (k + 1)).2
    · rw [(G.joins k).1]
      exact (hLU true k).1.trans (hLU true k).2
  have hRight (k : ℕ) : U true k < L true (k + 1) := by
    have h := sub_pos.mp (hJoinPos true k)
    rw [(G.joins k).1, (G.joins k).2.1] at h
    exact h
  have hLeft (k : ℕ) : U false (k + 1) < L false k := by
    have h := sub_pos.mp (hJoinPos false k)
    rw [(G.joins k).2.2.1, (G.joins k).2.2.2] at h
    exact h
  have hRmono : StrictMono sR := strictMono_nat_of_lt_succ
    (fun k => (hLU true k).2.trans (hRight k))
  have hLmono : StrictMono sL := strictMono_nat_of_lt_succ
    (fun k => neg_lt_neg ((hLeft k).trans (hLU false k).2))
  have hshift : Tendsto (fun k : ℕ => T.index + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat T.index
  have hRlim : Tendsto sR atTop (𝓝 G.rightEnd) := (G.limits true).1.comp hshift
  have hLlim : Tendsto sL atTop (𝓝 (-1)) := ((G.limits false).2.comp hshift).neg
  have hLHead : 1 < U false 0 := by
    have h := morseGeometry_seam_limit_lt hLmono hLlim 0
    change -(U false 0) < -1 at h
    exact neg_lt_neg_iff.mp h
  have hRHead : L true 0 < G.rightEnd := morseGeometry_seam_limit_lt hRmono hRlim 0
  have hGap : U false 0 < L true 0 := by
    simpa only [L, U, Nat.add_zero] using G.middle_gap
  refine ⟨hRmono, hLmono, hRlim, hLlim, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hLHead.trans hGap).trans_le (hRmono.monotone (Nat.zero_le k)),
      morseGeometry_seam_limit_lt hRmono hRlim k⟩
  · intro k
    have h := neg_lt_neg (hGap.trans hRHead)
    exact ⟨h.trans_le (hLmono.monotone (Nat.zero_le k)),
      morseGeometry_seam_limit_lt hLmono hLlim k⟩
  · change 0 < L true 0 + -(U false 0)
    linarith only [hGap]

noncomputable def morsePartitionMiddleSpan (T : Statements.MorseChainData) : ℝ :=
  morsePartitionSeam T true 0 + morsePartitionSeam T false 0

noncomputable def morsePartitionWidth {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) : ℕ → ℝ :=
  if side then morseSeamWidth 1 G.rightEnd (morsePartitionMiddleSpan T) (morsePartitionSeam T true)
  else morseSeamWidth (-G.rightEnd) (-1) (morsePartitionMiddleSpan T) (morsePartitionSeam T false)

noncomputable def morsePartitionOrientation (side : Bool) (x : ℝ) : ℝ :=
  if side then x else -x

noncomputable def morsePartitionTailCell {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) : Set ℝ :=
  morsePartitionOrientation side ⁻¹' morseSeamWindow (morsePartitionSeam T side) (morsePartitionWidth G side) k

noncomputable def morsePartitionMiddleCell {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) : Set ℝ :=
  Ioo (-(morsePartitionSeam T false 0 + morsePartitionWidth G false 0))
    (morsePartitionSeam T true 0 + morsePartitionWidth G true 0)

noncomputable def morsePartitionTailLocalizer {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) (x : ℝ) : ℝ :=
  morseSeamLocalizer (morsePartitionSeam T side) (morsePartitionWidth G side) k
    (morsePartitionOrientation side x)

noncomputable def morsePartitionMiddleLocalizer {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) : ℝ → ℝ :=
  morseMiddleLocalizer (morsePartitionSeam T false) (morsePartitionWidth G false)
    (morsePartitionSeam T true) (morsePartitionWidth G true)

/-- The actual localizers and cells depend only on the chain geometry,
so they are identical for all choices of the physical profile. -/
noncomputable def morsePartitionReference {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) : Statements.ReferenceData where
  a := 1
  b := G.rightEnd
  w := w
  phi := phi
  chi := chi
  chiLeft := chiLeft
  cells := morseTwoTailAt (morsePartitionMiddleCell G) (morsePartitionTailCell G)
  localizer := morseTwoTailAt (morsePartitionMiddleLocalizer G) (morsePartitionTailLocalizer G)
  cellIndex := morseTwoTailAt T.index (fun _ k => T.index + k)

private theorem morsePartition_middle_separation {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) :
    -(morsePartitionSeam T false 0 - morsePartitionWidth G false 0) ≤
      morsePartitionSeam T true 0 - morsePartitionWidth G true 0 := by
  obtain ⟨hR, hL, _, _, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  have hM : 0 < morsePartitionMiddleSpan T := hm
  have hl : morsePartitionWidth G false 0 ≤ morsePartitionMiddleSpan T / 16 :=
    (morseSeamWidth_bounds hM hL hLc 0).2.2.2.1
  have hr : morsePartitionWidth G true 0 ≤ morsePartitionMiddleSpan T / 16 :=
    (morseSeamWidth_bounds hM hR hRc 0).2.2.2.1
  change 0 < morsePartitionSeam T true 0 + morsePartitionSeam T false 0 at hM
  change morsePartitionWidth G false 0 ≤
    (morsePartitionSeam T true 0 + morsePartitionSeam T false 0) / 16 at hl
  change morsePartitionWidth G true 0 ≤
    (morsePartitionSeam T true 0 + morsePartitionSeam T false 0) / 16 at hr
  linarith only [hM, hl, hr]

/-- The genuine Nat-indexed localizers satisfy the actual radial partition
contract, with at most five terms including the middle one. -/
theorem morsePartitionReference_radialPartition {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) :
    Statements.RadialPartition (morsePartitionReference G w phi chi chiLeft) := by
  let D := morsePartitionReference G w phi chi chiLeft
  let sL := morsePartitionSeam T false
  let sR := morsePartitionSeam T true
  let hL := morsePartitionWidth G false
  let hR := morsePartitionWidth G true
  let m := morsePartitionMiddleSpan T
  obtain ⟨hRm, hLm, hRt, hLt, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  have leftGeometry := morseSeamOverlap_geometry (middle := m) hm hLm hLc hLt
  have rightGeometry := morseSeamOverlap_geometry (middle := m) hm hRm hRc hRt
  have hLp : ∀ k, 0 < hL k := leftGeometry.1
  have hRp : ∀ k, 0 < hR k := rightGeometry.1
  have hLsep : ∀ k, sL k + hL k < sL (k + 1) - hL (k + 1) := leftGeometry.2.1
  have hRsep : ∀ k, sR k + hR k < sR (k + 1) - hR (k + 1) := rightGeometry.2.1
  have hLlim : Tendsto (fun k => sL k - hL k) atTop (𝓝 (-1)) :=
    leftGeometry.2.2.2.2.2.2.2.2.2
  have hRlim : Tendsto (fun k => sR k - hR k) atTop (𝓝 G.rightEnd) :=
    rightGeometry.2.2.2.2.2.2.2.2.2
  have hMidsep := morsePartition_middle_separation G
  have hLocal (x : ℝ) : (fun j => D.localizer j x) =
      morseTwoTailAt (morsePartitionMiddleLocalizer G x)
        (fun side k => morsePartitionTailLocalizer G side k x) := by
    funext j
    cases j <;> rfl
  change Statements.RadialPartition D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => exact contDiff_morseMiddleLocalizer sL hL sR hR
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        change ContDiff ℝ ∞ (morsePartitionTailLocalizer G p.1 p.2)
        cases he : p.1
        · exact (contDiff_morseSeamLocalizer sL hL p.2).comp contDiff_id.neg
        · exact contDiff_morseSeamLocalizer sR hR p.2
  · intro j x
    cases j with
    | zero => exact morseMiddleLocalizer_nonneg (hLp 0) (hRp 0) hMidsep x
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        change 0 ≤ morsePartitionTailLocalizer G p.1 p.2 x
        cases he : p.1
        · exact morseSeamLocalizer_nonneg hLp hLsep p.2 (-x)
        · exact morseSeamLocalizer_nonneg hRp hRsep p.2 x
  · intro j
    cases j with
    | zero => exact morseMiddleLocalizer_support (hLp 0) (hRp 0) hMidsep
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        change Function.support (morsePartitionTailLocalizer G p.1 p.2) ⊆
          morsePartitionTailCell G p.1 p.2
        cases he : p.1
        · intro x hx
          exact morseSeamLocalizer_support hLp hLsep p.2 hx
        · intro x hx
          exact morseSeamLocalizer_support hRp hRsep p.2 hx
  · intro j
    cases j with
    | zero =>
        intro x hx
        have hl : hL 0 ≤ (-1 - sL 0) / 16 := (morseSeamWidth_bounds (middle := m) hm hLm hLc 0).2.2.1
        have hr : hR 0 ≤ (G.rightEnd - sR 0) / 16 :=
          (morseSeamWidth_bounds (middle := m) hm hRm hRc 0).2.2.1
        change x ∈ Ioo (-(sL 0 + hL 0)) (sR 0 + hR 0) at hx
        change x ∈ Ioo 1 G.rightEnd
        exact ⟨by linarith only [hx.1, hl, (hLc 0).2], by linarith only [hx.2, hr, (hRc 0).2]⟩
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        change morsePartitionTailCell G p.1 p.2 ⊆ Ioo 1 G.rightEnd
        cases he : p.1
        · intro x hx
          have h := leftGeometry.2.2.2.1 p.2 hx
          change -x ∈ Ioo (-G.rightEnd) (-1) at h
          exact ⟨by linarith only [h.2], by linarith only [h.1]⟩
        · exact rightGeometry.2.2.2.1 p.2
  · intro x hx
    have hLF := (morseSeamLocalizer_finite_overlap hLp hLsep (-x)).1
    have hRF := (morseSeamLocalizer_finite_overlap hRp hRsep x).1
    have hNat := morseTwoTail_tsum (middle := morsePartitionMiddleLocalizer G x)
      (tail := fun side k => morsePartitionTailLocalizer G side k x) hLF hRF
    have hT := morseMiddleLocalizer_add_tsum hLp hRp hLsep hRsep hLlim hRlim hx
    rw [hLocal x]
    exact ⟨hNat.1, hNat.2.trans hT.2.2⟩
  · refine ⟨5, ?_⟩
    intro x
    have hLF := morseSeamLocalizer_finite_overlap hLp hLsep (-x)
    have hRF := morseSeamLocalizer_finite_overlap hRp hRsep x
    change (Function.support (fun j => D.localizer j x)).Finite ∧
      (Function.support (fun j => D.localizer j x)).ncard ≤ 5
    rw [hLocal x]
    exact morseTwoTail_support_bound (middle := morsePartitionMiddleLocalizer G x)
      (tail := fun side k => morsePartitionTailLocalizer G side k x)
      hLF.1 hRF.1 hLF.2 hRF.2

private theorem morsePartitionSeam_as_physical (T : Statements.MorseChainData) (side : Bool) (k : ℕ) :
    Statements.morseChainSeam T side (T.index + k) =
      morsePartitionOrientation side (morsePartitionSeam T side k) := by
  cases side <;> simp [morsePartitionSeam, morsePartitionOrientation]

theorem morsePartitionWidth_eq_contract {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) (side : Bool) (k : ℕ) :
    morsePartitionWidth G side k =
      Statements.morseChainSeamCollar T (morsePartitionReference G w phi chi chiLeft) side (T.index + k) := by
  let s := morsePartitionSeam T side
  let q := Statements.morseChainSeam T side
  let m := morsePartitionMiddleSpan T
  obtain ⟨hR, hL, _, _, _, _, _⟩ := morsePartitionSeam_data G
  have hs : StrictMono s := by
    cases side
    · exact hL
    · exact hR
  have hq (j : ℕ) : q (T.index + j) = morsePartitionOrientation side (s j) :=
    morsePartitionSeam_as_physical T side j
  have hAbs (j : ℕ) : |q (T.index + (j + 1)) - q (T.index + j)| = s (j + 1) - s j := by
    rw [hq (j + 1), hq j]
    have hp := sub_pos.mpr (hs (Nat.lt_succ_self j))
    cases side
    · change |-s (j + 1) - -s j| = s (j + 1) - s j
      rw [show -s (j + 1) - -s j = -(s (j + 1) - s j) by ring, abs_neg, abs_of_pos hp]
    · exact abs_of_pos hp
  have hOut : |q (T.index + k + 1) - q (T.index + k)| = s (k + 1) - s k := by
    simpa only [Nat.add_assoc] using hAbs k
  have hIn : (if T.index < T.index + k then |q (T.index + k) - q (T.index + k - 1)|
      else Statements.morseChainSeam T true T.index - Statements.morseChainSeam T false T.index) =
        morseSeamPrevSpan s m k := by
    cases k with
    | zero =>
        simp [morseSeamPrevSpan, m, morsePartitionMiddleSpan, morsePartitionSeam, sub_eq_add_neg]
    | succ j =>
        rw [ite_eq_left (show T.index < T.index + (j + 1) by omega),
          show T.index + (j + 1) - 1 = T.index + j by omega]
        exact hAbs j
  change morsePartitionWidth G side k =
    min (min (q (T.index + k) - 1) (G.rightEnd - q (T.index + k)))
      (min (if T.index < T.index + k then |q (T.index + k) - q (T.index + k - 1)|
        else Statements.morseChainSeam T true T.index - Statements.morseChainSeam T false T.index)
        |q (T.index + k + 1) - q (T.index + k)|) / 16
  rw [hIn, hOut, hq k]
  cases side
  · change min (min (s k - -G.rightEnd) (-1 - s k))
        (min (morseSeamPrevSpan s m k) (s (k + 1) - s k)) / 16 =
      min (min (-s k - 1) (G.rightEnd - -s k))
        (min (morseSeamPrevSpan s m k) (s (k + 1) - s k)) / 16
    rw [show -s k - 1 = -1 - s k by ring,
      show G.rightEnd - -s k = s k - -G.rightEnd by ring,
      min_comm (-1 - s k) (s k - -G.rightEnd)]
  · rfl

theorem morsePartitionTailCell_subset_region {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) (side : Bool) (k : ℕ) :
    morsePartitionTailCell G side k ⊆
      Statements.morseChainLocalizerRegion T (morsePartitionReference G w phi chi chiLeft)
        side (T.index + k) := by
  let D := morsePartitionReference G w phi chi chiLeft
  let s := morsePartitionSeam T side
  let h := morsePartitionWidth G side
  have hq (j : ℕ) : Statements.morseChainSeam T side (T.index + j) =
      morsePartitionOrientation side (s j) :=
    morsePartitionSeam_as_physical T side j
  have hw (j : ℕ) : Statements.morseChainSeamCollar T D side (T.index + j) = h j :=
    (morsePartitionWidth_eq_contract G w phi chi chiLeft side j).symm
  intro x hx
  unfold Statements.morseChainLocalizerRegion
  simp only [Nat.add_assoc]
  rw [hw k, hw (k + 1), hq k, hq (k + 1)]
  cases side
  · change -x ∈ Ioo (s k - h k) (s (k + 1) + h (k + 1)) at hx
    change x ∈ Icc (-s (k + 1) - h (k + 1)) (-s k + h k)
    exact ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
  · change x ∈ Ioo (s k - h k) (s (k + 1) + h (k + 1)) at hx
    exact Ioo_subset_Icc_self hx

theorem morsePartitionTailCell_covers_block {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    Statements.morseChainBlock T side (T.index + k) ⊆ morsePartitionTailCell G side k := by
  let s := morsePartitionSeam T side
  let h := morsePartitionWidth G side
  let m := morsePartitionMiddleSpan T
  obtain ⟨hRm, hLm, hRt, hLt, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  have hq (j : ℕ) : Statements.morseChainSeam T side (T.index + j) =
      morsePartitionOrientation side (s j) := morsePartitionSeam_as_physical T side j
  intro x hx
  simp only [Statements.morseChainBlock, Nat.add_assoc] at hx
  rw [hq k, hq (k + 1)] at hx
  cases side
  · change x ∈ uIcc (-s k) (-s (k + 1)) at hx
    rw [uIcc_of_ge (neg_le_neg (hLm (Nat.lt_succ_self k)).le)] at hx
    have leftGeometry := morseSeamOverlap_geometry (middle := m) hm hLm hLc hLt
    apply leftGeometry.2.2.1 k
    change -x ∈ Icc (s k) (s (k + 1))
    exact ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
  · change x ∈ uIcc (s k) (s (k + 1)) at hx
    rw [uIcc_of_le (hRm (Nat.lt_succ_self k)).le] at hx
    exact (morseSeamOverlap_geometry (middle := m) hm hRm hRc hRt).2.2.1 k hx

/-- The actual cells meet the revised overlap and coverage clauses,
with the same physical seam indices as the realized geometry. -/
theorem morsePartitionReference_regions {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) :
    let D := morsePartitionReference G w phi chi chiLeft
    (∀ j, T.index < D.cellIndex j → ∃ side,
      D.cells j ⊆ Statements.morseChainLocalizerRegion T D side (D.cellIndex j)) ∧
    (∀ side n, T.index ≤ n → ∀ x ∈ Statements.morseChainBlock T side n,
      ∃ j, D.cellIndex j = n ∧ x ∈ D.cells j) := by
  let D := morsePartitionReference G w phi chi chiLeft
  constructor
  · intro j hj
    cases j with
    | zero => exact False.elim (Nat.lt_irrefl T.index hj)
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        exact ⟨p.1, morsePartitionTailCell_subset_region G w phi chi chiLeft p.1 p.2⟩
  · intro side n hn x hx
    let k := n - T.index
    have hk : T.index + k = n := Nat.add_sub_of_le hn
    refine ⟨morseTailIndex side k, ?_, ?_⟩
    · change morseTwoTailAt T.index (fun _ j => T.index + j) (morseTailIndex side k) = n
      rw [morseTwoTailAt_tail]
      exact hk
    · change x ∈ morseTwoTailAt (morsePartitionMiddleCell G) (morsePartitionTailCell G)
        (morseTailIndex side k)
      rw [morseTwoTailAt_tail]
      apply morsePartitionTailCell_covers_block G side k
      rwa [hk]

/-- Only finitely many actual windows carry any bounded set of indices. -/
theorem morsePartitionReference_finite_indices {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) (M : ℕ) :
    {j | (morsePartitionReference G w phi chi chiLeft).cellIndex j ≤ M}.Finite := by
  have hF : (({0} : Set ℕ) ∪
      ((morseTailIndex false) '' Iic M ∪ (morseTailIndex true) '' Iic M)).Finite :=
    (finite_singleton _).union (((finite_Iic M).image _).union ((finite_Iic M).image _))
  apply hF.subset
  intro j hj
  cases j with
  | zero => exact Or.inl (by simp)
  | succ j =>
      let p := Equiv.boolProdNatEquivNat.symm j
      change T.index + p.2 ≤ M at hj
      have hp : p.2 ∈ Iic M := by
        change p.2 ≤ M
        omega
      have he : morseTailIndex p.1 p.2 = j + 1 := by
        unfold morseTailIndex
        rw [Prod.eta p]
        exact congrArg (· + 1) (Equiv.boolProdNatEquivNat.apply_symm_apply j)
      cases hs : p.1
      · exact Or.inr (Or.inl ⟨p.2, hp, by simpa only [hs] using he⟩)
      · exact Or.inr (Or.inr ⟨p.2, hp, by simpa only [hs] using he⟩)

end ContinuousFlexibility.Radial
