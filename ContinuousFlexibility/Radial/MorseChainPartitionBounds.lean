import ContinuousFlexibility.Radial.MorseChainPartitionData
import ContinuousFlexibility.Radial.MorseChainEndpointDistances
import ContinuousFlexibility.Radial.MorseChainGeometry

/-!
# Quantitative geometry of the actual indexed windows

The end-distance comparison uses the same placed model widths and
connector endpoints. The actual overlap changes each distance by a
bounded factor. Compact subsets away from the two ends meet only finitely many windows.
-/

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

private noncomputable def morsePartitionScale (T : Statements.MorseChainData) (k : ℕ) : ℝ :=
  Statements.morseChainA T (T.index + k)

private theorem morsePartitionScale_pos_le_one {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    0 < morsePartitionScale T k ∧ morsePartitionScale T k ≤ 1 := by
  have hN : (100 : ℝ) ≤ ((T.index + k : ℕ) : ℝ) := by
    exact_mod_cast (show 100 ≤ T.index + k from G.start_large.trans (Nat.le_add_right _ _))
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hN 2
  have hd := G.d_exact (T.index + k)
  have hlo := (morseChainA_exp_bounds T (T.index + k) hd).1
  refine ⟨(by positivity : 0 < exp (-((T.index + k : ℕ) : ℝ) ^ 2) / 3).trans_le hlo, ?_⟩
  apply morseChainA_le_of_sq_ge_log T (T.index + k) hd (by norm_num)
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  rw [div_one]
  linarith only [hlog, hs]

private noncomputable def morsePartitionOutwardEnd {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) : ℝ :=
  if side then G.rightEnd else -1

private noncomputable def morsePartitionInwardEnd {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) : ℝ :=
  if side then 1 else -G.rightEnd

/-- The actual outward seam distances and step lengths are controlled
before the windows are widened. -/
theorem morsePartitionSeam_distance_bounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) :
    ∃ C : ℝ, 0 < C ∧ ∀ side k,
      G.factorLo * (9 / 10 : ℝ) * morsePartitionScale T (k + 1) ≤
        morsePartitionOutwardEnd G side - morsePartitionSeam T side (k + 1) ∧
      morsePartitionOutwardEnd G side - morsePartitionSeam T side k ≤ C * morsePartitionScale T k ∧
      G.factorLo * (9 / 10 : ℝ) * morsePartitionScale T k ≤
        morsePartitionSeam T side (k + 1) - morsePartitionSeam T side k := by
  let A := morsePartitionScale T
  let B (k : ℕ) := Statements.morseChainB T (T.index + k)
  let e (k : ℕ) := morseRightCapEnd (A k) (B k) (1 / 100)
  let l (k : ℕ) := G.normal k morseCellLeftCut
  let u (k : ℕ) := G.normal k (e k)
  let S := G.factor
  let c : ℝ := 1 / 100
  have hA (k : ℕ) : 0 < A k ∧ A k ≤ 1 := morsePartitionScale_pos_le_one G k
  have hAB (k : ℕ) : 4 * B k < A k ∧ 0 < B k := by
    have hd : (2 : ℝ) ≤ T.d (T.index + k) := by
      rw [G.d_exact]
      exact_mod_cast morseChainInteger_ge_two (T.index + k)
    exact morseChainParameters_pos T (T.index + k) hd
  have hl (k : ℕ) : 0 < l k :=
    ((G.model k).left_half _ (left_mem_Icc.mpr
      (morseCellLeftCut_lt_rightTurn (hAB k).2 (hAB k).1).le)).2.1
  have hu (k : ℕ) : u k ≤ 2 := by
    have hle : morseRightTurn (A k) (B k) ≤ e k :=
      le_add_of_nonneg_right (morseRightCapLength_pos (hA k).1 (by norm_num : (0 : ℝ) < 1 / 100)).le
    exact ((G.model k).right_half _ (right_mem_Icc.mpr hle)).2.2.1
  have hW (k : ℕ) : (9 / 10 : ℝ) * A k ≤ u k - l k ∧ u k - l k ≤ 2 * A k :=
    (G.model k).span
  have hL (side : Bool) (k : ℕ) : T.radius side (T.index + k) (T.leftX side (T.index + k)) =
      S side k * l k := by rw [G.radius_eq, G.leftX_eq]
  have hU (side : Bool) (k : ℕ) : T.radius side (T.index + k) (T.rightX side (T.index + k)) =
      S side k * u k := by
    rw [G.radius_eq, G.rightX_eq]
    rfl
  have hJ (k : ℕ) : S true (k + 1) * l (k + 1) - S true k * u k =
        S true k * u k * morseChainJoinFraction A c k ∧
      S false k * l k - S false (k + 1) * u (k + 1) =
        S false (k + 1) * u (k + 1) * morseChainJoinFraction A c k := by
    have hR := G.join_width true k
    have hLeft := G.join_width false k
    rw [(G.joins k).1, (G.joins k).2.1, hU, hL] at hR
    rw [(G.joins k).2.2.1, (G.joins k).2.2.2, hU, hL] at hLeft
    exact ⟨hR, hLeft⟩
  obtain ⟨hRm, hLm, hRt, hLt, _, _, _⟩ := morsePartitionSeam_data G
  have hSR (k : ℕ) : morsePartitionSeam T true k = S true k * l k := hL true k
  have hSL (k : ℕ) : morsePartitionSeam T false k = -(S false k * u k) := congrArg Neg.neg (hU false k)
  have hRight : Tendsto (fun k => S true k * l k) atTop (𝓝 G.rightEnd) := by
    rw [← show morsePartitionSeam T true = _ from funext hSR]
    exact hRt
  have hLeft : Tendsto (fun k => S false k * u k) atTop (𝓝 1) := by
    have he : (fun k => S false k * u k) = fun k => -morsePartitionSeam T false k := by
      funext k
      rw [hSL, neg_neg]
    rw [he]
    simpa only [neg_neg] using hLt.neg
  obtain ⟨C, hC, hdR, hdL⟩ := morsePlaced_endpoint_distances T T.index
    (fun k => G.d_exact (T.index + k)) (A := A) (l := l) (u := u) (S := S)
    (c := c) (cLo := 9 / 10) (cHi := 2)
    (sLo := G.factorLo) (sHi := G.factorHi) (rLeft := 1) (rRight := G.rightEnd)
    (fun _ => rfl) (fun k => (hA k).2)
    (by norm_num [c]) (by norm_num [c]) (by norm_num) (by norm_num) G.factorLo_pos
    G.factor_bounds hl hu hW hJ hRight hLeft
  have hWidth (side : Bool) (k : ℕ) : G.factorLo * (9 / 10 : ℝ) * A k ≤ S side k * (u k - l k) := by
    rw [mul_assoc]
    exact mul_le_mul (G.factor_bounds side k).1 (hW k).1
      (mul_nonneg (by norm_num) (hA k).1.le) (G.factor_pos side k).le
  have hu₀ (k : ℕ) : 0 < u k := by linarith only [hl k, (hW k).1, (hA k).1]
  have hj₀ (k : ℕ) : 0 ≤ morseChainJoinFraction A c k :=
    mul_nonneg (by norm_num [c]) (pow_nonneg (le_min (hA k).1.le (hA (k + 1)).1.le) 12)
  refine ⟨C, hC, ?_⟩
  intro side k
  cases side
  · have hord : S false (k + 1) * u (k + 1) ≤ S false k * u k := by
      have h := (hLm (Nat.lt_succ_self k)).le
      rw [hSL, hSL] at h
      exact neg_le_neg_iff.mp h
    have h0 := hdL k (S false k * u k) ⟨hord, le_rfl⟩
    have h1 := hdL k (S false (k + 1) * u (k + 1)) ⟨le_rfl, hord⟩
    change G.factorLo * (9 / 10 : ℝ) * A (k + 1) ≤ -1 - morsePartitionSeam T false (k + 1) ∧
      -1 - morsePartitionSeam T false k ≤ C * A k ∧ _
    rw [hSL, hSL]
    exact ⟨by linarith only [h1.1], by linarith only [h0.2], by
      have hj := mul_nonneg (mul_nonneg (G.factor_pos false (k + 1)).le (hu₀ (k + 1)).le) (hj₀ k)
      nlinarith only [hWidth false k, (hJ k).2, hj]⟩
  · have hord : S true k * l k ≤ S true (k + 1) * l (k + 1) := by
      have h := (hRm (Nat.lt_succ_self k)).le
      rwa [hSR, hSR] at h
    have h0 := hdR k (S true k * l k) ⟨le_rfl, hord⟩
    have h1 := hdR k (S true (k + 1) * l (k + 1)) ⟨hord, le_rfl⟩
    change G.factorLo * (9 / 10 : ℝ) * A (k + 1) ≤
        G.rightEnd - morsePartitionSeam T true (k + 1) ∧
      G.rightEnd - morsePartitionSeam T true k ≤ C * A k ∧ _
    rw [hSR, hSR]
    exact ⟨h1.1, h0.2, by
      have hj := mul_nonneg (mul_nonneg (G.factor_pos true k).le (hu₀ k).le) (hj₀ k)
      nlinarith only [hWidth true k, (hJ k).1, hj]⟩


/-- The overlapping tail windows retain the actual lower and upper end
scales and a compatible width, uniformly in side and index. -/
theorem morsePartitionTailCell_quantitative {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧ ∀ side k,
      (∀ x ∈ morsePartitionTailCell G side k,
        d * morsePartitionScale T (k + 1) ≤ min (x - 1) (G.rightEnd - x) ∧
          min (x - 1) (G.rightEnd - x) ≤ C * morsePartitionScale T k) ∧
      ∃ p q : ℝ, morsePartitionTailCell G side k ⊆ Icc p q ∧ q - p ≤ C * morsePartitionScale T k := by
  let s := morsePartitionSeam T
  let h := morsePartitionWidth G
  let m := morsePartitionMiddleSpan T
  let a := morsePartitionInwardEnd G
  let b := morsePartitionOutwardEnd G
  let A := morsePartitionScale T
  obtain ⟨C, hC, hSeam⟩ := morsePartitionSeam_distance_bounds G
  obtain ⟨hRm, hLm, hRt, hLt, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  obtain ⟨_, _, _, _, hRLen, hRDist, _, _, _, _⟩ :=
    morseSeamOverlap_geometry (middle := m) hm hRm hRc hRt
  obtain ⟨_, _, _, _, hLLen, hLDist, _, _, _, _⟩ :=
    morseSeamOverlap_geometry (middle := m) hm hLm hLc hLt
  let delta := min (s true 0 - 1) (s false 0 - -G.rightEnd)
  have hdelta : 0 < delta := lt_min (sub_pos.mpr (hRc 0).1) (sub_pos.mpr (hLc 0).1)
  let d := min ((15 / 16 : ℝ) * (G.factorLo * (9 / 10))) ((15 / 16 : ℝ) * delta)
  have hd : 0 < d := lt_min (mul_pos (by norm_num) (mul_pos G.factorLo_pos (by norm_num)))
    (mul_pos (by norm_num) hdelta)
  let C' := (9 / 8 : ℝ) * C
  have hC' : 0 < C' := mul_pos (by norm_num) hC
  refine ⟨d, C', hd, hC', ?_⟩
  intro side k
  have hsCore (j : ℕ) : s side j ∈ Ioo (a side) (b side) := by
    cases side
    · exact hLc j
    · exact hRc j
  have hIn : delta ≤ s side k - a side := by
    cases side
    · exact (min_le_right _ _).trans (sub_le_sub_right (hLm.monotone (Nat.zero_le k)) _)
    · exact (min_le_left _ _).trans (sub_le_sub_right (hRm.monotone (Nat.zero_le k)) _)
  have hLen : s side (k + 1) + h side (k + 1) - (s side k - h side k) ≤ C' * A k := by
    have h₁ : s side (k + 1) + h side (k + 1) - (s side k - h side k) ≤
        (9 / 8 : ℝ) * (s side (k + 1) - s side k) := by
      cases side
      · exact hLLen k
      · exact hRLen k
    have h₂ : s side (k + 1) - s side k ≤ C * A k := by
      have h := (hSeam side k).2.1
      change b side - s side k ≤ C * A k at h
      linarith only [(hsCore (k + 1)).2, h]
    exact h₁.trans (by
      change _ ≤ ((9 / 8 : ℝ) * C) * A k
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h₂ (by norm_num))
  constructor
  · intro x hx
    let y := morsePartitionOrientation side x
    have hy : y ∈ morseSeamWindow (s side) (h side) k := hx
    have hDist :
        (15 / 16 : ℝ) * (s side k - a side) ≤ y - a side ∧
        y - a side ≤ (17 / 16 : ℝ) * (s side (k + 1) - a side) ∧
        (15 / 16 : ℝ) * (b side - s side (k + 1)) ≤ b side - y ∧
        b side - y ≤ (17 / 16 : ℝ) * (b side - s side k) := by
      cases side
      · exact hLDist k y hy
      · exact hRDist k y hy
    have hMin : min (y - a side) (b side - y) = min (x - 1) (G.rightEnd - x) := by
      cases side
      · change min (-x - -G.rightEnd) (-1 - -x) = min (x - 1) (G.rightEnd - x)
        rw [show -x - -G.rightEnd = G.rightEnd - x by ring,
          show -1 - -x = x - 1 by ring, min_comm]
      · rfl
    rw [← hMin]
    have hA := morsePartitionScale_pos_le_one G (k + 1)
    constructor
    · apply le_min
      · calc
          _ ≤ d * 1 := mul_le_mul_of_nonneg_left hA.2 hd.le
          _ = d := mul_one _
          _ ≤ (15 / 16 : ℝ) * delta := min_le_right _ _
          _ ≤ (15 / 16 : ℝ) * (s side k - a side) := mul_le_mul_of_nonneg_left hIn (by norm_num)
          _ ≤ _ := hDist.1
      · calc
          _ ≤ ((15 / 16 : ℝ) * (G.factorLo * (9 / 10))) * A (k + 1) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hA.1.le
          _ = (15 / 16 : ℝ) * (G.factorLo * (9 / 10) * A (k + 1)) := by ring
          _ ≤ (15 / 16 : ℝ) * (b side - s side (k + 1)) :=
            mul_le_mul_of_nonneg_left (hSeam side k).1 (by norm_num)
          _ ≤ _ := hDist.2.2.1
    · calc
        _ ≤ b side - y := min_le_right _ _
        _ ≤ (17 / 16 : ℝ) * (b side - s side k) := hDist.2.2.2
        _ ≤ (17 / 16 : ℝ) * (C * A k) := mul_le_mul_of_nonneg_left (hSeam side k).2.1 (by norm_num)
        _ ≤ (9 / 8 : ℝ) * (C * A k) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hC.le (morsePartitionScale_pos_le_one G k).1.le)
        _ = _ := by change _ = ((9 / 8 : ℝ) * C) * A k; ring
  · cases side
    · refine ⟨-(s false (k + 1) + h false (k + 1)), -(s false k - h false k), ?_, ?_⟩
      · intro x hx
        change -x ∈ Ioo (s false k - h false k) (s false (k + 1) + h false (k + 1)) at hx
        exact ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
      · linarith only [hLen]
    · exact ⟨s true k - h true k, s true (k + 1) + h true (k + 1), Ioo_subset_Icc_self, hLen⟩

private theorem morsePartitionMiddleCell_endpoints {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) :
    let p := -(morsePartitionSeam T false 0 + morsePartitionWidth G false 0)
    let q := morsePartitionSeam T true 0 + morsePartitionWidth G true 0
    1 < p ∧ p < q ∧ q < G.rightEnd := by
  let sL := morsePartitionSeam T false
  let sR := morsePartitionSeam T true
  let hL := morsePartitionWidth G false
  let hR := morsePartitionWidth G true
  let m := morsePartitionMiddleSpan T
  obtain ⟨hRm, hLm, _, _, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  have hl := morseSeamWidth_bounds (middle := m) hm hLm hLc 0
  have hr := morseSeamWidth_bounds (middle := m) hm hRm hRc 0
  change 0 < sR 0 + sL 0 at hm
  change 1 < -(sL 0 + hL 0) ∧ -(sL 0 + hL 0) < sR 0 + hR 0 ∧ sR 0 + hR 0 < G.rightEnd
  have hlb : hL 0 ≤ (-1 - sL 0) / 16 := hl.2.2.1
  have hrb : hR 0 ≤ (G.rightEnd - sR 0) / 16 := hr.2.2.1
  have hlp : 0 < hL 0 := hl.1
  have hrp : 0 < hR 0 := hr.1
  exact ⟨by linarith only [(hLc 0).2, hlb],
    by linarith only [hm, hlp, hrp], by linarith only [(hRc 0).2, hrb]⟩


private theorem morse_inv_le_of_inv_le {a C : ℝ} (ha : 0 < a) (h : a⁻¹ ≤ C) :
    C⁻¹ ≤ a := by
  simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr ha) h

/-- A single geometric constant serves the exact exponential window
bounds on both tails and the actual finite middle interval. -/
theorem morsePartitionReference_geometry_bounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) :
    let D := morsePartitionReference G w phi chi chiLeft
    ∃ C : ℝ, 0 < C ∧
      (∀ j x, x ∈ D.cells j →
        C⁻¹ * exp (-((D.cellIndex j : ℝ) + 1) ^ 2) ≤ min (x - D.a) (D.b - x) ∧
        min (x - D.a) (D.b - x) ≤ C * exp (-(D.cellIndex j : ℝ) ^ 2)) ∧
      (∀ j, ∃ p q : ℝ, D.cells j ⊆ Icc p q ∧ q - p ≤ C * exp (-(D.cellIndex j : ℝ) ^ 2)) := by
  let D := morsePartitionReference G w phi chi chiLeft
  obtain ⟨d, K, hd, hK, htail⟩ := morsePartitionTailCell_quantitative G
  let p := -(morsePartitionSeam T false 0 + morsePartitionWidth G false 0)
  let q := morsePartitionSeam T true 0 + morsePartitionWidth G true 0
  have hm : 1 < p ∧ p < q ∧ q < G.rightEnd := morsePartitionMiddleCell_endpoints G
  let delta := min (p - 1) (G.rightEnd - q)
  have hdMid : 0 < delta := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2.2)
  let C := max 1 (max (3 / d) (max (9 * K) (max delta⁻¹ ((G.rightEnd - 1) * exp ((T.index : ℝ) ^ 2)))))
  have hC₁ : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC₁
  have hCd : 3 / d ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : 9 * K ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCδ : delta⁻¹ ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hCM : (G.rightEnd - 1) * exp ((T.index : ℝ) ^ 2) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hInv : C⁻¹ ≤ d / 3 := by
    apply morse_inv_le_of_inv_le (div_pos hd (by norm_num))
    rw [inv_div]
    exact hCd
  have hInvMid : C⁻¹ ≤ delta := morse_inv_le_of_inv_le hdMid hCδ
  have hMidExp : G.rightEnd - 1 ≤ C * exp (-(T.index : ℝ) ^ 2) := by
    calc
      _ = ((G.rightEnd - 1) * exp ((T.index : ℝ) ^ 2)) * exp (-(T.index : ℝ) ^ 2) := by
        rw [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCM (exp_pos _).le


  have hTailUpper (k : ℕ) : K * morsePartitionScale T k ≤ C * exp (-((T.index + k : ℕ) : ℝ) ^ 2) := by
    have h := (morseChainA_exp_bounds T (T.index + k) (G.d_exact _)).2
    calc
      _ ≤ K * (9 * exp (-((T.index + k : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h hK.le
      _ = (9 * K) * exp (-((T.index + k : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCK (exp_pos _).le
  have hTailLower (k : ℕ) : C⁻¹ * exp (-((T.index + (k + 1) : ℕ) : ℝ) ^ 2) ≤
      d * morsePartitionScale T (k + 1) := by
    have h := (morseChainA_exp_bounds T (T.index + (k + 1)) (G.d_exact _)).1
    calc
      _ ≤ (d / 3) * exp (-((T.index + (k + 1) : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hInv (exp_pos _).le
      _ = d * (exp (-((T.index + (k + 1) : ℕ) : ℝ) ^ 2) / 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hd.le
  refine ⟨C, hC, ?_, ?_⟩
  · intro j x hx
    cases j with
    | zero =>
        change x ∈ Ioo p q at hx
        change C⁻¹ * exp (-((T.index : ℝ) + 1) ^ 2) ≤ min (x - 1) (G.rightEnd - x) ∧
          min (x - 1) (G.rightEnd - x) ≤ C * exp (-(T.index : ℝ) ^ 2)
        have hδ : delta ≤ min (x - 1) (G.rightEnd - x) :=
          le_min ((min_le_left _ _).trans (by linarith only [hx.1]))
            ((min_le_right _ _).trans (by linarith only [hx.2]))
        have hOne : exp (-((T.index : ℝ) + 1) ^ 2) ≤ 1 :=
          exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
        exact ⟨(mul_le_mul_of_nonneg_left hOne (inv_nonneg.mpr hC.le)).trans
          ((mul_one _).le.trans (hInvMid.trans hδ)),
          (min_le_left _ _).trans ((by linarith only [hx.2, hm.2.2] : x - 1 ≤ G.rightEnd - 1).trans hMidExp)⟩
    | succ j =>
        let v := Equiv.boolProdNatEquivNat.symm j
        change x ∈ morsePartitionTailCell G v.1 v.2 at hx
        have h := (htail v.1 v.2).1 x hx
        have hlo := (hTailLower v.2).trans h.1
        have hhi := h.2.trans (hTailUpper v.2)
        change C⁻¹ * exp (-(((T.index + v.2 : ℕ) : ℝ) + 1) ^ 2) ≤ min (x - 1) (G.rightEnd - x) ∧
          min (x - 1) (G.rightEnd - x) ≤ C * exp (-((T.index + v.2 : ℕ) : ℝ) ^ 2)
        refine ⟨?_, hhi⟩
        simpa only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one] using hlo
  · intro j
    cases j with
    | zero =>
        refine ⟨p, q, Ioo_subset_Icc_self, ?_⟩
        exact (by linarith only [hm.1, hm.2.2] : q - p ≤ G.rightEnd - 1).trans hMidExp
    | succ j =>
        let v := Equiv.boolProdNatEquivNat.symm j
        obtain ⟨lo, hi, hS, hW⟩ := (htail v.1 v.2).2
        exact ⟨lo, hi, hS, hW.trans (hTailUpper v.2)⟩

theorem morsePartitionReference_cells_nonempty {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) :
    ∀ j, ((morsePartitionReference G w phi chi chiLeft).cells j).Nonempty := by
  intro j
  cases j with
  | zero =>
      let p := -(morsePartitionSeam T false 0 + morsePartitionWidth G false 0)
      let q := morsePartitionSeam T true 0 + morsePartitionWidth G true 0
      have h : 1 < p ∧ p < q ∧ q < G.rightEnd := morsePartitionMiddleCell_endpoints G
      refine ⟨(p + q) / 2, ?_⟩
      change (p + q) / 2 ∈ Ioo p q
      exact ⟨by linarith only [h.2.1], by linarith only [h.2.1]⟩
  | succ j =>
      let v := Equiv.boolProdNatEquivNat.symm j
      change (morsePartitionTailCell G v.1 v.2).Nonempty
      exact ⟨Statements.morseChainSeam T v.1 (T.index + v.2),
        morsePartitionTailCell_covers_block G v.1 v.2
          (by exact left_mem_uIcc)⟩

/-- A compact subset of the open core meets only finitely many actual
windows; the tail proof uses the real distance to the flat ends. -/
theorem morsePartitionReference_locally_finite {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ)
    (Q : Set ℝ) (hQ : IsCompact Q)
    (hQcore : Q ⊆ Statements.radialCore (morsePartitionReference G w phi chi chiLeft)) :
    {j | ((morsePartitionReference G w phi chi chiLeft).cells j ∩ Q).Nonempty}.Finite := by
  let D := morsePartitionReference G w phi chi chiLeft
  change {j | (D.cells j ∩ Q).Nonempty}.Finite
  by_cases hN : Q.Nonempty
  · let dist := fun x : ℝ => min (x - 1) (G.rightEnd - x)
    have hContinuous : Continuous dist :=
      (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
    obtain ⟨p, hp, hmin⟩ := hQ.exists_isMinOn hN hContinuous.continuousOn
    have hpCore : p ∈ Ioo 1 G.rightEnd := hQcore hp
    have hPos : 0 < dist p := lt_min (sub_pos.mpr hpCore.1) (sub_pos.mpr hpCore.2)
    obtain ⟨_, K, _, _, hT⟩ := morsePartitionTailCell_quantitative G
    have hSum : Summable (morsePartitionScale T) :=
      morseChainA_summable_shift T T.index (fun _ => G.d_exact _)
    have hLimit : Tendsto (fun k => K * morsePartitionScale T k) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := K)).mul hSum.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hLimit.eventually (Iio_mem_nhds hPos))
    apply (morsePartitionReference_finite_indices G w phi chi chiLeft (T.index + M)).subset
    intro j hj
    cases j with
    | zero => exact Nat.le_add_right _ _
    | succ j =>
        let v := Equiv.boolProdNatEquivNat.symm j
        change T.index + v.2 ≤ T.index + M
        apply Nat.add_le_add_left
        by_contra h
        obtain ⟨x, hxC, hxQ⟩ := hj
        change x ∈ morsePartitionTailCell G v.1 v.2 at hxC
        have h₁ : dist p ≤ dist x := isMinOn_iff.mp hmin x hxQ
        have h₂ : dist x ≤ K * morsePartitionScale T v.2 := ((hT v.1 v.2).1 x hxC).2
        exact (not_lt_of_ge (h₁.trans h₂)) (hM v.2 (by omega))
  · have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hN
    simp [he]

end ContinuousFlexibility.Radial
