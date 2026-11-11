import ContinuousFlexibility.Radial.MorseCellJoinCollars
import ContinuousFlexibility.Radial.MorseChainRadiusPlacement
import ContinuousFlexibility.Radial.MorseChainEndpointDistances

/-!
# Actual geometry of the two accumulating Morse chains

The cells use one normalized initial-value solution for each index.
The two radius placements are independent of the height choices; only
the entire right placement is dilated to create a positive middle gap.
This constructs the geometry of the Morse chain, before building its
globally flat profile and partition.
-/

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

/-- Auxiliary certificate for the one enlarged, normalized model at a
fixed pair of parameters. All fields refer to the same radius. -/
structure IsNormalizedMorseCell (A B : ℝ) (r : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ r
  radius_at_root : r (morseRightTurn A B) = 1
  speed_at_root : deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5
  equation : ∀ x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth)
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth),
    deriv (deriv r) x = -morseRho A B x * r x
  speed_pos : ∀ x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth)
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth), 0 < deriv r x
  left_half : ∀ x ∈ Icc morseCellLeftCut (morseRightTurn A B),
    |r x - 1| ≤ 6 * A ∧ 0 < r x ∧ r x ≤ 2 ∧
      (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ 7 * A
  right_half : ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)),
    |r x - 1| ≤ (3 / 10000 : ℝ) * A ∧ 0 < r x ∧ r x ≤ 2 ∧
      (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (3 / 100 : ℝ) * A ^ 5
  left_collar : ∀ x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth) morseCellLeftCut,
    (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧ A / 5 ≤ deriv r x ∧ deriv r x ≤ 8 * A ∧
      (3 / 4 : ℝ) * A ≤ -morseRho A B x ∧ -morseRho A B x ≤ 7 * A
  right_collar : ∀ x ∈ Icc (morseRightCapEnd A B (1 / 100))
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth),
    (1 / 2 : ℝ) ≤ r x ∧ r x ≤ 2 ∧ A ^ 5 / 200 ≤ deriv r x ∧ deriv r x ≤ A ^ 5 / 25 ∧
      B / 2 ≤ -morseRho A B x ∧ -morseRho A B x ≤ B
  left_speed : A / 4 ≤ deriv r morseCellLeftCut
  left_expansion : |r morseCellLeftCut - (1 - (15 / 16 : ℝ) * A)| ≤ 21 * A ^ 2
  span : (9 / 10 : ℝ) * A ≤ r (morseRightCapEnd A B (1 / 100)) - r morseCellLeftCut ∧
    r (morseRightCapEnd A B (1 / 100)) - r morseCellLeftCut ≤ 2 * A

theorem exists_normalizedMorseCell {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    ∃ r, IsNormalizedMorseCell A B r := by
  obtain ⟨r, hr, hr₀, hv₀, hEq, hL, hR, hLc, hRc, hv, _, hvL, hrL⟩ :=
    exists_morseRadius_with_joinCollars hB hAB hA₀ hBAlo hBAhi
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hspan := morseRightCap_radius_span (B := B) (δ := (1 / 100 : ℝ)) (c := (1 / 100 : ℝ))
    hA (by norm_num) hr (fun x hx =>
      ⟨(hR x hx).2.2.2.1, by
        simpa only [show (1 / 100 : ℝ) + 2 * (1 / 100) = 3 / 100 by norm_num] using
          (hR x hx).2.2.2.2⟩)
  rw [hr₀] at hspan
  have hA₂ : A ^ 2 ≤ (1 / 1000 : ℝ) * A := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hA₀ hA.le
  refine ⟨r, ⟨hr, hr₀, hv₀, hEq, hv, hL, hR, hLc, hRc, hvL, hrL, ?_⟩⟩
  exact ⟨by linarith only [hspan.1, (abs_le.mp hrL).2, hA₂, hA],
    by linarith only [hspan.2, (abs_le.mp hrL).1, hA₂, hA]⟩

/-- Concrete certificate for the geometry fields of the realized chain.
It does not assume or supply a global profile, partition, or inverse. -/
structure MorseChainGeometryWitness (T : Statements.MorseChainData) where
  normal : ℕ → ℝ → ℝ
  factor : Bool → ℕ → ℝ
  rightEnd : ℝ
  factorLo : ℝ
  factorHi : ℝ
  rightEnd_gt_one : 1 < rightEnd
  start_large : 100 ≤ T.index
  d_exact : ∀ n, T.d n = morseChainInteger n
  factorLo_pos : 0 < factorLo
  factor_bounds : ∀ side k, factorLo ≤ factor side k ∧ factor side k ≤ factorHi
  head_factor : factor true 0 = 5 * factor false 0
  model : ∀ k, IsNormalizedMorseCell (Statements.morseChainA T (T.index + k))
    (Statements.morseChainB T (T.index + k)) (normal k)
  radius_eq : ∀ side k, T.radius side (T.index + k) = fun x => factor side k * normal k x
  leftX_eq : ∀ side k, T.leftX side (T.index + k) = morseCellLeftCut
  rightX_eq : ∀ side k, T.rightX side (T.index + k) =
    morseRightCapEnd (Statements.morseChainA T (T.index + k))
      (Statements.morseChainB T (T.index + k)) (1 / 100)
  joins : ∀ k,
    T.joinLeft true (T.index + k) =
      T.radius true (T.index + k) (T.rightX true (T.index + k)) ∧
    T.joinRight true (T.index + k) =
      T.radius true (T.index + (k + 1)) (T.leftX true (T.index + (k + 1))) ∧
    T.joinLeft false (T.index + k) =
      T.radius false (T.index + (k + 1)) (T.rightX false (T.index + (k + 1))) ∧
    T.joinRight false (T.index + k) =
      T.radius false (T.index + k) (T.leftX false (T.index + k))
  join_width : ∀ side k, T.joinRight side (T.index + k) - T.joinLeft side (T.index + k) =
    T.joinLeft side (T.index + k) *
      morseChainJoinFraction (fun j => Statements.morseChainA T (T.index + j)) (1 / 100) k
  middle_gap : T.radius false T.index (T.rightX false T.index) <
    T.radius true T.index (T.leftX true T.index)
  limits : ∀ side : Bool,
    Tendsto (fun n => T.radius side n (T.leftX side n)) atTop (𝓝 (if side then rightEnd else 1)) ∧
    Tendsto (fun n => T.radius side n (T.rightX side n)) atTop (𝓝 (if side then rightEnd else 1))

/-- The coefficient formulas use only the index and integer choices.
The geometric fields of this private record are never used as evidence. -/
private noncomputable def morseChainCoefficientIndex (N : ℕ) : Statements.MorseChainData where
  index := N
  d := morseChainInteger
  radius := fun _ _ x => x
  leftX := fun _ _ => morseCellLeftCut
  rightX := fun _ _ => morseCellLeftCut
  joinLeft := fun _ _ => morseCellLeftCut
  joinRight := fun _ _ => morseCellLeftCut

theorem exists_morseChainGeometry (initial : ℕ) :
    ∃ T : Statements.MorseChainData, initial ≤ T.index ∧ Nonempty (MorseChainGeometryWitness T) := by
  classical
  let N := max initial 100
  let base := morseChainCoefficientIndex N
  let A (k : ℕ) := Statements.morseChainA base (N + k)
  let B (k : ℕ) := Statements.morseChainB base (N + k)
  let e (k : ℕ) := morseRightCapEnd (A k) (B k) (1 / 100)
  let c : ℝ := 1 / 100
  have hd (k : ℕ) : base.d (N + k) = morseChainInteger (N + k) := rfl
  have hd₂ (k : ℕ) : (2 : ℝ) ≤ base.d (N + k) := by
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two (N + k)
  have hAB (k : ℕ) : 4 * B k < A k ∧ 0 < B k :=
    morseChainParameters_pos base (N + k) (hd₂ k)
  have hA (k : ℕ) : 0 < A k := (mul_pos (by norm_num) (hAB k).2).trans (hAB k).1
  have hBA (k : ℕ) : A k ^ 9 / (9 : ℝ) ^ 9 ≤ B k ∧ B k ≤ A k ^ 9 :=
    morseChainB_A_bounds base (N + k) ((by norm_num : (1 : ℝ) ≤ 2).trans (hd₂ k))
  have hA₀ (k : ℕ) : A k ≤ 1 / 1000 := by
    apply morseChainA_le_of_sq_ge_log base (N + k) (hd k) (by norm_num)
    have hN : (100 : ℝ) ≤ ((N + k : ℕ) : ℝ) := by
      exact_mod_cast (show 100 ≤ N + k from (le_max_right initial 100).trans (Nat.le_add_right N k))
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hN 2
    have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / (1 / 1000 : ℝ))
    linarith only [hlog, hsq]
  have hModels (k : ℕ) : ∃ r, IsNormalizedMorseCell (A k) (B k) r :=
    exists_normalizedMorseCell (hAB k).2 (hAB k).1 (hA₀ k) (hBA k).1 (hBA k).2
  choose r hr using hModels
  let l (k : ℕ) := r k morseCellLeftCut
  let u (k : ℕ) := r k (e k)
  have hl (k : ℕ) : |l k - 1| ≤ 6 * A k :=
    ((hr k).left_half _ (left_mem_Icc.mpr (morseCellLeftCut_lt_rightTurn (hAB k).2 (hAB k).1).le)).1
  have hu (k : ℕ) : |u k - 1| ≤ 6 * A k := by
    have he : morseRightTurn (A k) (B k) ≤ e k :=
      le_add_of_nonneg_right (morseRightCapLength_pos (hA k) (by norm_num : (0 : ℝ) < 1 / 100)).le
    have h := ((hr k).right_half (e k) (right_mem_Icc.mpr he)).1
    change |u k - 1| ≤ (3 / 10000 : ℝ) * A k at h
    linarith only [h, hA k]
  have hl₀ (k : ℕ) : (1 / 2 : ℝ) ≤ l k := by linarith only [(abs_le.mp (hl k)).1, hA₀ k]
  have hu₂ (k : ℕ) : u k ≤ 2 := by linarith only [(abs_le.mp (hu k)).2, hA₀ k]
  have hlu (k : ℕ) : l k < u k := sub_pos.mp
    ((mul_pos (by norm_num : (0 : ℝ) < 9 / 10) (hA k)).trans_le (hr k).span.1)
  have hSum : Summable A := morseChainA_summable_shift base N hd
  obtain ⟨S₀, R₀, s₀, s₁, hR₀, hs₀, hS₀head, hS₀, hJ₀, hOrder, hLim₀⟩ :=
    exists_morseChainRadiusPlacement (A := A) (l := l) (u := u) (c := c)
      (rLeft := 1) (qRight := 1) hA hA₀ hSum hl hu hlu
      (by norm_num [c]) (by norm_num [c]) (by norm_num) (by norm_num)
  have hS₀p (side : Bool) (k : ℕ) : 0 < S₀ side k := hs₀.trans_le (hS₀ side k).1
  have hs₁ : 0 < s₁ := (hS₀p false 0).trans_le (hS₀ false 0).2
  let D := 5 * S₀ false 0
  have hD : 0 < D := mul_pos (by norm_num) (hS₀p false 0)
  let S (side : Bool) (k : ℕ) := if side then D * S₀ true k else S₀ false k
  let R := D * R₀
  let sLo := min 1 D * s₀
  let sHi := max 1 D * s₁
  have hsLo : 0 < sLo := mul_pos (lt_min zero_lt_one hD) hs₀
  have hS (side : Bool) (k : ℕ) : sLo ≤ S side k ∧ S side k ≤ sHi := by
    cases side
    · change min 1 D * s₀ ≤ S₀ false k ∧ S₀ false k ≤ max 1 D * s₁
      exact ⟨((mul_le_mul_of_nonneg_right (min_le_left _ _) hs₀.le).trans_eq (one_mul _)).trans
          (hS₀ false k).1,
        (hS₀ false k).2.trans (((one_mul s₁).symm.le).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁.le))⟩
    · change min 1 D * s₀ ≤ D * S₀ true k ∧ D * S₀ true k ≤ max 1 D * s₁
      exact ⟨mul_le_mul (min_le_right _ _) (hS₀ true k).1 hs₀.le hD.le,
        mul_le_mul (le_max_right _ _) (hS₀ true k).2 (hS₀p true k).le (hD.le.trans (le_max_right _ _))⟩
  have hHead : S true 0 = 5 * S false 0 := by
    change D * S₀ true 0 = D
    rw [hS₀head, mul_one]
  have hJr (k : ℕ) : S true (k + 1) * l (k + 1) - S true k * u k =
      S true k * u k * morseChainJoinFraction A c k := by
    change (D * S₀ true (k + 1)) * l (k + 1) - (D * S₀ true k) * u k =
      (D * S₀ true k) * u k * morseChainJoinFraction A c k
    calc
      _ = D * (S₀ true (k + 1) * l (k + 1) - S₀ true k * u k) := by ring
      _ = D * (S₀ true k * u k * morseChainJoinFraction A c k) := by rw [(hJ₀ k).1]
      _ = _ := by ring
  have hJl (k : ℕ) : S false k * l k - S false (k + 1) * u (k + 1) =
      S false (k + 1) * u (k + 1) * morseChainJoinFraction A c k := (hJ₀ k).2
  have hMiddle : S false 0 * u 0 < S true 0 * l 0 := by
    rw [hHead]
    have hP := hS₀p false 0
    change S₀ false 0 * u 0 < (5 * S₀ false 0) * l 0
    calc
      _ ≤ S₀ false 0 * 2 := mul_le_mul_of_nonneg_left (hu₂ 0) hP.le
      _ < S₀ false 0 * (5 * (1 / 2 : ℝ)) :=
        mul_lt_mul_of_pos_left (by norm_num) hP
      _ ≤ S₀ false 0 * (5 * l 0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hl₀ 0) (by norm_num)) hP.le
      _ = _ := by ring
  have hLimR (f : ℕ → ℝ)
      (h : Tendsto (fun k => S₀ true k * f k) atTop (𝓝 R₀)) :
      Tendsto (fun k => S true k * f k) atTop (𝓝 R) := by
    have he : (fun k => S true k * f k) = fun k => D * (S₀ true k * f k) := by
      funext k
      change (D * S₀ true k) * f k = _
      ring
    rw [he]
    exact (tendsto_const_nhds (x := D)).mul h
  have hLim (side : Bool) :
      Tendsto (fun k => S side k * l k) atTop (𝓝 (if side then R else 1)) ∧
      Tendsto (fun k => S side k * u k) atTop (𝓝 (if side then R else 1)) := by
    cases side
    · exact hLim₀ false
    · exact ⟨hLimR l (hLim₀ true).1, hLimR u (hLim₀ true).2⟩
  have hLeftHead (k : ℕ) : S false k * u k ≤ S false 0 * u 0 := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (((hOrder k).2.2.1.trans (hOrder k).2.2.2).le).trans ih
  have hRightHead (k : ℕ) : S true 0 * l 0 ≤ S true k * l k := by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        have h := (hOrder k).1.trans (hOrder k).2.1
        exact ih.trans (by
          change (D * S₀ true k) * l k ≤ (D * S₀ true (k + 1)) * l (k + 1)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h.le hD.le)
  have hLhead : 1 ≤ S false 0 * u 0 := le_of_tendsto' (hLim false).2 hLeftHead
  have hRhead : S true 0 * l 0 ≤ R := ge_of_tendsto' (hLim true).1 hRightHead
  have hGapEnd : 1 < R := (hLhead.trans_lt hMiddle).trans_le hRhead
  let T : Statements.MorseChainData :=
    { index := N
      d := morseChainInteger
      radius := fun side n x => S side (n - N) * r (n - N) x
      leftX := fun _ _ => morseCellLeftCut
      rightX := fun _ n => e (n - N)
      joinLeft := fun side n => if side then S true (n - N) * u (n - N)
        else S false (n - N + 1) * u (n - N + 1)
      joinRight := fun side n => if side then S true (n - N + 1) * l (n - N + 1)
        else S false (n - N) * l (n - N) }
  refine ⟨T, le_max_left _ _, ⟨{
    normal := r, factor := S, rightEnd := R, factorLo := sLo, factorHi := sHi
    rightEnd_gt_one := hGapEnd
    start_large := le_max_right _ _
    d_exact := fun _ => rfl
    factorLo_pos := hsLo
    factor_bounds := hS
    head_factor := hHead
    model := hr
    radius_eq := ?_
    leftX_eq := fun _ _ => rfl
    rightX_eq := ?_
    joins := ?_
    join_width := ?_
    middle_gap := ?_
    limits := ?_ }⟩⟩
  · intro side k
    change (fun x => S side (N + k - N) * r (N + k - N) x) = _
    rw [Nat.add_sub_cancel_left]
  · intro side k
    change e (N + k - N) = e k
    rw [Nat.add_sub_cancel_left]
  · intro k
    simp [T, l, u]
  · intro side k
    cases side
    · change S false (N + k - N) * l (N + k - N) -
          S false (N + k - N + 1) * u (N + k - N + 1) =
        S false (N + k - N + 1) * u (N + k - N + 1) * morseChainJoinFraction A c k
      rw [Nat.add_sub_cancel_left]
      exact hJl k
    · change S true (N + k - N + 1) * l (N + k - N + 1) -
          S true (N + k - N) * u (N + k - N) =
        S true (N + k - N) * u (N + k - N) * morseChainJoinFraction A c k
      rw [Nat.add_sub_cancel_left]
      exact hJr k
  · change S false (N - N) * u (N - N) < S true (N - N) * l (N - N)
    simpa only [Nat.sub_self] using hMiddle
  · intro side
    exact ⟨(hLim side).1.comp (tendsto_sub_atTop_nat N),
      (hLim side).2.comp (tendsto_sub_atTop_nat N)⟩

theorem MorseChainGeometryWitness.factor_pos {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) : 0 < G.factor side k :=
  G.factorLo_pos.trans_le (G.factor_bounds side k).1

theorem MorseChainGeometryWitness.radius_speed {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    deriv (T.radius side (T.index + k)) =
      fun x => G.factor side k * deriv (G.normal k) x := by
  rw [G.radius_eq]
  funext x
  exact ((((G.model k).smooth.differentiable (by simp) x).hasDerivAt).const_mul
    (G.factor side k)).deriv

/-- The actual entries of T, not just the normalized auxiliary radii,
solve the same scaled Morse radius equation and are strictly increasing. -/
theorem MorseChainGeometryWitness.actual_radius_equation {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    let n := T.index + k
    ContDiff ℝ ∞ (T.radius side n) ∧ T.leftX side n < T.rightX side n ∧
      ∀ x ∈ Icc (T.leftX side n) (T.rightX side n),
        0 < deriv (T.radius side n) x ∧
        deriv (deriv (T.radius side n)) x =
          -morseRho (Statements.morseChainA T n) (Statements.morseChainB T n) x * T.radius side n x := by
  let n := T.index + k
  let A := Statements.morseChainA T n
  let B := Statements.morseChainB T n
  let E := morseRightCapEnd A B (1 / 100)
  have hd : (2 : ℝ) ≤ T.d n := by
    rw [G.d_exact]
    exact_mod_cast morseChainInteger_ge_two n
  have hAB := morseChainParameters_pos T n hd
  have hA : 0 < A := (mul_pos (by norm_num) hAB.2).trans hAB.1
  have hE : morseCellLeftCut < E := (morseCellLeftCut_lt_rightTurn hAB.2 hAB.1).trans_le
    (le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le)
  refine ⟨by rw [G.radius_eq]; exact contDiff_const.mul (G.model k).smooth,
    by rw [G.leftX_eq, G.rightX_eq]; exact hE, ?_⟩
  intro x hx
  rw [G.leftX_eq, G.rightX_eq] at hx
  have hh : 0 ≤ morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  have hx' : x ∈ Icc (morseCellLeftCut - morseJoinCollarWidth) (E + morseJoinCollarWidth) :=
    ⟨(sub_le_self _ hh).trans hx.1, hx.2.trans (le_add_of_nonneg_right hh)⟩
  have hv := (contDiff_infty_iff_deriv.mp (G.model k).smooth).2
  have hdd : HasDerivAt (fun y => G.factor side k * deriv (G.normal k) y)
      (G.factor side k * deriv (deriv (G.normal k)) x) x :=
    ((hv.differentiable (by simp) x).hasDerivAt).const_mul (G.factor side k)
  constructor
  · rw [G.radius_speed]
    exact mul_pos (G.factor_pos side k) ((G.model k).speed_pos x hx')
  · rw [G.radius_speed, hdd.deriv, (G.model k).equation x hx', G.radius_eq]
    change G.factor side k * (-morseRho A B x * G.normal k x) =
      -morseRho A B x * (G.factor side k * G.normal k x)
    ring

end ContinuousFlexibility.Radial
