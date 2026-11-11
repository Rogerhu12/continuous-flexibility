import ContinuousFlexibility.Radial.MorseChainSelectedJets
import ContinuousFlexibility.Radial.MorseChainPartitionTrace
import ContinuousFlexibility.Radial.MorseCellCriticalPoints
import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# Realization of the accumulating Morse chain

The geometry, analytic estimates and all stationary-point assertions
refer to one selected profile. In particular the local critical-point
calculation applies to its actual full germs, including the seams.
-/

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem morseRealization_AB {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (n : ℕ) :
    4 * Statements.morseChainB T n < Statements.morseChainA T n ∧
      0 < Statements.morseChainB T n := by
  apply morseChainParameters_pos
  rw [G.d_exact]
  exact_mod_cast morseChainInteger_ge_two n

/-- The retained turning point, IVP speed and both cuts belong to the
same radius entries used in the reference data. -/
theorem morseChain_retainedGeometry {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) : Statements.MorseChainRetainedGeometry T := by
  intro side n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let n := T.index + k
  let A := Statements.morseChainA T n
  let B := Statements.morseChainB T n
  let X := morseRightTurn A B
  have hAB := morseRealization_AB G n
  have hA : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 4) hAB.2).trans hAB.1
  have hL : T.leftX side n = -log (3 / 2) := G.leftX_eq side k
  have hU : T.rightX side n = X + (1 / 100 : ℝ) / A ^ 4 := G.rightX_eq side k
  have hLT : T.leftX side n < X := by
    rw [G.leftX_eq]
    exact morseCellLeftCut_lt_rightTurn hAB.2 hAB.1
  have hUT : X < T.rightX side n := by
    rw [hU]
    exact lt_add_of_pos_right _ (div_pos (by norm_num) (pow_pos hA _))
  refine ⟨hAB.2, hAB.1, hL, hLT, hUT, hU, ?_⟩
  change deriv (T.radius side n) X = (1 / 100 : ℝ) * A ^ 5 * T.radius side n X
  rw [G.radius_speed, G.radius_eq]
  change G.factor side k * deriv (G.normal k) X =
    (1 / 100 : ℝ) * A ^ 5 * (G.factor side k * G.normal k X)
  rw [(G.model k).speed_at_root, (G.model k).radius_at_root, mul_one]
  ring

private theorem morseRealization_cell_mono {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    StrictMonoOn (T.radius side (T.index + k))
      (Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k))) :=
  morseCell_strictMonoOn (G.actual_radius_equation side k).1
    (fun x hx => ((G.actual_radius_equation side k).2.2 x hx).1)

private theorem morseRealization_radius_mem {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) {X : ℝ}
    (hx : X ∈ Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k))) :
    T.radius side (T.index + k) X ∈
      Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k) := by
  have hmono := (morseRealization_cell_mono G side k).monotoneOn
  have h := (G.actual_radius_equation side k).2.1.le
  exact ⟨hmono (left_mem_Icc.mpr h) hx hx.1, hmono hx (right_mem_Icc.mpr h) hx.2⟩

/-- The assembled height is literally the scaled radius speed at every
retained coordinate, including the two closed endpoints. -/
theorem morseChainGluedProfile_at_radius {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) {X : ℝ}
    (hx : X ∈ Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k))) :
    morseChainGluedProfile G σ hσ (T.radius side (T.index + k) X) =
      Statements.morseChainAmplitude T σ (T.index + k) * deriv (T.radius side (T.index + k)) X :=
  (morseChainGluedProfile_model_germ G σ hσ side k (morseRealization_radius_mem G side k hx)).eq_of_nhds.trans
    (morseChainPhysicalModelHeight_apply_retained G
      (morseChainAmplitude_pos T σ hσ (T.index + k)) side k hx)

private theorem morseRealization_cell_inside {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) :
    Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k) ⊆ Ioo 1 G.rightEnd := by
  let D := morseChainSelectedProfileData G σ hσ
  intro x hx
  have hl : 1 < D.leftCut := D.cuts_inside.1
  have hr : D.rightCut < G.rightEnd := D.cuts_inside.2
  have hmid : D.leftCut < D.rightCut := D.order
  cases side
  · have h : -x ∈ Icc (D.left.enter k) (D.left.leave k) :=
      ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
    have h₁ : -x < -1 := h.2.trans_lt ((D.left.order k).2.trans (D.left.enter_lt_endpoint (k + 1)))
    have h₂ : D.left.enter 0 ≤ -x :=
      (D.left.enter_strictMono.monotone (Nat.zero_le k)).trans h.1
    exact ⟨by linarith only [h₁], (show x ≤ D.leftCut by
      change x ≤ -(D.left.enter 0)
      linarith only [h₂]).trans_lt (hmid.trans hr)⟩
  · have h : x ∈ Icc (D.right.enter k) (D.right.leave k) := hx
    have h₁ : D.rightCut ≤ x :=
      (D.right.enter_strictMono.monotone (Nat.zero_le k)).trans h.1
    exact ⟨(hl.trans hmid).trans_le h₁,
      h.2.trans_lt ((D.right.order k).2.trans (D.right.enter_lt_endpoint (k + 1)))⟩

private theorem morseRealization_join_inside {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) :
    Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k)) ⊆ Ioo 1 G.rightEnd := by
  have hL (s : Bool) (i : ℕ) : morseChainCellLeftRadius T s i ∈ Ioo 1 G.rightEnd :=
    morseRealization_cell_inside G σ hσ s i
      (left_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G s i).le)
  have hU (s : Bool) (i : ℕ) : morseChainCellRightRadius T s i ∈ Ioo 1 G.rightEnd :=
    morseRealization_cell_inside G σ hσ s i
      (right_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G s i).le)
  intro x hx
  cases side
  · rw [(G.joins k).2.2.1, (G.joins k).2.2.2] at hx
    exact ⟨(hU false (k + 1)).1.trans_le hx.1, hx.2.trans_lt (hL false k).2⟩
  · rw [(G.joins k).1, (G.joins k).2.1] at hx
    exact ⟨(hU true k).1.trans_le hx.1, hx.2.trans_lt (hL true (k + 1)).2⟩

private theorem morseRealization_join_slope {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) :
    2 / x ≤ deriv (morseChainGluedProfile G σ hσ) x / morseChainGluedProfile G σ hσ x := by
  have h := morseChainGluedProfile_join_germ G σ hσ side k hx
  rw [h.deriv_eq, h.eq_of_nhds]
  exact (morseChainChosenJoin G σ hσ side k).slope x hx


/-- The actual model germs reduce the critical-point test to the
simple roots of the normalized coefficient on the larger chart. -/
private theorem morseRealization_cell_nonDegenerate {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) {z : ℝ}
    (hz : z ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k))
    (h0 : deriv (morseChainGluedProfile G σ hσ) z = 0) :
    deriv (deriv (morseChainGluedProfile G σ hσ)) z ≠ 0 := by
  let n := T.index + k
  let A := Statements.morseChainA T n
  let B := Statements.morseChainB T n
  let E := morseRightCapEnd A B (1 / 100)
  let l := morseCellLeftCut - morseJoinCollarWidth
  let u := E + morseJoinCollarWidth
  let s := G.factor side k
  let r := G.normal k
  let amp := Statements.morseChainAmplitude T σ n
  let w := morseChainGluedProfile G σ hσ
  have hr := G.actual_radius_equation side k
  let X := morseCellModelCoordinate (T.radius side n) (T.leftX side n) (T.rightX side n) z
  obtain ⟨hX, hXR⟩ := morseCellModelCoordinate_right hr.2.1.le hr.1
    (morseRealization_cell_mono G side k) hz
  change X ∈ Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k)) at hX
  change T.radius side n X = z at hXR
  rw [G.leftX_eq, G.rightX_eq] at hX
  have hh : 0 < morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  have hX' : X ∈ Ioo l u :=
    ⟨(sub_lt_self _ hh).trans_le hX.1, hX.2.trans_lt (lt_add_of_pos_right _ hh)⟩
  have hlu : l ≤ u := hX'.1.le.trans hX'.2.le
  have hs : 0 < s := G.factor_pos side k
  have ha : 0 < amp := morseChainAmplitude_pos T σ hσ n
  have hAB := morseRealization_AB G n
  have hv (y : ℝ) (hy : y ∈ Ioo l u) : 0 < deriv r y :=
    (G.model k).speed_pos y (Ioo_subset_Icc_self hy)
  have hEq (y : ℝ) (hy : y ∈ Ioo l u) :
      deriv (deriv r) y = -morseRho A B y * r y :=
    (G.model k).equation y (Ioo_subset_Icc_self hy)
  have hrX : 0 < r X := by
    rcases le_total X (morseRightTurn A B) with h | h
    · exact ((G.model k).left_half X ⟨hX.1, h⟩).2.1
    · exact ((G.model k).right_half X ⟨h, hX.2⟩).2.1
  have hz' : z = s * r X := hXR.symm.trans (congrFun (G.radius_eq side k) X)
  have hm : StrictMonoOn r (Icc l u) := morseCell_strictMonoOn (G.model k).smooth (G.model k).speed_pos
  have hV : z ∈ Ioo (s * r l) (s * r u) := by
    rw [hz']
    exact ⟨mul_lt_mul_of_pos_left (hm (left_mem_Icc.mpr hlu) (Ioo_subset_Icc_self hX') hX'.1) hs,
      mul_lt_mul_of_pos_left (hm (Ioo_subset_Icc_self hX') (right_mem_Icc.mpr hlu) hX'.2) hs⟩
  have hChart := morseCollarCoordinate_physicalChart hlu hs (G.model k).smooth hv
  have hg : morseChainPhysicalModelHeight G amp side k =ᶠ[𝓝 z] morseCollarExpHeight r amp s l u := by
    filter_upwards [Ioo_mem_nhds hV.1 hV.2] with y hy
    have hvy := hv _ (hChart.2.1 hy)
    change amp * s * deriv r (morseCollarCoordinate r s l u y) =
      exp (log (amp * s * deriv r (morseCollarCoordinate r s l u y)))
    exact (exp_log (mul_pos (mul_pos ha hs) hvy)).symm
  have hw : w =ᶠ[𝓝 z] morseCollarExpHeight r amp s l u :=
    (morseChainGluedProfile_model_germ G σ hσ side k hz).trans hg
  have hd : deriv (morseCollarExpHeight r amp s l u) z = 0 := hw.deriv_eq.symm.trans h0
  have hCrit := (morseCollarExpHeight_critical hAB.2 hAB.1 ha hs (G.model k).smooth
    hv hX' hrX hEq).2.2.2
  rw [hz'] at hd
  have hn := hCrit hd
  change deriv (deriv w) z ≠ 0
  rw [hw.deriv.deriv_eq, hz']
  exact hn

private theorem morseRealization_core_pieces {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    {z : ℝ} (hz : z ∈ Ioo 1 G.rightEnd) :
    (∃ side k, z ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k)) ∨
    (∃ side k, z ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) ∨
      z ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0) := by
  let D := morseChainSelectedProfileData G σ hσ
  by_cases hL : z ≤ D.leftCut
  · have hIn : D.left.enter 0 ≤ -z := by
      change z ≤ -(D.left.enter 0) at hL
      linarith only [hL]
    obtain ⟨k, hk⟩ := morse_outward_block_exists D.left.limit hIn (neg_lt_neg hz.1)
    rcases le_total (-z) (D.left.leave k) with h | h
    · left
      refine ⟨false, k, ?_⟩
      change -z ≤ -morseChainCellLeftRadius T false k at h
      have h' : -morseChainCellRightRadius T false k ≤ -z := hk.1
      exact ⟨neg_le_neg_iff.mp h, neg_le_neg_iff.mp h'⟩
    · right; left
      refine ⟨false, k, ?_⟩
      rw [(G.joins k).2.2.1, (G.joins k).2.2.2]
      change -morseChainCellLeftRadius T false k ≤ -z at h
      have h' : -z ≤ -morseChainCellRightRadius T false (k + 1) := hk.2.le
      exact ⟨neg_le_neg_iff.mp h', neg_le_neg_iff.mp h⟩
  · by_cases hR : D.rightCut ≤ z
    · obtain ⟨k, hk⟩ := morse_outward_block_exists D.right.limit hR hz.2
      rcases le_total z (D.right.leave k) with h | h
      · exact Or.inl ⟨true, k, hk.1, h⟩
      · right; left
        refine ⟨true, k, ?_⟩
        rw [(G.joins k).1, (G.joins k).2.1]
        exact ⟨h, hk.2.le⟩
    · right; right
      have h₁ : D.leftCut ≤ z := le_of_lt (lt_of_not_ge hL)
      have h₂ : z ≤ D.rightCut := le_of_lt (lt_of_not_ge hR)
      change -(-morseChainCellRightRadius T false 0) ≤ z at h₁
      exact ⟨by simpa only [neg_neg] using h₁, h₂⟩

/-- Every stationary point of the same glued positive profile is
nondegenerate. Joins and the middle have positive physical slope. -/
theorem morseChainGluedProfile_nonDegenerate {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    {z : ℝ} (hz : z ∈ Ioo 1 G.rightEnd)
    (h0 : deriv (morseChainGluedProfile G σ hσ) z = 0) :
    deriv (deriv (morseChainGluedProfile G σ hσ)) z ≠ 0 := by
  rcases morseRealization_core_pieces G σ hσ hz with ⟨side, k, hk⟩ | ⟨side, k, hk⟩ | hm
  · exact morseRealization_cell_nonDegenerate G σ hσ side k hk h0
  · have hs := morseRealization_join_slope G σ hσ side k hk
    rw [h0, zero_div] at hs
    exact ((not_le_of_gt (div_pos (by norm_num : (0 : ℝ) < 2)
      (zero_lt_one.trans hz.1))) hs).elim
  · have hg := morseChainGluedProfile_middle_germ G σ hσ hm
    have hMid := Classical.choose_spec (exists_morseChainMiddleUnit G)
    have hD : deriv (morseChainGluedProfile G σ hσ) z =
        Statements.morseChainAmplitude T σ T.index * deriv (morseChainMiddleUnit G) z :=
      hg.deriv_eq.trans
        ((((hMid.1.differentiable (by simp) z).hasDerivAt).const_mul
          (Statements.morseChainAmplitude T σ T.index)).deriv)
    have hpos : 0 < deriv (morseChainGluedProfile G σ hσ) z := by
      rw [hD]
      exact mul_pos (morseChainAmplitude_pos T σ hσ T.index) (hMid.2.2.2.2 z hm)
    exact (hpos.ne' h0).elim


/-- A nonzero compact smooth auxiliary function in the actual finite
core. It supplies only the geometry clause here; the matched kernel
line is the later spectral assertion. -/
theorem exists_morseChainReference_auxiliary {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) :
    ∃ phi : ℝ → ℝ, ContDiff ℝ ∞ phi ∧
      (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
      ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0 := by
  let c := (1 + G.rightEnd) / 2
  let d := G.rightEnd - 1
  have hd : 0 < d := sub_pos.mpr G.rightEnd_gt_one
  let beta : ContDiffBump c :=
    ⟨d / 8, d / 4, div_pos hd (by norm_num), by linarith only [hd]⟩
  have hc : c ∈ Ioo 1 G.rightEnd := by
    change 1 < (1 + G.rightEnd) / 2 ∧ (1 + G.rightEnd) / 2 < G.rightEnd
    exact ⟨by linarith only [G.rightEnd_gt_one], by linarith only [G.rightEnd_gt_one]⟩
  refine ⟨beta, beta.contDiff, ?_, c, hc, ?_⟩
  · intro x hx
    by_contra h
    have hx' : x ∈ Function.support beta := h
    rw [beta.support_eq, Real.ball_eq_Ioo] at hx'
    change x ∈ Ioo (c - d / 4) (c + d / 4) at hx'
    dsimp only [c, d] at hx'
    rcases hx with h | h
    · linarith only [hx'.1, h, G.rightEnd_gt_one]
    · linarith only [hx'.2, h, G.rightEnd_gt_one]
  · rw [beta.one_of_mem_closedBall (Metric.mem_closedBall_self beta.rIn_pos.le)]
    exact one_ne_zero

private theorem morseRealization_join_width {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) :
    T.joinRight side (T.index + k) - T.joinLeft side (T.index + k) ≤
      G.rightEnd * (Statements.morseChainA T (T.index + k)) ^ 12 := by
  let a := T.joinLeft side (T.index + k)
  let b := T.joinRight side (T.index + k)
  let A := Statements.morseChainA T (T.index + k)
  let A' := Statements.morseChainA T (T.index + (k + 1))
  have hA (n : ℕ) : 0 < Statements.morseChainA T n := by
    have h := morseRealization_AB G n
    exact (mul_pos (by norm_num : (0 : ℝ) < 4) h.2).trans h.1
  have ha : a ∈ Ioo 1 G.rightEnd := morseRealization_join_inside G σ hσ side k
    (left_mem_Icc.mpr (morseChainPhysicalJoin_order G side k).le)
  have hpow : (min A A') ^ 12 ≤ A ^ 12 :=
    pow_le_pow_left₀ (le_min (hA _).le (hA _).le) (min_le_left _ _) 12
  calc
    b - a = a * ((1 / 100 : ℝ) * (min A A') ^ 12) := G.join_width side k
    _ ≤ a * A ^ 12 := by
      apply mul_le_mul_of_nonneg_left _ (zero_lt_one.trans ha.1).le
      calc
        _ ≤ 1 * (min A A') ^ 12 :=
          mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (le_min (hA _).le (hA _).le) _)
        _ = (min A A') ^ 12 := one_mul _
        _ ≤ _ := hpow
    _ ≤ _ := mul_le_mul_of_nonneg_right ha.2.le (pow_nonneg (hA _).le _)

/-- Package the complete geometric clauses with estimates on the very
same actual selected profile and partition. -/
theorem morseChainReference_realization {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (phi chi chiLeft : ℝ → ℝ) (C : ℕ → ℝ)
    (hC : ∀ s, 0 < C s) (hCwidth : G.rightEnd ≤ C 0)
    (hPhi : ContDiff ℝ ∞ phi ∧ (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
      ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0)
    (hw : ContDiff ℝ ∞ (morseChainGluedProfile G σ hσ)) :
    let w := morseChainGluedProfile G σ hσ
    let D := morsePartitionReference G w phi chi chiLeft
    (∀ j r, r ∈ D.cells j →
      (C 0)⁻¹ * exp (-((D.cellIndex j : ℝ) + 1) ^ 2) ≤ min (r - D.a) (D.b - r) ∧
        min (r - D.a) (D.b - r) ≤ C 0 * exp (-(D.cellIndex j : ℝ) ^ 2)) →
    (∀ j, ∃ l h : ℝ, D.cells j ⊆ Icc l h ∧
      h - l ≤ C 0 * exp (-(D.cellIndex j : ℝ) ^ 2)) →
    (∀ j r, r ∈ D.cells j → ∀ s, MorseChainJetBounds (D.cellIndex j) s (C s) w r) →
    Statements.MorseChainRealization T σ D C := by
  dsimp only
  let w := morseChainGluedProfile G σ hσ
  let D := morsePartitionReference G w phi chi chiLeft
  intro hDist hWidths hJets
  have hInterior := morseChainGluedProfile_interior_exterior G σ hσ
  have hGeo : Statements.RadialProfileGeometry D :=
    ⟨zero_lt_one, G.rightEnd_gt_one, ⟨hw, hInterior.2.2⟩, ⟨hPhi.1, hPhi.2.1⟩,
      hInterior.2.1, hPhi.2.2, fun _ hx => morseChainGluedProfile_nonDegenerate G σ hσ hx⟩
  have hAcc : Statements.AccumulatingProfileBounds D C := by
    refine ⟨hGeo, morsePartitionReference_radialPartition G w phi chi chiLeft,
      hC, morsePartitionReference_cells_nonempty G w phi chi chiLeft,
      morsePartitionReference_finite_indices G w phi chi chiLeft,
      morsePartitionReference_locally_finite G w phi chi chiLeft, hDist,
      ?_, ?_, ?_, hWidths, ?_, morsePartitionReference_trace G w phi chi chiLeft⟩
    · intro j r hr
      exact (hJets j r hr 0).1
    · intro j r hr s
      exact (hJets j r hr s).2.2.1
    · intro j r hr s
      exact (hJets j r hr s).2.2.2.2
    · intro a b ε _ _ hε
      exact radial_scale_absorption a b hε
  have hRegions := morsePartitionReference_regions G w phi chi chiLeft
  refine ⟨?_, morseChain_retainedGeometry G, ?_, ?_, ?_, G.middle_gap, G.limits,
    hRegions.1, hRegions.2, hAcc⟩
  · intro n _
    rw [G.d_exact]
    exact ⟨(morseChainInteger_spec n).1, (morseChainInteger_spec n).2,
      fun k => morseChainInteger_minimal n k⟩
  · intro side n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨hSmooth, hOrder, hEq⟩ := G.actual_radius_equation side k
    refine ⟨hSmooth, hOrder, fun x hx => ⟨(hEq x hx).1, (hEq x hx).2, ?_⟩⟩
    exact morseChainGluedProfile_at_radius G σ hσ side k hx
  · intro side n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine ⟨morseChainPhysicalJoin_order G side k, ?_, ?_,
      (morseRealization_join_width G σ hσ side k).trans
        (mul_le_mul_of_nonneg_right hCwidth (by positivity)), ?_⟩
    · cases side
      · simpa [Nat.add_assoc] using (G.joins k).2.2.1
      · simpa [Nat.add_assoc] using (G.joins k).1
    · cases side
      · simpa [Nat.add_assoc] using (G.joins k).2.2.2
      · simpa [Nat.add_assoc] using (G.joins k).2.1
    · intro x hx
      exact morseRealization_join_slope G σ hσ side k (Ioo_subset_Icc_self hx)
  · intro side n hn x hx
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨X, hX, rfl⟩ := hx
    exact morseRealization_cell_inside G σ hσ side k (morseRealization_radius_mem G side k hX)

end ContinuousFlexibility.Radial
