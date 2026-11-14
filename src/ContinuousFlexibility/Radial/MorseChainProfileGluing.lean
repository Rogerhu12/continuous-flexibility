module

public import ContinuousFlexibility.Radial.MorseChainGeometry
public import ContinuousFlexibility.Radial.MorseChainFlatExtension
public import ContinuousFlexibility.Radial.MorseMiddleJoin
public import ContinuousFlexibility.Radial.MorseAdjacentJoin

/-!
# Gluing the actual two-sided Morse profile

Each outward block consists of a model cell and its following join. The
left tail uses the reflected coordinate. Two finite cuts connect the
tails to the middle bridge in physical radius.
-/

@[expose] public section

noncomputable section
namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Model cells and joins arranged in an outward coordinate. -/
structure MorseOutwardProfileData (endpoint : ℝ) where
  enter : ℕ → ℝ
  leave : ℕ → ℝ
  model : ℕ → ℝ → ℝ
  join : ℕ → ℝ → ℝ
  limit : Tendsto enter atTop (𝓝 endpoint)
  order : ∀ k, enter k < leave k ∧ leave k < enter (k + 1)
  model_smooth : ∀ k, ContDiff ℝ ∞ (model k)
  join_smooth : ∀ k, ContDiff ℝ ∞ (join k)
  meet : ∀ k, model k =ᶠ[𝓝 (leave k)] join k
  next : ∀ k, join k =ᶠ[𝓝 (enter (k + 1))] model (k + 1)
  model_pos : ∀ k x, x ∈ Icc (enter k) (leave k) → 0 < model k x
  join_pos : ∀ k x, x ∈ Icc (leave k) (enter (k + 1)) → 0 < join k x

namespace MorseOutwardProfileData

variable {endpoint : ℝ} (D : MorseOutwardProfileData endpoint)

def block (k : ℕ) : ℝ → ℝ := morseGlueCut (D.leave k) (D.model k) (D.join k)

def profile : ℝ → ℝ := morseOutwardGlue D.enter D.block

theorem enter_strictMono : StrictMono D.enter :=
  strictMono_nat_of_lt_succ fun k => (D.order k).1.trans (D.order k).2

theorem enter_lt_endpoint (k : ℕ) : D.enter k < endpoint := by
  have hbound : D.enter (k + 1) ≤ endpoint := by
    apply ge_of_tendsto D.limit
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact D.enter_strictMono.monotone hn
  exact (D.enter_strictMono (Nat.lt_succ_self k)).trans_le hbound

theorem block_smooth (k : ℕ) : ContDiff ℝ ∞ (D.block k) :=
  contDiff_morseGlueCut (D.model_smooth k) (D.join_smooth k) (D.meet k)

theorem block_match (k : ℕ) :
    D.block k =ᶠ[𝓝 (D.enter (k + 1))] D.block (k + 1) :=
  (morseGlueCut_eventually_right (D.meet k) (D.order k).2.le).trans
    ((D.next k).trans (morseGlueCut_eventually_left (D.meet (k + 1)) (D.order (k + 1)).1.le).symm)

theorem eventually_model {k : ℕ} {x : ℝ} (hx : x ∈ Icc (D.enter k) (D.leave k)) :
    D.profile =ᶠ[𝓝 x] D.model k :=
  (morseOutwardGlue_eventually_piece D.enter_strictMono D.block_match
    ⟨hx.1, hx.2.trans (D.order k).2.le⟩).trans (morseGlueCut_eventually_left (D.meet k) hx.2)

theorem eventually_join {k : ℕ} {x : ℝ} (hx : x ∈ Icc (D.leave k) (D.enter (k + 1))) :
    D.profile =ᶠ[𝓝 x] D.join k :=
  (morseOutwardGlue_eventually_piece D.enter_strictMono D.block_match
    ⟨(D.order k).1.le.trans hx.1, hx.2⟩).trans (morseGlueCut_eventually_right (D.meet k) hx.1)

theorem zero_of_endpoint_le {x : ℝ} (hx : endpoint ≤ x) : D.profile x = 0 :=
  morseOutwardGlue_eq_zero_of_le D.enter_strictMono D.limit hx

theorem positive {x : ℝ} (hx : D.enter 0 ≤ x) (he : x < endpoint) : 0 < D.profile x := by
  obtain ⟨k, hk⟩ := morse_outward_block_exists D.limit hx he
  rcases le_total x (D.leave k) with h | h
  · rw [(D.eventually_model ⟨hk.1, h⟩).eq_of_nhds]
    exact D.model_pos k x ⟨hk.1, h⟩
  · rw [(D.eventually_join ⟨h, hk.2.le⟩).eq_of_nhds]
    exact D.join_pos k x ⟨h, hk.2.le⟩

theorem contDiffOn_profile : ContDiffOn ℝ ∞ D.profile (Iio endpoint) :=
  contDiffOn_morseOutwardGlue D.enter_strictMono D.limit D.block_smooth D.block_match

/-- Bounds on the actual selected pieces give smoothness and all exterior
zero jets of the same profile. -/
theorem flat_of_exp_bounds (N : ℕ) {d : ℝ} (hd : 0 < d)
    (hDist : ∀ k x, x ∈ Icc (D.enter k) (D.enter (k + 1)) →
      d * exp (-(((N + k : ℕ) : ℝ) + 1) ^ 2) ≤ endpoint - x)
    (hExp : ∀ j, ∃ C B : ℝ, 0 ≤ C ∧ ∀ k x, x ∈ Icc (D.enter k) (D.enter (k + 1)) →
      |iteratedDeriv j (D.block k) x| ≤ C *
        exp (-((N + k : ℕ) : ℝ) ^ (5 / 2 : ℝ) + B * ((N + k : ℕ) : ℝ) ^ 2)) :
    ContDiff ℝ ∞ D.profile ∧ ∀ j x, endpoint ≤ x → iteratedDeriv j D.profile x = 0 :=
  contDiff_flat_morseOutwardGlue N hd D.enter_strictMono D.limit D.block_smooth D.block_match hDist hExp

end MorseOutwardProfileData

private theorem morse_reflect_eventuallyEq {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    (fun y => f (-y)) =ᶠ[𝓝 (-x)] fun y => g (-y) := by
  have ht : Tendsto (fun y : ℝ => -y) (𝓝 (-x)) (𝓝 x) := by
    simpa only [ContinuousAt, neg_neg] using
      (continuous_neg.continuousAt : ContinuousAt (fun y : ℝ => -y) (-x))
  exact h.comp_tendsto ht

/-- Two accumulating tails joined at their first model cells by a finite
middle profile. The left tail is recorded in the outward coordinate `-r`. -/
structure MorseTwoSidedProfileData (leftEnd rightEnd : ℝ) where
  left : MorseOutwardProfileData (-leftEnd)
  right : MorseOutwardProfileData rightEnd
  middle : ℝ → ℝ
  order : -(left.enter 0) < right.enter 0
  middle_smooth : ContDiff ℝ ∞ middle
  middle_pos : ∀ x ∈ Icc (-(left.enter 0)) (right.enter 0), 0 < middle x
  left_meet : (fun x => left.model 0 (-x)) =ᶠ[𝓝 (-(left.enter 0))] middle
  right_meet : middle =ᶠ[𝓝 (right.enter 0)] right.model 0

namespace MorseTwoSidedProfileData

variable {leftEnd rightEnd : ℝ} (D : MorseTwoSidedProfileData leftEnd rightEnd)

def leftCut : ℝ := -(D.left.enter 0)

def rightCut : ℝ := D.right.enter 0

def profile : ℝ → ℝ :=
  morseGlueCut D.leftCut (fun x => D.left.profile (-x))
    (morseGlueCut D.rightCut D.middle D.right.profile)

theorem cuts_inside : leftEnd < D.leftCut ∧ D.rightCut < rightEnd := by
  refine ⟨?_, D.right.enter_lt_endpoint 0⟩
  have h := neg_lt_neg (D.left.enter_lt_endpoint 0)
  simpa only [neg_neg, leftCut] using h

private theorem right_match : D.middle =ᶠ[𝓝 D.rightCut] D.right.profile :=
  D.right_meet.trans (D.right.eventually_model ⟨le_rfl, (D.right.order 0).1.le⟩).symm

private theorem left_match :
    (fun x => D.left.profile (-x)) =ᶠ[𝓝 D.leftCut]
      morseGlueCut D.rightCut D.middle D.right.profile :=
  (morse_reflect_eventuallyEq (D.left.eventually_model ⟨le_rfl, (D.left.order 0).1.le⟩)).trans
    (D.left_meet.trans (morseGlueCut_eventually_left D.right_match D.order.le).symm)

theorem eventually_left {x : ℝ} (hx : x ≤ D.leftCut) :
    D.profile =ᶠ[𝓝 x] fun y => D.left.profile (-y) :=
  morseGlueCut_eventually_left D.left_match hx

theorem eventually_middle {x : ℝ} (hx : x ∈ Icc D.leftCut D.rightCut) :
    D.profile =ᶠ[𝓝 x] D.middle :=
  (morseGlueCut_eventually_right D.left_match hx.1).trans
    (morseGlueCut_eventually_left D.right_match hx.2)

theorem eventually_right {x : ℝ} (hx : D.rightCut ≤ x) :
    D.profile =ᶠ[𝓝 x] D.right.profile :=
  (morseGlueCut_eventually_right D.left_match (D.order.le.trans hx)).trans
    (morseGlueCut_eventually_right D.right_match hx)

theorem eventually_left_model {k : ℕ} {x : ℝ}
    (hx : -x ∈ Icc (D.left.enter k) (D.left.leave k)) :
    D.profile =ᶠ[𝓝 x] fun y => D.left.model k (-y) := by
  have h : x ≤ D.leftCut := by
    simpa only [neg_neg, leftCut] using neg_le_neg
      ((D.left.enter_strictMono.monotone (Nat.zero_le k)).trans hx.1)
  have he := morse_reflect_eventuallyEq (D.left.eventually_model hx)
  rw [neg_neg] at he
  exact (D.eventually_left h).trans he

theorem eventually_left_join {k : ℕ} {x : ℝ}
    (hx : -x ∈ Icc (D.left.leave k) (D.left.enter (k + 1))) :
    D.profile =ᶠ[𝓝 x] fun y => D.left.join k (-y) := by
  have h : x ≤ D.leftCut := by
    simpa only [neg_neg, leftCut] using neg_le_neg
      ((D.left.enter_strictMono.monotone (Nat.zero_le k)).trans ((D.left.order k).1.le.trans hx.1))
  have he := morse_reflect_eventuallyEq (D.left.eventually_join hx)
  rw [neg_neg] at he
  exact (D.eventually_left h).trans he

theorem eventually_right_model {k : ℕ} {x : ℝ}
    (hx : x ∈ Icc (D.right.enter k) (D.right.leave k)) :
    D.profile =ᶠ[𝓝 x] D.right.model k :=
  (D.eventually_right ((D.right.enter_strictMono.monotone (Nat.zero_le k)).trans hx.1)).trans
    (D.right.eventually_model hx)

theorem eventually_right_join {k : ℕ} {x : ℝ}
    (hx : x ∈ Icc (D.right.leave k) (D.right.enter (k + 1))) :
    D.profile =ᶠ[𝓝 x] D.right.join k :=
  (D.eventually_right ((D.right.enter_strictMono.monotone (Nat.zero_le k)).trans
    ((D.right.order k).1.le.trans hx.1))).trans (D.right.eventually_join hx)

theorem zero_exterior {x : ℝ} (hx : x ≤ leftEnd ∨ rightEnd ≤ x) : D.profile x = 0 := by
  rcases hx with h | h
  · rw [(D.eventually_left (h.trans D.cuts_inside.1.le)).eq_of_nhds]
    exact D.left.zero_of_endpoint_le (neg_le_neg h)
  · rw [(D.eventually_right (D.cuts_inside.2.le.trans h)).eq_of_nhds]
    exact D.right.zero_of_endpoint_le h

theorem positive {x : ℝ} (hx : x ∈ Ioo leftEnd rightEnd) : 0 < D.profile x := by
  by_cases hL : x ≤ D.leftCut
  · rw [(D.eventually_left hL).eq_of_nhds]
    have h : D.left.enter 0 ≤ -x := by
      simpa only [leftCut, neg_neg] using neg_le_neg hL
    exact D.left.positive h (neg_lt_neg hx.1)
  by_cases hR : D.rightCut ≤ x
  · rw [(D.eventually_right hR).eq_of_nhds]
    exact D.right.positive hR hx.2
  have hm : x ∈ Icc D.leftCut D.rightCut := ⟨le_of_not_ge hL, le_of_not_ge hR⟩
  rw [(D.eventually_middle hm).eq_of_nhds]
  exact D.middle_pos x hm

theorem contDiffOn_profile : ContDiffOn ℝ ∞ D.profile (Ioo leftEnd rightEnd) := by
  intro x hx
  by_cases hL : x ≤ D.leftCut
  · have hs := D.left.contDiffOn_profile.contDiffAt (Iio_mem_nhds (neg_lt_neg hx.1))
    have hs' : ContDiffAt ℝ ∞ (fun y => D.left.profile (-y)) x :=
      hs.comp x contDiff_id.neg.contDiffAt
    exact (hs'.congr_of_eventuallyEq (D.eventually_left hL)).contDiffWithinAt
  by_cases hR : D.rightCut ≤ x
  · have hs := D.right.contDiffOn_profile.contDiffAt (Iio_mem_nhds hx.2)
    exact (hs.congr_of_eventuallyEq (D.eventually_right hR)).contDiffWithinAt
  have hm : x ∈ Icc D.leftCut D.rightCut := ⟨le_of_not_ge hL, le_of_not_ge hR⟩
  exact (D.middle_smooth.contDiffAt.congr_of_eventuallyEq (D.eventually_middle hm)).contDiffWithinAt

/-- Flatness of the two tails transfers through the same finite cuts,
including all ordinary derivatives at the two physical endpoints. -/
theorem flat_of_tails
    (hLs : ContDiff ℝ ∞ D.left.profile) (hRs : ContDiff ℝ ∞ D.right.profile)
    (hL : ∀ j x, -leftEnd ≤ x → iteratedDeriv j D.left.profile x = 0)
    (hR : ∀ j x, rightEnd ≤ x → iteratedDeriv j D.right.profile x = 0) :
    ContDiff ℝ ∞ D.profile ∧
      ∀ j x, x ≤ leftEnd ∨ rightEnd ≤ x → iteratedDeriv j D.profile x = 0 := by
  refine ⟨contDiff_morseGlueCut (hLs.comp contDiff_id.neg)
    (contDiff_morseGlueCut D.middle_smooth hRs D.right_match) D.left_match, ?_⟩
  intro j x hx
  rcases hx with h | h
  · rw [(D.eventually_left (h.trans D.cuts_inside.1.le)).iteratedDeriv_eq j,
      iteratedDeriv_comp_neg, hL j (-x) (neg_le_neg h), smul_zero]
  · exact ((D.eventually_right (D.cuts_inside.2.le.trans h)).iteratedDeriv_eq j).trans (hR j x h)

end MorseTwoSidedProfileData

/-- The actual left and right radii of a retained cell. -/
def morseChainCellLeftRadius (T : Statements.MorseChainData) (side : Bool) (k : ℕ) : ℝ :=
  T.radius side (T.index + k) (T.leftX side (T.index + k))

def morseChainCellRightRadius (T : Statements.MorseChainData) (side : Bool) (k : ℕ) : ℝ :=
  T.radius side (T.index + k) (T.rightX side (T.index + k))

private def morseChainProfileXEnd (T : Statements.MorseChainData) (k : ℕ) : ℝ :=
  morseRightCapEnd (Statements.morseChainA T (T.index + k))
    (Statements.morseChainB T (T.index + k)) (1 / 100)

private def morseChainProfileXLo : ℝ := morseCellLeftCut - morseJoinCollarWidth

private def morseChainProfileXHi (T : Statements.MorseChainData) (k : ℕ) : ℝ :=
  morseChainProfileXEnd T k + morseJoinCollarWidth

/-- The actual local height and log height use the inverse of the same
placed radius on the enlarged model interval. -/
def morseChainPhysicalModelHeight {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (amplitude : ℝ) (side : Bool) (k : ℕ) (z : ℝ) : ℝ :=
  amplitude * G.factor side k * deriv (G.normal k)
    (morseCollarCoordinate (G.normal k) (G.factor side k)
      morseChainProfileXLo (morseChainProfileXHi T k) z)

def morseChainPhysicalModelLog {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (amplitude : ℝ) (side : Bool) (k : ℕ) : ℝ → ℝ :=
  morseCollarLogProfile (G.normal k) amplitude (G.factor side k)
    morseChainProfileXLo (morseChainProfileXHi T k)

private theorem morseChainProfile_parameters {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    4 * Statements.morseChainB T (T.index + k) < Statements.morseChainA T (T.index + k) ∧
      0 < Statements.morseChainB T (T.index + k) := by
  apply morseChainParameters_pos
  rw [G.d_exact]
  exact_mod_cast morseChainInteger_ge_two (T.index + k)

private theorem morseChainProfile_turn_le_end {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    morseRightTurn (Statements.morseChainA T (T.index + k))
      (Statements.morseChainB T (T.index + k)) ≤ morseChainProfileXEnd T k := by
  have hAB := morseChainProfile_parameters G k
  have hA := (mul_pos (by norm_num : (0 : ℝ) < 4) hAB.2).trans hAB.1
  exact le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le

private theorem morseChainProfile_left_lt_end {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) : morseCellLeftCut < morseChainProfileXEnd T k :=
  (morseCellLeftCut_lt_rightTurn (morseChainProfile_parameters G k).2
    (morseChainProfile_parameters G k).1).trans_le (morseChainProfile_turn_le_end G k)

private theorem morseChainProfile_left_mem {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    morseCellLeftCut ∈ Ioo morseChainProfileXLo (morseChainProfileXHi T k) := by
  have hh : 0 < morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  exact ⟨sub_lt_self _ hh, (morseChainProfile_left_lt_end G k).trans (lt_add_of_pos_right _ hh)⟩

private theorem morseChainProfile_right_mem {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    morseChainProfileXEnd T k ∈ Ioo morseChainProfileXLo (morseChainProfileXHi T k) := by
  have hh : 0 < morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  exact ⟨(sub_lt_self _ hh).trans (morseChainProfile_left_lt_end G k), lt_add_of_pos_right _ hh⟩

private theorem morseChainCellLeftRadius_eq {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    morseChainCellLeftRadius T side k = G.factor side k * G.normal k morseCellLeftCut := by
  rw [morseChainCellLeftRadius, G.leftX_eq, G.radius_eq]

private theorem morseChainCellRightRadius_eq {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    morseChainCellRightRadius T side k = G.factor side k * G.normal k (morseChainProfileXEnd T k) := by
  rw [morseChainCellRightRadius, G.rightX_eq, G.radius_eq, morseChainProfileXEnd]

theorem morseChainCellLeftRadius_lt_right {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    morseChainCellLeftRadius T side k < morseChainCellRightRadius T side k := by
  obtain ⟨hs, hlt, hEq⟩ := G.actual_radius_equation side k
  have hm : StrictMonoOn (T.radius side (T.index + k))
      (Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k))) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hs.continuous.continuousOn
      (fun x hx => (hEq x (interior_subset hx)).1)
  exact hm (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt

theorem morseChainPhysicalModelHeight_apply {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {amplitude : ℝ} (hamp : 0 < amplitude)
    (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Ioo morseChainProfileXLo (morseChainProfileXHi T k)) :
    morseChainPhysicalModelHeight G amplitude side k (T.radius side (T.index + k) x) =
      amplitude * deriv (T.radius side (T.index + k)) x := by
  rw [G.radius_speed, G.radius_eq, morseChainPhysicalModelHeight]
  have hInv : morseCollarCoordinate (G.normal k) (G.factor side k) morseChainProfileXLo
      (morseChainProfileXHi T k) (G.factor side k * G.normal k x) = x :=
    (morseCollarLogProfile_jet hamp (G.factor_pos side k) (G.model k).smooth
    (fun y hy => (G.model k).speed_pos y (Ioo_subset_Icc_self hy)) hx
    ((G.model k).equation x (Ioo_subset_Icc_self hx))).1
  dsimp only
  rw [hInv, mul_assoc]

theorem morseChainPhysicalModelHeight_apply_retained {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {amplitude : ℝ} (hamp : 0 < amplitude)
    (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k))) :
    morseChainPhysicalModelHeight G amplitude side k (T.radius side (T.index + k) x) =
      amplitude * deriv (T.radius side (T.index + k)) x := by
  rw [G.leftX_eq, G.rightX_eq] at hx
  exact morseChainPhysicalModelHeight_apply G hamp side k
    ⟨(morseChainProfile_left_mem G k).1.trans_le hx.1,
      hx.2.trans_lt (morseChainProfile_right_mem G k).2⟩

/-- Extend the true physical model height on the retained cell, preserving
the whole germ at both cuts and at every interior point. -/
theorem exists_morseChainPhysicalModel_extension {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {amplitude : ℝ} (hamp : 0 < amplitude)
    (side : Bool) (k : ℕ) :
    ∃ model : ℝ → ℝ, ContDiff ℝ ∞ model ∧ (∀ z, 0 < model z) ∧
      ∀ z ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k),
        model =ᶠ[𝓝 z] morseChainPhysicalModelHeight G amplitude side k := by
  let s := G.factor side k
  let r := G.normal k
  let p := morseChainProfileXLo
  let q := morseChainProfileXHi T k
  let a := morseChainCellLeftRadius T side k
  let b := morseChainCellRightRadius T side k
  have hs : 0 < s := G.factor_pos side k
  have hr : ContDiff ℝ ∞ r := (G.model k).smooth
  have hv (x : ℝ) (hx : x ∈ Ioo p q) : 0 < deriv r x :=
    (G.model k).speed_pos x (Ioo_subset_Icc_self hx)
  have hEq (x : ℝ) (hx : x ∈ Ioo p q) :
      deriv (deriv r) x = -morseRho (Statements.morseChainA T (T.index + k))
        (Statements.morseChainB T (T.index + k)) x * r x :=
    (G.model k).equation x (Ioo_subset_Icc_self hx)
  have hpq : p ≤ q := (morseChainProfile_left_mem G k).1.le.trans (morseChainProfile_left_mem G k).2.le
  have him := morseCollar_scaledRadius_image_Ioo hpq hs hr hv
  have ha : a ∈ Ioo (s * r p) (s * r q) := by
    rw [← him]
    exact ⟨morseCellLeftCut, morseChainProfile_left_mem G k, (morseChainCellLeftRadius_eq G side k).symm⟩
  have hb : b ∈ Ioo (s * r p) (s * r q) := by
    rw [← him]
    exact ⟨morseChainProfileXEnd T k, morseChainProfile_right_mem G k,
      (morseChainCellRightRadius_eq G side k).symm⟩
  obtain ⟨F, hFs, _, hFg⟩ := exists_contDiff_joinGerm_extension ha.1
    (morseChainCellLeftRadius_lt_right G side k).le hb.2
    (contDiffOn_morseCollarLogProfile hpq hamp hs hr hv hEq)
  refine ⟨fun z => exp (F z), hFs.exp, fun z => exp_pos _, ?_⟩
  intro z hz
  refine ((hFg z hz).fun_comp exp).trans ?_
  have hz' : z ∈ Ioo (s * r p) (s * r q) := ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
  filter_upwards [isOpen_Ioo.mem_nhds hz'] with y hy
  exact exp_morseCollarLogProfile_eqOn hpq hamp hs hr hv hy

private theorem morseChainProfile_head_order {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) :
    morseChainCellRightRadius T false 0 < morseChainCellLeftRadius T true 0 := by
  simpa only [morseChainCellRightRadius, morseChainCellLeftRadius, Nat.add_zero] using G.middle_gap

/-- Choose a middle bridge at unit amplitude. The resulting shape depends
only on the geometric witness, so it can be shared by all height choices. -/
theorem exists_morseChainMiddleUnit {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T) :
    ∃ center : ℝ → ℝ, ContDiff ℝ ∞ center ∧ (∀ z, 0 < center z) ∧
      (center =ᶠ[𝓝 (morseChainCellRightRadius T false 0)] morseChainPhysicalModelHeight G 1 false 0) ∧
      (center =ᶠ[𝓝 (morseChainCellLeftRadius T true 0)] morseChainPhysicalModelHeight G 1 true 0) ∧
      ∀ z ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0),
        0 < deriv center z := by
  let A := Statements.morseChainA T (T.index + 0)
  let B := Statements.morseChainB T (T.index + 0)
  let sL := G.factor false 0
  let sR := G.factor true 0
  let E := morseChainProfileXEnd T 0
  let r := G.normal 0
  have hAB := morseChainProfile_parameters G 0
  have hA : A ≤ 1 := by
    apply morseChainA_le_of_sq_ge_log T (T.index + 0) (G.d_exact _) (by norm_num)
    have hN : (100 : ℝ) ≤ ((T.index + 0 : ℕ) : ℝ) := by exact_mod_cast G.start_large
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hN 2
    rw [div_one]
    linarith only [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9), hsq]
  have hL := (G.model 0).right_collar E
    (left_mem_Icc.mpr (le_add_of_nonneg_right (by norm_num [morseJoinCollarWidth])))
  have hR := (G.model 0).left_half morseCellLeftCut (left_mem_Icc.mpr
    (morseCellLeftCut_lt_rightTurn hAB.2 hAB.1).le)
  have hvL := (G.model 0).right_half E (right_mem_Icc.mpr (morseChainProfile_turn_le_end G 0))
  have hab : sL * r E < sR * r morseCellLeftCut := by
    rw [← morseChainCellRightRadius_eq G false 0, ← morseChainCellLeftRadius_eq G true 0]
    exact morseChainProfile_head_order G
  obtain ⟨h, _, FL, FR, _, _, _, _, _, _, _, _, _, hws, hwp, hwa, hwb, hwd, _⟩ :=
    exists_morseMiddleJoin_of_model_germs (A := A) (B := B) (lam := 1) (eta := 1)
      (pL := morseChainProfileXLo) (qL := morseChainProfileXHi T 0)
      (pR := morseChainProfileXLo) (qR := morseChainProfileXHi T 0)
      hAB.2 hAB.1 hA (by norm_num) (G.factor_pos false 0) (G.factor_pos true 0) (by norm_num)
      (G.model 0).smooth (G.model 0).smooth
      (fun x hx => (G.model 0).speed_pos x (Ioo_subset_Icc_self hx))
      (fun x hx => (G.model 0).speed_pos x (Ioo_subset_Icc_self hx))
      (fun x hx => (G.model 0).equation x (Ioo_subset_Icc_self hx))
      (fun x hx => (G.model 0).equation x (Ioo_subset_Icc_self hx))
      (morseChainProfile_right_mem G 0) (morseChainProfile_left_mem G 0)
      hL.1 hR.2.2.1 hvL.2.2.2.2 (G.model 0).left_speed hab
  refine ⟨morseJoinProfile (sL * r E) (sR * r morseCellLeftCut) h h FL FR, hws, hwp, ?_, ?_, ?_⟩
  · rw [morseChainCellRightRadius_eq G false 0]
    exact hwa
  · rw [morseChainCellLeftRadius_eq G true 0]
    exact hwb
  · intro z hz
    rw [morseChainCellRightRadius_eq G false 0, morseChainCellLeftRadius_eq G true 0] at hz
    exact (hwd z hz).2

def morseChainMiddleUnit {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T) : ℝ → ℝ :=
  Classical.choose (exists_morseChainMiddleUnit G)

/-- The endpoints are indexed by increasing physical radius, on both sides. -/
def morseChainJoinDeparture (side : Bool) (k : ℕ) : ℕ := if side then k else k + 1

def morseChainJoinArrival (side : Bool) (k : ℕ) : ℕ := if side then k + 1 else k

private theorem morseChainProfile_join_ends {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    T.joinLeft side (T.index + k) = morseChainCellRightRadius T side (morseChainJoinDeparture side k) ∧
    T.joinRight side (T.index + k) = morseChainCellLeftRadius T side (morseChainJoinArrival side k) := by
  cases side
  · exact ⟨(G.joins k).2.2.1, (G.joins k).2.2.2⟩
  · exact ⟨(G.joins k).1, (G.joins k).2.1⟩

theorem morseChainPhysicalJoin_order {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    T.joinLeft side (T.index + k) < T.joinRight side (T.index + k) := by
  let i := morseChainJoinDeparture side k
  have hleft : 0 < T.joinLeft side (T.index + k) := by
    rw [(morseChainProfile_join_ends G side k).1, morseChainCellRightRadius_eq G]
    exact mul_pos (G.factor_pos side i)
      ((G.model i).right_half _ (right_mem_Icc.mpr (morseChainProfile_turn_le_end G i))).2.1
  have hA (j : ℕ) : 0 < Statements.morseChainA T (T.index + j) :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) (morseChainProfile_parameters G j).2).trans
      (morseChainProfile_parameters G j).1
  apply sub_pos.mp
  rw [G.join_width, morseChainJoinFraction]
  exact mul_pos hleft (mul_pos (by norm_num) (pow_pos (lt_min (hA k) (hA (k + 1))) 12))

def morseChainProfileJoinCutoff (T : Statements.MorseChainData) (side : Bool) (k : ℕ) : ℝ :=
  (T.joinRight side (T.index + k) - T.joinLeft side (T.index + k)) / 4

def morseChainProfileJoinShape (T : Statements.MorseChainData) (side : Bool) (k : ℕ)
    (FL FR : ℝ → ℝ) : ℝ → ℝ :=
  morseJoinProfile (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))
    (morseChainProfileJoinCutoff T side k) (morseChainProfileJoinCutoff T side k) FL FR

/-- The chosen physical join includes the very same supported logarithmic
germs used in its interpolation formula. -/
structure MorseChainJoinChoice {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (side : Bool) (k : ℕ) where
  leftLog : ℝ → ℝ
  rightLog : ℝ → ℝ
  left_smooth : ContDiff ℝ ∞ leftLog
  right_smooth : ContDiff ℝ ∞ rightLog
  left_germs : ∀ z ∈ Icc (T.joinLeft side (T.index + k))
      (T.joinLeft side (T.index + k) + morseChainProfileJoinCutoff T side k),
    leftLog =ᶠ[𝓝 z] morseChainPhysicalModelLog G
      (Statements.morseChainAmplitude T σ (T.index + morseChainJoinDeparture side k))
      side (morseChainJoinDeparture side k)
  right_germs : ∀ z ∈ Icc (T.joinRight side (T.index + k) - morseChainProfileJoinCutoff T side k)
      (T.joinRight side (T.index + k)),
    rightLog =ᶠ[𝓝 z] morseChainPhysicalModelLog G
      (Statements.morseChainAmplitude T σ (T.index + morseChainJoinArrival side k))
      side (morseChainJoinArrival side k)
  budget : MorseJoinBudget (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))
    (morseChainProfileJoinCutoff T side k) (morseChainProfileJoinCutoff T side k)
    (2 / T.joinLeft side (T.index + k)) leftLog rightLog
  smooth : ContDiff ℝ ∞ (morseChainProfileJoinShape T side k leftLog rightLog)
  positive : ∀ z, 0 < morseChainProfileJoinShape T side k leftLog rightLog z
  left_height : morseChainProfileJoinShape T side k leftLog rightLog =ᶠ[𝓝 (T.joinLeft side (T.index + k))]
    morseChainPhysicalModelHeight G
      (Statements.morseChainAmplitude T σ (T.index + morseChainJoinDeparture side k))
      side (morseChainJoinDeparture side k)
  right_height : morseChainProfileJoinShape T side k leftLog rightLog =ᶠ[𝓝 (T.joinRight side (T.index + k))]
    morseChainPhysicalModelHeight G
      (Statements.morseChainAmplitude T σ (T.index + morseChainJoinArrival side k))
      side (morseChainJoinArrival side k)
  slope : ∀ z ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k)),
    2 / z ≤ deriv (morseChainProfileJoinShape T side k leftLog rightLog) z /
      morseChainProfileJoinShape T side k leftLog rightLog z

theorem exists_morseChainPhysicalJoin {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) :
    Nonempty (MorseChainJoinChoice G σ side k) := by
  let i := morseChainJoinDeparture side k
  let j := morseChainJoinArrival side k
  let n := T.index + i
  let m := T.index + j
  let sL := G.factor side i
  let sR := G.factor side j
  let rL := G.normal i
  let rR := G.normal j
  let a := sL * rL (morseChainProfileXEnd T i)
  let b := sR * rR morseCellLeftCut
  let A := Statements.morseChainA T
  have hEnds : T.joinLeft side (T.index + k) = a ∧ T.joinRight side (T.index + k) = b := by
    rw [(morseChainProfile_join_ends G side k).1, (morseChainProfile_join_ends G side k).2,
      morseChainCellRightRadius_eq G, morseChainCellLeftRadius_eq G]
    exact ⟨rfl, rfl⟩
  have hmin : min (A n) (A m) = min (A (T.index + k)) (A (T.index + (k + 1))) := by
    cases side
    · exact min_comm _ _
    · rfl
  have hw := G.join_width side k
  rw [hEnds.1, hEnds.2] at hw
  have hPlace : b - a = (1 / 100 : ℝ) * a * (min (A n) (A m)) ^ 12 := by
    rw [hw, morseChainJoinFraction, hmin]
    ring
  have hNn : T.index ≤ n := Nat.le_add_right _ _
  have hNm : T.index ≤ m := Nat.le_add_right _ _
  have hadj : m = n + 1 ∨ n = m + 1 := by
    cases side
    · exact Or.inr (Nat.add_assoc _ _ _).symm
    · exact Or.inl (Nat.add_assoc _ _ _).symm
  have hvL := (G.model i).right_half _ (right_mem_Icc.mpr (morseChainProfile_turn_le_end G i))
  have hAB := morseChainProfile_parameters G j
  have hvR := (G.model j).left_half morseCellLeftCut
    (left_mem_Icc.mpr (morseCellLeftCut_lt_rightTurn hAB.2 hAB.1).le)
  obtain ⟨FL, FR, hFL, hFR, hFLg, hFRg, hbudget, hws, hwp, hWa, hWb, hSlope, _⟩ :=
    exists_morseAdjacentJoin_with_model_germs T σ hσ (n := n) (m := m)
      (G.start_large.trans hNn) hNn hNm hadj (G.d_exact n) (G.d_exact m)
      (c := (1 / 100 : ℝ)) (by norm_num) (by norm_num) (G.factor_pos side i) (G.factor_pos side j)
      (G.model i).smooth (G.model j).smooth
      (fun x hx => (G.model i).speed_pos x (Ioo_subset_Icc_self hx))
      (fun x hx => (G.model j).speed_pos x (Ioo_subset_Icc_self hx))
      (fun x hx => (G.model i).equation x (Ioo_subset_Icc_self hx))
      (fun x hx => (G.model j).equation x (Ioo_subset_Icc_self hx))
      (G.model i).right_collar (G.model j).left_collar hvL.2.2.2
      ⟨(G.model j).left_speed, hvR.2.2.2.2⟩ hPlace
  refine ⟨⟨FL, FR, hFL, hFR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals
    simp only [morseChainProfileJoinShape, morseChainProfileJoinCutoff, hEnds.1, hEnds.2, hPlace]
    dsimp only [a, b, sL, sR, rL, rR, n, m, A, i, j, morseChainPhysicalModelLog,
      morseChainPhysicalModelHeight, morseChainProfileXLo, morseChainProfileXHi, morseChainProfileXEnd]
      at hFLg hFRg hbudget hws hwp hWa hWb hSlope ⊢
    assumption

def morseChainChosenJoin {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) :
    MorseChainJoinChoice G σ side k :=
  Classical.choice (exists_morseChainPhysicalJoin G σ hσ side k)

def morseChainChosenModel {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) : ℝ → ℝ :=
  Classical.choose (exists_morseChainPhysicalModel_extension G
    (morseChainAmplitude_pos T σ hσ (T.index + k)) side k)

theorem morseChainChosenModel_spec {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) :
    let model := morseChainChosenModel G σ hσ side k
    ContDiff ℝ ∞ model ∧ (∀ z, 0 < model z) ∧
      ∀ z ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k),
        model =ᶠ[𝓝 z] morseChainPhysicalModelHeight G
          (Statements.morseChainAmplitude T σ (T.index + k)) side k :=
  Classical.choose_spec (exists_morseChainPhysicalModel_extension G
    (morseChainAmplitude_pos T σ hσ (T.index + k)) side k)

def morseChainChosenJoinProfile {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) : ℝ → ℝ :=
  morseChainProfileJoinShape T side k
    (morseChainChosenJoin G σ hσ side k).leftLog (morseChainChosenJoin G σ hσ side k).rightLog

private theorem morseChainProfile_shift (N : ℕ) : Tendsto (fun k : ℕ => N + k) atTop atTop := by
  simpa only [Nat.add_comm N] using tendsto_add_atTop_nat N

/-- The right chain already has the physical coordinate as its outward
coordinate. -/
def morseChainRightProfileData {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) : MorseOutwardProfileData G.rightEnd where
  enter := morseChainCellLeftRadius T true
  leave := morseChainCellRightRadius T true
  model := morseChainChosenModel G σ hσ true
  join := morseChainChosenJoinProfile G σ hσ true
  limit := (G.limits true).1.comp (morseChainProfile_shift T.index)
  order k := ⟨morseChainCellLeftRadius_lt_right G true k, by
    have h := morseChainPhysicalJoin_order G true k
    rw [(morseChainProfile_join_ends G true k).1, (morseChainProfile_join_ends G true k).2] at h
    exact h⟩
  model_smooth k := (morseChainChosenModel_spec G σ hσ true k).1
  join_smooth k := (morseChainChosenJoin G σ hσ true k).smooth
  meet k := by
    have h := (morseChainChosenJoin G σ hσ true k).left_height
    rw [(morseChainProfile_join_ends G true k).1] at h
    exact ((morseChainChosenModel_spec G σ hσ true k).2.2 _
      (right_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G true k).le)).trans h.symm
  next k := by
    have h := (morseChainChosenJoin G σ hσ true k).right_height
    rw [(morseChainProfile_join_ends G true k).2] at h
    exact h.trans ((morseChainChosenModel_spec G σ hσ true (k + 1)).2.2 _
      (left_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G true (k + 1)).le)).symm
  model_pos k x _ := (morseChainChosenModel_spec G σ hσ true k).2.1 x
  join_pos k x _ := (morseChainChosenJoin G σ hσ true k).positive x

/-- The left physical joins run from cell `k+1` to cell `k`. Reflection
orders the same chosen functions outward from the middle bridge. -/
def morseChainLeftProfileData {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) : MorseOutwardProfileData (-1) where
  enter k := -morseChainCellRightRadius T false k
  leave k := -morseChainCellLeftRadius T false k
  model k x := morseChainChosenModel G σ hσ false k (-x)
  join k x := morseChainChosenJoinProfile G σ hσ false k (-x)
  limit := ((G.limits false).2.comp (morseChainProfile_shift T.index)).neg
  order k := ⟨neg_lt_neg (morseChainCellLeftRadius_lt_right G false k), by
    have h := morseChainPhysicalJoin_order G false k
    rw [(morseChainProfile_join_ends G false k).1, (morseChainProfile_join_ends G false k).2] at h
    exact neg_lt_neg h⟩
  model_smooth k := (morseChainChosenModel_spec G σ hσ false k).1.comp contDiff_id.neg
  join_smooth k := (morseChainChosenJoin G σ hσ false k).smooth.comp contDiff_id.neg
  meet k := by
    have h := (morseChainChosenJoin G σ hσ false k).right_height
    rw [(morseChainProfile_join_ends G false k).2] at h
    exact morse_reflect_eventuallyEq (((morseChainChosenModel_spec G σ hσ false k).2.2 _
      (left_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G false k).le)).trans h.symm)
  next k := by
    have h := (morseChainChosenJoin G σ hσ false k).left_height
    rw [(morseChainProfile_join_ends G false k).1] at h
    exact morse_reflect_eventuallyEq (h.trans ((morseChainChosenModel_spec G σ hσ false (k + 1)).2.2 _
      (right_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G false (k + 1)).le)).symm)
  model_pos k x _ := (morseChainChosenModel_spec G σ hσ false k).2.1 (-x)
  join_pos k x _ := (morseChainChosenJoin G σ hσ false k).positive (-x)

/-- The actual selection for one height sequence. The middle bridge is
the fixed unit-amplitude shape times the height of the head cell. -/
def morseChainSelectedProfileData {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) : MorseTwoSidedProfileData 1 G.rightEnd := by
  let amp := Statements.morseChainAmplitude T σ T.index
  have hp : 0 < amp := morseChainAmplitude_pos T σ hσ T.index
  have hm := Classical.choose_spec (exists_morseChainMiddleUnit G)
  refine
    { left := morseChainLeftProfileData G σ hσ
      right := morseChainRightProfileData G σ hσ
      middle := fun x => amp * morseChainMiddleUnit G x
      order := ?_
      middle_smooth := contDiff_const.mul hm.1
      middle_pos := fun x _ => mul_pos hp (hm.2.1 x)
      left_meet := ?_
      right_meet := ?_ }
  · simpa only [morseChainLeftProfileData, morseChainRightProfileData, neg_neg] using
      morseChainProfile_head_order G
  · have hg := (morseChainChosenModel_spec G σ hσ false 0).2.2 _
      (right_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G false 0).le)
    have hc := hm.2.2.1.fun_comp (fun y => amp * y)
    have he : (fun y => amp * y) ∘ morseChainPhysicalModelHeight G 1 false 0 =
        morseChainPhysicalModelHeight G amp false 0 := by
      funext x
      simp only [Function.comp_apply, morseChainPhysicalModelHeight, one_mul, mul_assoc]
    rw [he] at hc
    change (fun x => amp * morseChainMiddleUnit G x) =ᶠ[𝓝 (morseChainCellRightRadius T false 0)]
      morseChainPhysicalModelHeight G amp false 0 at hc
    simpa only [morseChainLeftProfileData, neg_neg, Nat.add_zero] using hg.trans hc.symm
  · have hg := (morseChainChosenModel_spec G σ hσ true 0).2.2 _
      (left_mem_Icc.mpr (morseChainCellLeftRadius_lt_right G true 0).le)
    have hc := hm.2.2.2.1.fun_comp (fun y => amp * y)
    have he : (fun y => amp * y) ∘ morseChainPhysicalModelHeight G 1 true 0 =
        morseChainPhysicalModelHeight G amp true 0 := by
      funext x
      simp only [Function.comp_apply, morseChainPhysicalModelHeight, one_mul, mul_assoc]
    rw [he] at hc
    change (fun x => amp * morseChainMiddleUnit G x) =ᶠ[𝓝 (morseChainCellLeftRadius T true 0)]
      morseChainPhysicalModelHeight G amp true 0 at hc
    simpa only [morseChainRightProfileData, Nat.add_zero] using hc.trans hg.symm

def morseChainGluedProfile {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) : ℝ → ℝ :=
  (morseChainSelectedProfileData G σ hσ).profile

theorem morseChainGluedProfile_interior_exterior {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    let w := morseChainGluedProfile G σ hσ
    ContDiffOn ℝ ∞ w (Ioo 1 G.rightEnd) ∧
      (∀ x ∈ Ioo 1 G.rightEnd, 0 < w x) ∧
      ∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → w x = 0 := by
  let D := morseChainSelectedProfileData G σ hσ
  exact ⟨D.contDiffOn_profile, fun _ hx => D.positive hx, fun _ hx => D.zero_exterior hx⟩

theorem morseChainGluedProfile_model_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) {z : ℝ}
    (hz : z ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k)) :
    morseChainGluedProfile G σ hσ =ᶠ[𝓝 z] morseChainPhysicalModelHeight G
      (Statements.morseChainAmplitude T σ (T.index + k)) side k := by
  let D := morseChainSelectedProfileData G σ hσ
  have hm := (morseChainChosenModel_spec G σ hσ side k).2.2 z hz
  cases side
  · have h := D.eventually_left_model (k := k) (x := z) ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩
    change D.profile =ᶠ[𝓝 z] fun y => morseChainChosenModel G σ hσ false k (-(-y)) at h
    have he : D.profile =ᶠ[𝓝 z] morseChainChosenModel G σ hσ false k := by
      simpa only [neg_neg] using h
    change D.profile =ᶠ[𝓝 z] _
    exact he.trans hm
  · exact (D.eventually_right_model hz).trans hm

theorem morseChainGluedProfile_join_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) {z : ℝ}
    (hz : z ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) :
    morseChainGluedProfile G σ hσ =ᶠ[𝓝 z] morseChainChosenJoinProfile G σ hσ side k := by
  let D := morseChainSelectedProfileData G σ hσ
  have he := morseChainProfile_join_ends G side k
  rw [he.1, he.2] at hz
  cases side
  · have h := D.eventually_left_join (k := k) (x := z) ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩
    change D.profile =ᶠ[𝓝 z] fun y => morseChainChosenJoinProfile G σ hσ false k (-(-y)) at h
    change D.profile =ᶠ[𝓝 z] morseChainChosenJoinProfile G σ hσ false k
    simpa only [neg_neg] using h
  · exact D.eventually_right_join hz

theorem morseChainGluedProfile_middle_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    {z : ℝ} (hz : z ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0)) :
    morseChainGluedProfile G σ hσ =ᶠ[𝓝 z]
      fun x => Statements.morseChainAmplitude T σ T.index * morseChainMiddleUnit G x := by
  let D := morseChainSelectedProfileData G σ hσ
  have h : z ∈ Icc D.leftCut D.rightCut := by
    simpa only [D, MorseTwoSidedProfileData.leftCut, MorseTwoSidedProfileData.rightCut,
      morseChainSelectedProfileData, morseChainLeftProfileData, morseChainRightProfileData, neg_neg] using hz
  exact D.eventually_middle h

end ContinuousFlexibility.Radial
