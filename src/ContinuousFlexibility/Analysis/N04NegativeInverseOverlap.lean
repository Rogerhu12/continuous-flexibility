module

public import ContinuousFlexibility.Analysis.N04NegativeInverseGeometry
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The fixed middle band for the two actual negative charts

After division by the common root cut radius, the two root coordinates
have complementary three-halves powers.  Consequently an inverse point
which crosses the reference half-cut stays in a fixed compact middle band
as soon as the opposite chart differs from its reference by at most 1/4.

The same Bool-indexed identity treats both sides.  The transition is only
used on a fixed open interval with strictly positive power arguments;
no smoothness through a physical root is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The fixed scalar change between the two normalized root coordinates. -/
def n04NegativeInverseRootTransition (x : ℝ) : ℝ :=
  (2 - x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)

/-- The coefficient-independent factor relating the two physical heights. -/
def n04NegativeInverseHeightTransition (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (n04NegativeInverseRootTransition x / x))

theorem n04NegativeInverse_travelOrientation_add_opposite
    (T s : ℝ) (side : Bool) :
    n04bTravelOrientation T side s + n04bTravelOrientation T (!side) s = T := by
  cases side <;> simp [n04bTravelOrientation] <;> ring

/-- Normalization removes the coefficient-dependent root cut scale. -/
theorem n04NegativeInverse_normalizedRoot_threeHalves
    {T s : ℝ} (hT : 0 < T) (side : Bool)
    (hs : 0 ≤ n04bTravelOrientation T side s) :
    (n04bRootHalfCoordinate T side s / n04bRootCutRadius T) ^ (3 / 2 : ℝ) =
      2 * n04bTravelOrientation T side s / T := by
  have hr : 0 ≤ n04bRootHalfCoordinate T side s := by
    exact Real.rpow_nonneg (by
      change 0 ≤ 3 * n04bTravelOrientation T side s / 2
      positivity) _
  have hR := n04bRootCutRadius_pos hT
  have hn := n04b_rootTravel_rootCoordinate hs
  have hd := n04b_rootTravel_cut hT
  have hn' : n04bRootHalfCoordinate T side s ^ (3 / 2 : ℝ) =
      (3 / 2 : ℝ) * n04bTravelOrientation T side s := by
    change (2 / 3 : ℝ) * n04bRootHalfCoordinate T side s ^ (3 / 2 : ℝ) =
      n04bTravelOrientation T side s at hn
    linarith
  have hd' : n04bRootCutRadius T ^ (3 / 2 : ℝ) = (3 / 4 : ℝ) * T := by
    change (2 / 3 : ℝ) * n04bRootCutRadius T ^ (3 / 2 : ℝ) = T / 2 at hd
    linarith
  rw [Real.div_rpow hr hR.le, hn', hd']
  field_simp [hT.ne']
  <;> ring

/-- The two normalized radial coordinates have complementary powers on
the entire original travel strip, including points beyond either half-cut. -/
theorem n04NegativeInverse_normalizedRoot_power_sum
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Ioo (0 : ℝ) T) (side : Bool) :
    (n04bRootHalfCoordinate T side s / n04bRootCutRadius T) ^ (3 / 2 : ℝ) +
      (n04bRootHalfCoordinate T (!side) s / n04bRootCutRadius T) ^ (3 / 2 : ℝ) = 2 := by
  rw [n04NegativeInverse_normalizedRoot_threeHalves hT side
      (n04b_travelOrientation_pos_of_fullStrip side hs).le,
    n04NegativeInverse_normalizedRoot_threeHalves hT (!side)
      (n04b_travelOrientation_pos_of_fullStrip (!side) hs).le,
    ← add_div, ← mul_add,
    n04NegativeInverse_travelOrientation_add_opposite T s side]
  exact mul_div_cancel_right₀ (2 : ℝ) hT.ne'

theorem n04NegativeInverse_eq_transition_of_power_sum
    {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) = 2) :
    x = n04NegativeInverseRootTransition y := by
  have he : 2 - y ^ (3 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := by linarith
  rw [n04NegativeInverseRootTransition, he, ← Real.rpow_mul hx]
  norm_num

theorem n04NegativeInverse_normalizedRoot_transition
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Ioo (0 : ℝ) T) (side : Bool) :
    n04bRootHalfCoordinate T side s / n04bRootCutRadius T =
      n04NegativeInverseRootTransition
        (n04bRootHalfCoordinate T (!side) s / n04bRootCutRadius T) := by
  apply n04NegativeInverse_eq_transition_of_power_sum
  · apply div_nonneg _ (n04bRootCutRadius_pos hT).le
    exact Real.rpow_nonneg (by
      change 0 ≤ 3 * n04bTravelOrientation T side s / 2
      have := (n04b_travelOrientation_pos_of_fullStrip side hs).le
      positivity) _
  · exact n04NegativeInverse_normalizedRoot_power_sum hT hs side

/-- A small opposite-chart discrepancy traps both of its arguments in
the fixed middle band and keeps the target coordinate uniformly positive. -/
theorem n04NegativeInverse_normalized_coordinates_band
    {x y y₀ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : 0 ≤ y)
    (hxy : x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) = 2)
    (hy₀ : y₀ ≤ 1) (hclose : |y - y₀| ≤ 1 / 4) :
    x ∈ Icc (7 / 16 : ℝ) 1 ∧
      y ∈ Icc (1 : ℝ) (5 / 4) ∧ y₀ ∈ Icc (3 / 4 : ℝ) 1 := by
  have hxp : x ^ (3 / 2 : ℝ) < 1 :=
    Real.rpow_lt_one hx.1.le hx.2 (by norm_num)
  have hyp : (1 : ℝ) ^ (3 / 2 : ℝ) < y ^ (3 / 2 : ℝ) := by
    rw [Real.one_rpow]
    linarith
  have hy1 : 1 < y :=
    (Real.rpow_lt_rpow_iff (by norm_num) hy (by norm_num)).mp hyp
  have hdiff : y - y₀ ≤ 1 / 4 := (le_abs_self (y - y₀)).trans hclose
  have hyupper : y ≤ 5 / 4 := by linarith
  have hypupper : y ^ (3 / 2 : ℝ) ≤ 25 / 16 := by
    calc
      y ^ (3 / 2 : ℝ) ≤ (5 / 4 : ℝ) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hy hyupper (by norm_num)
      _ ≤ (5 / 4 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 25 / 16 := by norm_num [Real.rpow_two]
  have hxp_le : x ^ (3 / 2 : ℝ) ≤ x :=
    Real.rpow_le_self_of_le_one hx.1.le hx.2.le (by norm_num)
  exact ⟨⟨by linarith, hx.2.le⟩, ⟨hy1.le, hyupper⟩,
    ⟨by linarith, hy₀⟩⟩

/-- All segments used to compare the current and reference opposite
coordinates remain in the same fixed compact band. -/
theorem n04NegativeInverse_middle_segment
    {x y : ℝ} (hx : x ∈ Icc (3 / 4 : ℝ) (5 / 4))
    (hy : y ∈ Icc (3 / 4 : ℝ) (5 / 4))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) * x + t * y ∈ Icc (3 / 4 : ℝ) (5 / 4) := by
  exact (convex_Icc (3 / 4 : ℝ) (5 / 4)) hx hy
    (by linarith [ht.2]) ht.1 (by ring)

theorem n04NegativeInverse_middle_power_lt_two
    {x : ℝ} (hx : x ∈ Ioo (1 / 2 : ℝ) (4 / 3)) :
    x ^ (3 / 2 : ℝ) < 2 := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hp : x ^ (3 / 2 : ℝ) ≤ (4 / 3 : ℝ) ^ (2 : ℝ) :=
    (Real.rpow_le_rpow hx0.le hx.2.le (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  norm_num [Real.rpow_two] at hp
  linarith

theorem n04NegativeInverseRootTransition_pos
    {x : ℝ} (hx : x ∈ Ioo (1 / 2 : ℝ) (4 / 3)) :
    0 < n04NegativeInverseRootTransition x :=
  Real.rpow_pos_of_pos (sub_pos.mpr (n04NegativeInverse_middle_power_lt_two hx)) _

theorem n04NegativeInverseRootTransition_contDiffAt
    {x : ℝ} (hx : x ∈ Ioo (1 / 2 : ℝ) (4 / 3)) :
    ContDiffAt ℝ ∞ n04NegativeInverseRootTransition x := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  exact (contDiffAt_const.sub
    (Real.contDiffAt_rpow_const_of_ne hx0.ne')).rpow_const_of_ne
      (sub_pos.mpr (n04NegativeInverse_middle_power_lt_two hx)).ne'

theorem n04NegativeInverseRootTransition_contDiffOn :
    ContDiffOn ℝ ∞ n04NegativeInverseRootTransition
      (Ioo (1 / 2 : ℝ) (4 / 3)) :=
  fun _ hx => (n04NegativeInverseRootTransition_contDiffAt hx).contDiffWithinAt

theorem n04NegativeInverseHeightTransition_contDiffAt
    {x : ℝ} (hx : x ∈ Ioo (1 / 2 : ℝ) (4 / 3)) :
    ContDiffAt ℝ ∞ n04NegativeInverseHeightTransition x := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hratio : 0 < n04NegativeInverseRootTransition x / x :=
    div_pos (n04NegativeInverseRootTransition_pos hx) hx0
  exact ((((n04NegativeInverseRootTransition_contDiffAt hx).div
    contDiffAt_id hx0.ne').sqrt hratio.ne').sqrt
      (Real.sqrt_pos.mpr hratio).ne')

theorem n04NegativeInverseHeightTransition_contDiffOn :
    ContDiffOn ℝ ∞ n04NegativeInverseHeightTransition
      (Ioo (1 / 2 : ℝ) (4 / 3)) :=
  fun _ hx => (n04NegativeInverseHeightTransition_contDiffAt hx).contDiffWithinAt

theorem n04NegativeInverse_middle_iteratedDeriv_bound
    {f : ℝ → ℝ} (hf : ∀ x ∈ Ioo (1 / 2 : ℝ) (4 / 3), ContDiffAt ℝ ∞ f x)
    (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Icc (3 / 4 : ℝ) (5 / 4),
      |iteratedDeriv n f x| ≤ B := by
  have hc : ContinuousOn (fun x => |iteratedDeriv n f x|)
      (Icc (3 / 4 : ℝ) (5 / 4)) := by
    intro x hx
    have hs := hf x (show x ∈ Ioo (1 / 2 : ℝ) (4 / 3) from
        ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      (hs.continuousAt_iteratedFDeriv (k := n) (by simp)).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (3 / 4 : ℝ) (5 / 4))).bddAbove_image hc
  exact ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _),
    fun x hx => (hB ⟨x, hx, rfl⟩).trans (le_max_right _ _)⟩

/-- The transition's derivative constants are independent of the state,
component and side, because their arguments lie in one fixed compact band. -/
theorem n04NegativeInverseRootTransition_iteratedDeriv_bound (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Icc (3 / 4 : ℝ) (5 / 4),
      |iteratedDeriv n n04NegativeInverseRootTransition x| ≤ B :=
  n04NegativeInverse_middle_iteratedDeriv_bound
    (fun _ hx => n04NegativeInverseRootTransition_contDiffAt hx) n

theorem n04NegativeInverseHeightTransition_iteratedDeriv_bound (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Icc (3 / 4 : ℝ) (5 / 4),
      |iteratedDeriv n n04NegativeInverseHeightTransition x| ≤ B :=
  n04NegativeInverse_middle_iteratedDeriv_bound
    (fun _ hx => n04NegativeInverseHeightTransition_contDiffAt hx) n

theorem n04NegativeInverse_rootHeight_ratio
    {c r s : ℝ} (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) :
    (Real.sqrt (c / Real.sqrt r))⁻¹ =
      Real.sqrt (Real.sqrt (r / s)) * (Real.sqrt (c / Real.sqrt s))⁻¹ := by
  rw [Real.sqrt_div hc.le, Real.sqrt_div hc.le, Real.sqrt_div hr.le,
    Real.sqrt_div (Real.sqrt_nonneg r), inv_div, inv_div]
  field_simp [(Real.sqrt_pos.mpr hc).ne',
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hs)).ne']


namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- Complementarity holds for the literal stored charts on the whole
physical component, even if the point is outside one of its moving halves. -/
theorem negativeChart_normalizedRoot_power_sum (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    ((n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p).1 /
          n04bRootCutRadius (W.C.travel m)) ^ (3 / 2 : ℝ) +
      ((n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side) p).1 /
          n04bRootCutRadius (W.C.travel m)) ^ (3 / 2 : ℝ) = 2 := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field hw hs m
  have hp' := ((n04b_actualTravelChart_bijOn
    W.through03 W.hS W.hT W.field hw hs m).mapsTo hp).1
  rw [((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hw hs m side).component_chart_germ hp).self_of_nhds,
    ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hw hs m (!side)).component_chart_germ hp).self_of_nhds]
  exact n04NegativeInverse_normalizedRoot_power_sum hT hp' side

theorem negativeChart_normalizedRoot_transition (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p).1 /
      n04bRootCutRadius (W.C.travel m) =
    n04NegativeInverseRootTransition
      ((n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side) p).1 /
          n04bRootCutRadius (W.C.travel m)) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field hw hs m
  apply n04NegativeInverse_eq_transition_of_power_sum
  · apply div_nonneg _ (n04bRootCutRadius_pos hT).le
    rw [((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hw hs m side).component_chart_germ hp).self_of_nhds]
    exact (W.negativeRootChart_radial_pos m side hz hp).le
  · exact W.negativeChart_normalizedRoot_power_sum m side hz hp

/-- Both root charts retain precisely the same actual angular lift. -/
theorem negativeChart_opposite_angular_eq (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p).2 =
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side) p).2 := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  rw [((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hw hs m side).component_chart_germ hp).self_of_nhds,
    ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hw hs m (!side)).component_chart_germ hp).self_of_nhds]
  rfl

/-- The two actual heights differ by one fixed smooth scalar multiplier
of the opposite normalized radial coordinate. -/
theorem negativeHeight_opposite_transition (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    n04bActualNegativeHeight W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p =
      n04NegativeInverseHeightTransition
        ((n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m (!side) p).1 /
            n04bRootCutRadius (W.C.travel m)) *
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m (!side) p := by
  let w := liftSectorParameter W.S W.C z
  let F := n04bActualTravelChart W.S W.C W.L w m
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field hw hs m
  have hR := n04bRootCutRadius_pos hT
  have hside := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    hw hs m side
  have hopp := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    hw hs m (!side)
  have hr := W.negativeRootChart_radial_pos m side hz hp
  have ho := W.negativeRootChart_radial_pos m (!side) hz hp
  have hfactor : n04NegativeInverseHeightTransition
      ((n04bActualNegativeChart W.hT W.hS W.through03 W.field w m (!side) p).1 /
        n04bRootCutRadius (W.C.travel m)) =
      Real.sqrt (Real.sqrt
        ((n04bRootPhysicalChart F (W.C.travel m) side p).1 /
          (n04bRootPhysicalChart F (W.C.travel m) (!side) p).1)) := by
    unfold n04NegativeInverseHeightTransition
    rw [← W.negativeChart_normalizedRoot_transition m side hz hp,
      (hside.component_chart_germ hp).self_of_nhds,
      (hopp.component_chart_germ hp).self_of_nhds]
    congr 2
    exact div_div_div_cancel_right₀ hR.ne' _ _
  rw [hfactor, (hside.component_height_germ hp).self_of_nhds,
    (hopp.component_height_germ hp).self_of_nhds]
  exact n04NegativeInverse_rootHeight_ratio
    (mul_pos (W.field.positive_a w hw hs p
      (W.through03.1.1.negativeComponent_subset_annularOpen m hp))
      (n04b_actualCharacteristic_halfGap_pos W.through03 W.field hw hs m hp)) hr ho

/-- At the actual inverse, only the opposite chart's zeroth-order
reference discrepancy is needed to confine a crossing to the middle band. -/
theorem negativeInverse_overlap_band (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ))
    (y₀ : ℝ) (hy₀ : y₀ ≤ 1)
    (hclose : |(n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side)
        (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side q)).1 /
          n04bRootCutRadius (W.C.travel m) - y₀| ≤ 1 / 4) :
    q.1 / n04bRootCutRadius (W.C.travel m) ∈ Icc (7 / 16 : ℝ) 1 ∧
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side)
        (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side q)).1 /
          n04bRootCutRadius (W.C.travel m) ∈ Icc (1 : ℝ) (5 / 4) ∧
      y₀ ∈ Icc (3 / 4 : ℝ) 1 := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field hw hs m
  have hR := n04bRootCutRadius_pos hT
  have hp := W.negativeInverse_maps_component m side hz hq
  have hsum := W.negativeChart_normalizedRoot_power_sum m side hz hp
  rw [W.negativeInverse_right m side hz hq] at hsum
  apply n04NegativeInverse_normalized_coordinates_band
    ⟨div_pos hq.1.1 hR, (div_lt_one hR).mpr hq.1.2⟩ ?_ hsum hy₀ hclose
  apply div_nonneg _ hR.le
  rw [((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    hw hs m (!side)).component_chart_germ hp).self_of_nhds]
  exact (W.negativeRootChart_radial_pos m (!side) hz hp).le

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverse_overlap_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverse_overlap_band

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeInverseRootTransition_iteratedDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeInverseRootTransition_iteratedDeriv_bound
