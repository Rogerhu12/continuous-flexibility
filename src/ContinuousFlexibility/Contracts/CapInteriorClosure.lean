module

public import ContinuousFlexibility.Contracts.CapInteriorProfile
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# A continuous closed-height extension of the actual cap wall

The closed strictly monotone part of the actual height-drop function has a
genuine compact-interval homeomorphic inverse. Clamping to its image gives a
continuous total inverse, including the two end heights where the unconstrained
`invFun` need not select the limiting point of a plateau. The resulting wall
agrees with the actual interior wall at every strict interior height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

def capHeightDropClosedMap (s : Icc (1 / 4 : ℝ) (3 / 4)) : Icc (0 : ℝ) capDrop :=
  ⟨capHeightDrop s, by
    have hl := monotone_capHeightDrop s.2.1
    have hr := monotone_capHeightDrop s.2.2
    rw [capHeightDrop_eq_left le_rfl] at hl
    rw [capHeightDrop_eq_right le_rfl] at hr
    exact ⟨hl, hr⟩⟩

theorem bijective_capHeightDropClosedMap : Function.Bijective capHeightDropClosedMap := by
  constructor
  · intro s t h
    apply Subtype.ext
    exact strictMonoOn_capHeightDrop.injOn s.2 t.2 (congrArg Subtype.val h)
  · intro y
    have hy : (y : ℝ) ∈ Icc (capHeightDrop (1 / 4)) (capHeightDrop (3 / 4)) := by
      simpa only [capHeightDrop_eq_left le_rfl, capHeightDrop_eq_right le_rfl] using y.2
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
      contDiff_capHeightDrop.continuous.continuousOn hy
    exact ⟨⟨s, hs⟩, Subtype.ext he⟩

def capHeightDropClosedEquiv : Icc (1 / 4 : ℝ) (3 / 4) ≃ Icc (0 : ℝ) capDrop :=
  Equiv.ofBijective capHeightDropClosedMap bijective_capHeightDropClosedMap

theorem continuous_capHeightDropClosedEquiv :
    Continuous (capHeightDropClosedEquiv : Icc (1 / 4 : ℝ) (3 / 4) → Icc (0 : ℝ) capDrop) :=
  (contDiff_capHeightDrop.continuous.comp continuous_subtype_val).subtype_mk _

def capHeightDropClosedHomeomorph : Icc (1 / 4 : ℝ) (3 / 4) ≃ₜ Icc (0 : ℝ) capDrop :=
  continuous_capHeightDropClosedEquiv.homeoOfEquivCompactToT2

def capClampedDrop (y : ℝ) : Icc (0 : ℝ) capDrop :=
  ⟨max 0 (min capDrop y), le_max_left _ _,
    max_le capDrop_pos.le (min_le_left _ _)⟩

theorem continuous_capClampedDrop : Continuous capClampedDrop :=
  (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

def capClosedHeightParameter (y : ℝ) : ℝ :=
  (capHeightDropClosedHomeomorph.symm (capClampedDrop y)).1

theorem continuous_capClosedHeightParameter : Continuous capClosedHeightParameter :=
  continuous_subtype_val.comp (capHeightDropClosedHomeomorph.symm.continuous.comp
    continuous_capClampedDrop)

theorem capClosedHeightParameter_mem (y : ℝ) :
    capClosedHeightParameter y ∈ Icc (1 / 4 : ℝ) (3 / 4) :=
  (capHeightDropClosedHomeomorph.symm (capClampedDrop y)).2

theorem capHeightDrop_closedParameter {y : ℝ} (hy : y ∈ Icc 0 capDrop) :
    capHeightDrop (capClosedHeightParameter y) = y := by
  have he := congrArg Subtype.val (capHeightDropClosedHomeomorph.apply_symm_apply (capClampedDrop y))
  change capHeightDrop (capClosedHeightParameter y) = max 0 (min capDrop y) at he
  simpa only [min_eq_right hy.2, max_eq_right hy.1] using he

theorem capClosedHeightParameter_eq {y : ℝ} (hy : y ∈ Ioo 0 capDrop) :
    capClosedHeightParameter y = capHeightParameter y := by
  have hm := capHeightParameter_mem hy
  apply strictMonoOn_capHeightDrop.injOn (capClosedHeightParameter_mem y) ⟨hm.1.le, hm.2.le⟩
  rw [capHeightDrop_closedParameter ⟨hy.1.le, hy.2.le⟩, capHeightDrop_parameter hy]

@[simp] theorem capClosedHeightParameter_zero : capClosedHeightParameter 0 = 1 / 4 := by
  apply strictMonoOn_capHeightDrop.injOn (capClosedHeightParameter_mem 0)
    (show (1 / 4 : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) by norm_num)
  rw [capHeightDrop_closedParameter ⟨le_rfl, capDrop_pos.le⟩, capHeightDrop_eq_left le_rfl]

@[simp] theorem capClosedHeightParameter_capDrop : capClosedHeightParameter capDrop = 3 / 4 := by
  apply strictMonoOn_capHeightDrop.injOn (capClosedHeightParameter_mem capDrop)
    (show (3 / 4 : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) by norm_num)
  rw [capHeightDrop_closedParameter ⟨capDrop_pos.le, le_rfl⟩, capHeightDrop_eq_right le_rfl]

def capExtendedWallRadius (R h L z : ℝ) : ℝ :=
  R + L * capRadialOffset (capClosedHeightParameter ((h - z) / L))

theorem continuous_capExtendedWallRadius (R h L : ℝ) :
    Continuous (capExtendedWallRadius R h L) :=
  continuous_const.add (continuous_const.mul (contDiff_capRadialOffset.continuous.comp
    (continuous_capClosedHeightParameter.comp ((continuous_const.sub continuous_id).div_const L))))

theorem capExtendedWallRadius_eq {R h L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) :
    capExtendedWallRadius R h L z = capWallRadius R h L z := by
  simp only [capExtendedWallRadius, capWallRadius,
    capClosedHeightParameter_eq (cap_normalized_height_mem hL hz)]

@[simp] theorem capExtendedWallRadius_top (R h L : ℝ) :
    capExtendedWallRadius R h L h = R + L / 4 := by
  simp only [capExtendedWallRadius, sub_self, zero_div, capClosedHeightParameter_zero,
    capRadialOffset_eq_left le_rfl]
  ring

theorem capExtendedWallRadius_bottom (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    capExtendedWallRadius R h L (h - L * capDrop) = R + L / 4 := by
  have he : (h - (h - L * capDrop)) / L = capDrop := by field_simp [hL.ne']; ring
  rw [capExtendedWallRadius, he, capClosedHeightParameter_capDrop, capRadialOffset_eq_right le_rfl]
  ring

theorem capExtendedWallRadius_gt (R h : ℝ) {L : ℝ} (hL : 0 < L) (z : ℝ) :
    R < capExtendedWallRadius R h L z := by
  have hm := capClosedHeightParameter_mem ((h - z) / L)
  have hp := capRadialOffset_pos
    (show capClosedHeightParameter ((h - z) / L) ∈ Ioo 0 1 from
      ⟨by linarith [hm.1], by linarith [hm.2]⟩)
  dsimp only [capExtendedWallRadius]
  linarith [mul_pos hL hp]

theorem closure_capRevolutionInterior_subset (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    closure (capRevolutionInterior R h L) ⊆
      {v | v 2 ∈ Icc (h - L * capDrop) h ∧
        cartesianRadius (graphBaseProjection v) ≤ capExtendedWallRadius R h L (v 2)} := by
  have hz : Continuous (fun v : E3 => v 2) := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  apply closure_minimal
  · intro v hv
    refine ⟨⟨hv.1.1.le, hv.1.2.le⟩, ?_⟩
    rw [capExtendedWallRadius_eq hL hv.1]
    exact hv.2.le
  · exact (isClosed_Icc.preimage hz).inter (isClosed_le
      (continuous_cartesianRadius.comp continuous_graphBaseProjection)
      ((continuous_capExtendedWallRadius R h L).comp hz))

def euclideanCoordinatesHomeomorph : E3 ≃ₜ PolarPoint × ℝ where
  toFun := fun v => (graphBaseProjection v, v 2)
  invFun := euclideanVectorOfCoordinates
  left_inv := euclideanVectorOfCoordinates_of_vector
  right_inv := by
    intro q
    apply Prod.ext
    · apply Prod.ext <;> simp [euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]
    · simp [euclideanVectorOfCoordinates, e3Basis]
  continuous_toFun := continuous_graphBaseProjection.prodMk
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  continuous_invFun := continuous_euclideanVectorOfCoordinates

/-- A positive continuous horizontal radius straightens to a unit cylinder.
No differentiability at the end heights is required. -/
def horizontalRadiusHomeomorph (w : ℝ → ℝ) (hc : Continuous w) (hw : ∀ z, 0 < w z) :
    (PolarPoint × ℝ) ≃ₜ (PolarPoint × ℝ) where
  toFun := fun q => ((w q.2)⁻¹ • q.1, q.2)
  invFun := fun q => (w q.2 • q.1, q.2)
  left_inv := by
    intro q
    apply Prod.ext
    · simp only [smul_smul, mul_inv_cancel₀ (hw q.2).ne', one_smul]
    · rfl
  right_inv := by
    intro q
    apply Prod.ext
    · simp only [smul_smul, inv_mul_cancel₀ (hw q.2).ne', one_smul]
    · rfl
  continuous_toFun := (((hc.comp continuous_snd).inv₀
    (fun q => (hw q.2).ne')).smul continuous_fst).prodMk continuous_snd
  continuous_invFun := ((hc.comp continuous_snd).smul continuous_fst).prodMk continuous_snd

def capCylinderHomeomorph {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    E3 ≃ₜ PolarPoint × ℝ :=
  euclideanCoordinatesHomeomorph.trans (horizontalRadiusHomeomorph
    (capExtendedWallRadius R h L) (continuous_capExtendedWallRadius R h L)
    (fun z => hR.trans (capExtendedWallRadius_gt R h hL z)))

theorem capRevolutionInterior_eq_preimage_cylinder {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    capRevolutionInterior R h L = (capCylinderHomeomorph hR hL h) ⁻¹'
      ({x : PolarPoint | cartesianRadius x < 1} ×ˢ Ioo (h - L * capDrop) h) := by
  ext v
  have hw : 0 < capExtendedWallRadius R h L (v 2) :=
    hR.trans (capExtendedWallRadius_gt R h hL (v 2))
  have he : cartesianRadius ((capExtendedWallRadius R h L (v 2))⁻¹ • graphBaseProjection v) < 1 ↔
      cartesianRadius (graphBaseProjection v) < capExtendedWallRadius R h L (v 2) := by
    rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hw), inv_mul_eq_div, div_lt_one hw]
  change (v 2 ∈ Ioo (h - L * capDrop) h ∧
    cartesianRadius (graphBaseProjection v) < capWallRadius R h L (v 2)) ↔
      (cartesianRadius ((capExtendedWallRadius R h L (v 2))⁻¹ • graphBaseProjection v) < 1 ∧
        v 2 ∈ Ioo (h - L * capDrop) h)
  rw [he]
  constructor
  · rintro ⟨hz, hr⟩
    exact ⟨by simpa only [capExtendedWallRadius_eq hL hz] using hr, hz⟩
  · rintro ⟨hr, hz⟩
    exact ⟨hz, by simpa only [capExtendedWallRadius_eq hL hz] using hr⟩

theorem closure_openCartesianUnitDisk :
    closure {x : PolarPoint | cartesianRadius x < 1} = {x | cartesianRadius x ≤ 1} := by
  have hc := Complex.equivRealProdCLM.symm.toHomeomorph.preimage_closure (Metric.ball (0 : ℂ) 1)
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hc
  have hb : Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' Metric.ball (0 : ℂ) 1 =
      {x : PolarPoint | cartesianRadius x < 1} := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
    rfl
  have hd : Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' Metric.closedBall (0 : ℂ) 1 =
      {x : PolarPoint | cartesianRadius x ≤ 1} := by
    ext x
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rfl
  simpa only [hb, hd] using hc.symm

theorem closure_capRevolutionInterior {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    closure (capRevolutionInterior R h L) =
      {v | v 2 ∈ Icc (h - L * capDrop) h ∧
        cartesianRadius (graphBaseProjection v) ≤ capExtendedWallRadius R h L (v 2)} := by
  have hbottom : h - L * capDrop < h := by linarith [mul_pos hL capDrop_pos]
  rw [capRevolutionInterior_eq_preimage_cylinder hR hL h,
    ← (capCylinderHomeomorph hR hL h).preimage_closure,
    closure_prod_eq, closure_openCartesianUnitDisk, closure_Ioo hbottom.ne]
  ext v
  have hw : 0 < capExtendedWallRadius R h L (v 2) :=
    hR.trans (capExtendedWallRadius_gt R h hL (v 2))
  change (cartesianRadius ((capExtendedWallRadius R h L (v 2))⁻¹ • graphBaseProjection v) ≤ 1 ∧
    v 2 ∈ Icc (h - L * capDrop) h) ↔ _
  rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hw), inv_mul_eq_div, div_le_one hw]
  exact and_comm

theorem frontier_capRevolutionInterior {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    frontier (capRevolutionInterior R h L) =
      {v | v 2 ∈ Icc (h - L * capDrop) h ∧
        cartesianRadius (graphBaseProjection v) ≤ capExtendedWallRadius R h L (v 2) ∧
        (v 2 = h - L * capDrop ∨ v 2 = h ∨
          cartesianRadius (graphBaseProjection v) = capExtendedWallRadius R h L (v 2))} := by
  rw [frontier, (isOpen_capRevolutionInterior R h hL).interior_eq,
    closure_capRevolutionInterior hR hL h]
  ext v
  constructor
  · rintro ⟨⟨hz, hr⟩, hn⟩
    refine ⟨hz, hr, ?_⟩
    by_cases hb : v 2 = h - L * capDrop
    · exact Or.inl hb
    by_cases ht : v 2 = h
    · exact Or.inr (Or.inl ht)
    refine Or.inr (Or.inr ?_)
    by_contra hrad
    have hzo : v 2 ∈ Ioo (h - L * capDrop) h :=
      ⟨lt_of_le_of_ne hz.1 (Ne.symm hb), lt_of_le_of_ne hz.2 ht⟩
    apply hn
    refine ⟨hzo, ?_⟩
    rw [← capExtendedWallRadius_eq hL hzo]
    exact lt_of_le_of_ne hr hrad
  · rintro ⟨hz, hr, hs⟩
    refine ⟨⟨hz, hr⟩, fun hv => ?_⟩
    rcases hs with hb | ht | he
    · exact hv.1.1.ne' hb
    · exact hv.1.2.ne ht
    · have hh : cartesianRadius (graphBaseProjection v) < capExtendedWallRadius R h L (v 2) := by
        simpa only [capExtendedWallRadius_eq hL hv.1] using hv.2
      exact hh.ne he

end ContinuousFlexibility
