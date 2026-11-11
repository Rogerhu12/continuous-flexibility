import ContinuousFlexibility.Geometry.CapDiskNormal
import ContinuousFlexibility.Contracts.GraphCylinderVolume
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The actual radial wall of the cap interior

The strictly dropping portion of the explicit meridian is inverted at every
height strictly between the bottom and top planes. Its radial coordinate is
therefore a genuine smooth function of physical height. This constructs the
wall used for the inside region; it does not assume an interior or an outward
orientation, and it does not assert that the analytic annular core exists.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem capHeightDrop_mem_open_iff (s : ℝ) :
    capHeightDrop s ∈ Ioo 0 capDrop ↔ s ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
  constructor
  · intro hs
    constructor
    · by_contra hn
      have he := capHeightDrop_eq_left (le_of_not_gt hn)
      linarith [hs.1]
    · by_contra hn
      have he := capHeightDrop_eq_right (le_of_not_gt hn)
      linarith [hs.2]
  · intro hs
    have hl := capHeightDrop_lt hs.1 (by norm_num : (1 / 4 : ℝ) < 3 / 4) hs.1
    have hr := capHeightDrop_lt hs.2 hs.2 (by norm_num : (1 / 4 : ℝ) < 3 / 4)
    simpa only [mem_Ioo, capHeightDrop_eq_left le_rfl, capHeightDrop_eq_right le_rfl] using And.intro hl hr

theorem exists_capHeightDrop_preimage {y : ℝ} (hy : y ∈ Ioo 0 capDrop) :
    ∃ s : ℝ, s ∈ Ioo (1 / 4 : ℝ) (3 / 4) ∧ capHeightDrop s = y := by
  have hy' : y ∈ Icc (capHeightDrop (1 / 4)) (capHeightDrop (3 / 4)) := by
    simpa only [capHeightDrop_eq_left le_rfl, capHeightDrop_eq_right le_rfl] using
      (show y ∈ Icc 0 capDrop from ⟨hy.1.le, hy.2.le⟩)
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
    contDiff_capHeightDrop.continuous.continuousOn hy'
  refine ⟨s, (capHeightDrop_mem_open_iff s).mp ?_, hs⟩
  simpa only [hs] using hy

def capHeightParameter (y : ℝ) : ℝ := Function.invFun capHeightDrop y

theorem capHeightDrop_parameter {y : ℝ} (hy : y ∈ Ioo 0 capDrop) :
    capHeightDrop (capHeightParameter y) = y := by
  obtain ⟨s, _, hs⟩ := exists_capHeightDrop_preimage hy
  exact Function.invFun_eq ⟨s, hs⟩

theorem capHeightParameter_mem {y : ℝ} (hy : y ∈ Ioo 0 capDrop) :
    capHeightParameter y ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
  apply (capHeightDrop_mem_open_iff _).mp
  simpa only [capHeightDrop_parameter hy] using hy

theorem capHeightParameter_drop {s : ℝ} (hs : s ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    capHeightParameter (capHeightDrop s) = s := by
  have hy := (capHeightDrop_mem_open_iff s).mpr hs
  have hi := capHeightParameter_mem hy
  exact strictMonoOn_capHeightDrop.injOn ⟨hi.1.le, hi.2.le⟩ ⟨hs.1.le, hs.2.le⟩
    (capHeightDrop_parameter hy)

private theorem eventually_capHeightParameter_drop {s : ℝ}
    (hs : s ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    ∀ᶠ t in 𝓝 s, capHeightParameter (capHeightDrop t) = t := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact capHeightParameter_drop ht

theorem hasStrictDerivAt_capHeightParameter_drop {s : ℝ}
    (hs : s ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    HasStrictDerivAt capHeightParameter (capDownwardVelocity s)⁻¹ (capHeightDrop s) := by
  have hd := contDiff_capHeightDrop.hasStrictDerivAt (x := s) (by simp)
  rw [(hasDerivAt_capHeightDrop s).deriv] at hd
  exact hd.to_local_left_inverse (capDownwardVelocity_pos hs).ne'
    (eventually_capHeightParameter_drop hs)

theorem contDiffAt_capHeightParameter_drop {s : ℝ}
    (hs : s ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    ContDiffAt ℝ ∞ capHeightParameter (capHeightDrop s) := by
  have h0 : deriv capHeightDrop s ≠ 0 := by
    rw [(hasDerivAt_capHeightDrop s).deriv]
    exact (capDownwardVelocity_pos hs).ne'
  let h := (contDiff_capHeightDrop.hasStrictDerivAt (x := s) (by simp)).hasStrictFDerivAt_equiv h0
  let e := h.toOpenPartialHomeomorph capHeightDrop
  have he : e.symm (capHeightDrop s) = s := h.localInverse_apply_image
  have hd : HasDerivAt e (deriv capHeightDrop s) (e.symm (capHeightDrop s)) := by
    rw [he]
    exact (hasDerivAt_capHeightDrop s).differentiableAt.hasDerivAt
  have hc : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (capHeightDrop s)) := by
    rw [he]
    exact contDiff_capHeightDrop.contDiffAt
  have hi := e.contDiffAt_symm_deriv h0 h.image_mem_toOpenPartialHomeomorph_target hd hc
  have heq : capHeightParameter =ᶠ[𝓝 (capHeightDrop s)] (e.symm : ℝ → ℝ) :=
    h.localInverse_unique (eventually_capHeightParameter_drop hs)
  exact hi.congr_of_eventuallyEq heq

theorem contDiffAt_capHeightParameter {y : ℝ} (hy : y ∈ Ioo 0 capDrop) :
    ContDiffAt ℝ ∞ capHeightParameter y := by
  have h := contDiffAt_capHeightParameter_drop (capHeightParameter_mem hy)
  simpa only [capHeightDrop_parameter hy] using h

theorem hasDerivAt_capHeightParameter {y : ℝ} (hy : y ∈ Ioo 0 capDrop) :
    HasDerivAt capHeightParameter (capDownwardVelocity (capHeightParameter y))⁻¹ y := by
  have h := (hasStrictDerivAt_capHeightParameter_drop (capHeightParameter_mem hy)).hasDerivAt
  simpa only [capHeightDrop_parameter hy] using h

def capWallRadius (R h L z : ℝ) : ℝ :=
  R + L * capRadialOffset (capHeightParameter ((h - z) / L))

theorem cap_normalized_height_mem {h L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) : (h - z) / L ∈ Ioo 0 capDrop := by
  exact ⟨div_pos (sub_pos.mpr hz.2) hL, (div_lt_iff₀ hL).mpr (by linarith [hz.1])⟩

theorem capWallRadius_gt {R h L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) : R < capWallRadius R h L z := by
  have hm := capHeightParameter_mem (cap_normalized_height_mem hL hz)
  have hp := capRadialOffset_pos (show capHeightParameter ((h - z) / L) ∈ Ioo 0 1 from
    ⟨by linarith [hm.1], by linarith [hm.2]⟩)
  dsimp only [capWallRadius]
  linarith [mul_pos hL hp]

theorem contDiffAt_capWallRadius (R h : ℝ) {L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) : ContDiffAt ℝ ∞ (capWallRadius R h L) z := by
  have hi := (contDiffAt_capHeightParameter (cap_normalized_height_mem hL hz)).comp z
    ((contDiff_const.sub contDiff_id).div_const L).contDiffAt
  exact contDiffAt_const.add (contDiffAt_const.mul (contDiff_capRadialOffset.contDiffAt.comp z hi))

theorem capWallRadius_at_meridian (R h : ℝ) {L s : ℝ} (hL : 0 < L)
    (hs : s / L ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    capWallRadius R h L (capMeridianHeight h L s) = capMeridianRadius R L s := by
  have he : (h - capMeridianHeight h L s) / L = capHeightDrop (s / L) := by
    unfold capMeridianHeight
    field_simp [hL.ne']
    ring
  simp only [capWallRadius, he, capHeightParameter_drop hs, capMeridianRadius]

theorem hasDerivAt_capWallRadius (R h : ℝ) {L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) :
    HasDerivAt (capWallRadius R h L)
      (-capRadialVelocity (capHeightParameter ((h - z) / L)) /
        capDownwardVelocity (capHeightParameter ((h - z) / L))) z := by
  have hn := ((hasDerivAt_const z h).sub (hasDerivAt_id z)).div_const L
  have hi := (hasDerivAt_capHeightParameter (cap_normalized_height_mem hL hz)).comp z hn
  have hr := (hasDerivAt_capRadialOffset _).comp z hi
  convert! (hr.const_mul L).const_add R using 1
  simp only [Function.comp_apply, Pi.sub_apply, id_eq]
  field_simp [hL.ne']
  ring

theorem capRadialOffset_le_self {s : ℝ} (hs : 0 ≤ s) : capRadialOffset s ≤ s := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hs
    (contDiff_capRadialVelocity.continuous.intervalIntegrable 0 s)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 s)
    (fun t _ => (show capRadialVelocity t ≤ 1 from Real.cos_le_one _))
  simpa only [capRadialOffset, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hi

theorem capWallRadius_le {R h L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) : capWallRadius R h L z ≤ R + L := by
  have hm := capHeightParameter_mem (cap_normalized_height_mem hL hz)
  have ho := capRadialOffset_le_self (show 0 ≤ capHeightParameter ((h - z) / L) by linarith [hm.1])
  have hh : capRadialOffset (capHeightParameter ((h - z) / L)) ≤ 1 := by linarith [hm.2]
  dsimp only [capWallRadius]
  linarith [mul_le_mul_of_nonneg_left hh hL.le]

/-- The actual solid bounded by the unmarked meridian cap and its flat top. -/
def capRevolutionInterior (R h L : ℝ) : Set E3 :=
  {v | v 2 ∈ Ioo (h - L * capDrop) h ∧
    cartesianRadius (graphBaseProjection v) < capWallRadius R h L (v 2)}

theorem isOpen_capRevolutionInterior (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    IsOpen (capRevolutionInterior R h L) := by
  apply isOpen_iff_mem_nhds.mpr
  intro v hv
  have hp : Continuous (fun u : E3 => u 2) := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hh : ∀ᶠ u in 𝓝 v, u 2 ∈ Ioo (h - L * capDrop) h :=
    hp.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hv.1)
  have hw : ContinuousAt (fun u : E3 => capWallRadius R h L (u 2)) v :=
    ContinuousAt.comp (f := fun u : E3 => u 2) (x := v)
      (contDiffAt_capWallRadius R h hL hv.1).continuousAt hp.continuousAt
  have hr := (continuous_cartesianRadius.comp continuous_graphBaseProjection).continuousAt.eventually_lt hw hv.2
  filter_upwards [hh, hr] with u hu hru
  exact ⟨hu, hru⟩

theorem capRevolutionInterior_subset_compact (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ K : Set E3, IsCompact K ∧ capRevolutionInterior R h L ⊆ K := by
  let K := euclideanVectorOfCoordinates ''
    ({x : PolarPoint | cartesianRadius x ≤ R + L} ×ˢ Icc (h - L * capDrop) h)
  refine ⟨K, ((isCompact_closedCartesianDisk (R + L)).prod isCompact_Icc).image
    continuous_euclideanVectorOfCoordinates, ?_⟩
  intro v hv
  exact ⟨(graphBaseProjection v, v 2),
    ⟨hv.2.le.trans (capWallRadius_le hL hv.1), hv.1.1.le, hv.1.2.le⟩,
    euclideanVectorOfCoordinates_of_vector v⟩

theorem capRevolutionInterior_volume_lt_top (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    volume (capRevolutionInterior R h L) < ⊤ := by
  obtain ⟨K, hK, hsub⟩ := capRevolutionInterior_subset_compact R h hL
  exact (measure_mono hsub).trans_lt hK.measure_lt_top

theorem capRevolutionInterior_volume_pos {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    0 < volume (capRevolutionInterior R h L) := by
  apply (isOpen_capRevolutionInterior R h hL).measure_pos volume
  let z := h - L * capDrop / 2
  have hz : z ∈ Ioo (h - L * capDrop) h := by
    dsimp only [z]
    have hp := mul_pos hL capDrop_pos
    constructor <;> linarith
  refine ⟨euclideanVectorOfCoordinates (0, z), ?_⟩
  have hb : graphBaseProjection (euclideanVectorOfCoordinates (0, z)) = 0 := by
    simp [euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]
  have hv : euclideanVectorOfCoordinates (0, z) 2 = z := by
    simp [euclideanVectorOfCoordinates, e3Basis]
  change euclideanVectorOfCoordinates (0, z) 2 ∈ Ioo (h - L * capDrop) h ∧ _
  rw [hv, hb]
  exact ⟨hz, by simpa [cartesianRadius] using hR.trans (capWallRadius_gt hL hz)⟩

end ContinuousFlexibility
