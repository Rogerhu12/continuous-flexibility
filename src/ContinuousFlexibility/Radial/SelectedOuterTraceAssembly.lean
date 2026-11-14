module

public import ContinuousFlexibility.Radial.SelectedTailRegularResponse
public import ContinuousFlexibility.Radial.MatchingTraceCalculus

/-!
# Gluing the two one-sided representatives and their frozen traces

The representative switches only in the omitted middle interval. Near
either cut it is exactly that side's constructed representative. The
within-derivative in the frozen outer flux therefore equals the derivative
on the correct physical half-closed tail.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def radialOuterGlue (l h : ℝ) (uL uR : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r < (l + h) / 2 then uL r else uR r

theorem radialOuterGlue_left_germ {l h r : ℝ} (hlh : l < h) (hr : r ≤ l)
    (uL uR : ℝ → ℝ) : radialOuterGlue l h uL uR =ᶠ[𝓝 r] uL := by
  filter_upwards [Iio_mem_nhds (show r < (l + h) / 2 by linarith)] with x hx
  exact if_pos hx

theorem radialOuterGlue_right_germ {l h r : ℝ} (hlh : l < h) (hr : h ≤ r)
    (uL uR : ℝ → ℝ) : radialOuterGlue l h uL uR =ᶠ[𝓝 r] uR := by
  filter_upwards [Ioi_mem_nhds (show (l + h) / 2 < r by linarith)] with x hx
  exact if_neg (not_lt.mpr hx.le)

theorem radialOuterGlue_contDiffOn {a b l h : ℝ} (hlh : l < h)
    {uL uR : ℝ → ℝ} (hL : ContDiffOn ℝ 1 uL (Ioc a l))
    (hR : ContDiffOn ℝ 1 uR (Ico h b)) :
    ContDiffOn ℝ 1 (radialOuterGlue l h uL uR) (Ioc a l ∪ Ico h b) := by
  intro r hr
  rcases hr with hr | hr
  · have hmem : Ioc a l ∈ 𝓝[Ioc a l ∪ Ico h b] r := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (hr.2.trans_lt hlh)),
        self_mem_nhdsWithin] with x hx hxs
      rcases hxs with hxs | hxs
      · exact hxs
      · exact False.elim ((not_lt.mpr hxs.1) hx)
    have he := radialOuterGlue_left_germ hlh hr.2 uL uR
    exact ((hL r hr).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds
  · have hmem : Ico h b ∈ 𝓝[Ioc a l ∪ Ico h b] r := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (hlh.trans_le hr.1)),
        self_mem_nhdsWithin] with x hx hxs
      rcases hxs with hxs | hxs
      · exact False.elim ((not_lt.mpr hxs.2) hx)
      · exact hxs
    have he := radialOuterGlue_right_germ hlh hr.1 uL uR
    exact ((hR r hr).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds

theorem matchingOuterFlux_eq_tailHalf {D : ReferenceData} {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b)) (right : Bool) :
    let i : Fin 2 := if right then 1 else 0
    matchingOuterFlux D M u i =
      outerTailSign right * D.w (matchingCut D M i) *
        derivWithin u (radialTailHalf D right (matchingCut D M i)) (matchingCut D M i) /
          sqrt (M.boundaryScale i) := by
  let i : Fin 2 := if right then 1 else 0
  have hcut := matchingCut_mem_core_of_geometry ha hm hb i
  have hsub : radialTailHalf D right (matchingCut D M i) ⊆
      closure (matchingOuterRegion D M) := by
    rw [matchingOuterRegion_closure ha hb]
    intro r hr
    cases right
    · exact Or.inl ⟨hr.1.le, hr.2⟩
    · exact Or.inr ⟨hr.1, hr.2.le⟩
  have he := derivWithin_subset hsub
    ((radialTailHalf_uniqueDiff D right (matchingCut D M i)).uniqueDiffWithinAt
      (radialTailHalf_cut hcut)) (matchingOuter_differentiableWithinAt ha hm hb hu i)
  change bufferSign i * D.w (matchingCut D M i) *
      derivWithin u (closure (matchingOuterRegion D M)) (matchingCut D M i) / _ = _
  rw [← he]
  have hs : bufferSign i = outerTailSign right := by
    cases right <;> norm_num [i, bufferSign, outerTailSign]
  rw [hs]

theorem outerRobin_sqrt_iff {lam : ℝ} (hlam : 0 < lam)
    (v : ℝ × ℝ) (x z : ℝ) :
    outerStatePair v (x, z / lam) = 0 ↔
      v.1 * sqrt lam * x + v.2 * z / sqrt lam = 0 := by
  have hs := (sqrt_pos.mpr hlam).ne'
  have hd : sqrt lam * (z / lam) = z / sqrt lam := by
    calc
      _ = (sqrt lam * z) / (sqrt lam * sqrt lam) := by
        rw [mul_self_sqrt hlam.le, mul_div_assoc]
      _ = _ := mul_div_mul_left _ _ hs
  have he : v.1 * sqrt lam * x + v.2 * z / sqrt lam =
      sqrt lam * outerStatePair v (x, z / lam) := by
    calc
      _ = sqrt lam * (v.1 * x) + v.2 * (sqrt lam * (z / lam)) := by
        rw [hd]
        ring
      _ = _ := by simp only [outerStatePair]; ring
  rw [he, mul_eq_zero]
  simp only [hs, false_or]

end ContinuousFlexibility.Radial
