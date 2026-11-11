import ContinuousFlexibility.Radial.SelectedRetainedCone
import ContinuousFlexibility.Radial.SeedGluedPairConstruction
import ContinuousFlexibility.Radial.SelectedReferenceTransport

/-! # One actually glued pair retaining both long selected first cones -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

structure SeedRetainedPair (S : SelectedTailData) (K : SeedCentralCutoff)
    (q length : ℝ) where
  left : SeedRetainedFirstCone S false length
  right : SeedRetainedFirstCone S true length
  pair : SeedGluedPair (S.family S.sigma)
    (S.cut false S.chain.index) (S.cut true S.chain.index) left.natural right.natural K q
  left_germ : ∀ r, 0 < r → r ≤ pair.radiusL * left.tail.cut →
    pair.profile =ᶠ[𝓝 r] seedRescale pair.radiusL (pair.heightL * pair.radiusL) left.tail.profile ∧
    pair.height =ᶠ[𝓝 r] seedRescale pair.radiusL pair.amplitudeL left.tail.height
  right_germ : ∀ r, pair.radiusR * right.tail.cut ≤ r →
    pair.profile =ᶠ[𝓝 r] seedRescale pair.radiusR (pair.heightR * pair.radiusR) right.tail.profile ∧
    pair.height =ᶠ[𝓝 r] seedRescale pair.radiusR pair.amplitudeR right.tail.height
  left_before : pair.radiusL * left.tail.cut < exp (K.left - q - 4)
  right_after : exp (K.right + q + 4) < pair.radiusR * right.tail.cut
  left_logSlope_lower : ∀ r ∈ Icc (pair.radiusL * S.cut false S.chain.index) (exp K.left),
    (3 / 4 : ℝ) * pair.profile r ≤ r * deriv pair.profile r
  right_logSlope_lower : ∀ r ∈ Icc (exp K.right) (pair.radiusR * S.cut true S.chain.index),
    (3 / 4 : ℝ) * pair.profile r ≤ r * deriv pair.profile r

theorem exists_seedRetainedPair {S : SelectedTailData} (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (K : SeedCentralCutoff) {q length : ℝ} (hq : 0 < q) (hlength : 0 < length) :
    Nonempty (SeedRetainedPair S K q length) := by
  obtain ⟨L⟩ := exists_seedRetainedFirstCone hS hband false hlength
  obtain ⟨R⟩ := exists_seedRetainedFirstCone hS hband true hlength
  have hD : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hL := hS.2.2.2.2.2 false S.chain.index 2 le_rfl (by decide) hband
  have hR := hS.2.2.2.2.2 true S.chain.index 2 le_rfl (by decide) hband
  obtain ⟨G, hGL, hGR, hbefore, hafter, _, _, hLLower, hRLower⟩ :=
    exists_seedGluedPair_retaining_logSlope hD hL.1 hR.1
    L.tail R.tail (by simpa using L.canonical) (by simpa using R.canonical) K hq
  exact ⟨⟨L, R, G, hGL, hGR, hbefore, hafter,
    hLLower L.logSlope_inward, hRLower R.logSlope_inward⟩⟩

/-- Both physical connecting gaps have the same lower bound, independent
of the retained logarithmic length and all radius and height rescalings. -/
theorem SeedRetainedPair.gap_logSlope_lower {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {r : ℝ}
    (hr : r ∈ Icc (P.pair.radiusL * S.cut false S.chain.index) (exp K.left) ∪
      Icc (exp K.right) (P.pair.radiusR * S.cut true S.chain.index)) :
    (3 / 4 : ℝ) * P.pair.profile r ≤ r * deriv P.pair.profile r :=
  hr.elim (P.left_logSlope_lower r) (P.right_logSlope_lower r)

private theorem seed_selected_first_cut_entry_order {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (right : Bool) :
    if right then S.cut right S.chain.index < S.entry right S.chain.index
      else S.entry right S.chain.index < S.cut right S.chain.index := by
  have h := (hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.1
  cases right <;> exact h.1.trans h.2

/-- Reindex the same glued functions by the original selected entrances.
Only the bookkeeping changes; the actual old cut-to-entry intervals remain. -/
def SeedRetainedPair.toEntryPair {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (T : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) :
    SeedGluedPair (S.family S.sigma)
      (S.entry false S.chain.index) (S.entry true S.chain.index)
      (S.outgoing false 2) (S.outgoing true 2) K q where
  profile := T.pair.profile
  height := T.pair.height
  radiusL := T.pair.radiusL
  radiusR := T.pair.radiusR
  heightL := T.pair.heightL
  heightR := T.pair.heightR
  amplitudeL := T.pair.amplitudeL
  amplitudeR := T.pair.amplitudeR
  radiusL_pos := T.pair.radiusL_pos
  radius_order := T.pair.radius_order
  heightL_pos := T.pair.heightL_pos
  heightR_pos := T.pair.heightR_pos
  amplitudeL_ne := T.pair.amplitudeL_ne
  amplitudeR_ne := T.pair.amplitudeR_ne
  geometry := T.pair.geometry
  equation := T.pair.equation
  left_entry := (mul_lt_mul_of_pos_left (seed_selected_first_cut_entry_order hS hband false)
    T.pair.radiusL_pos).trans T.pair.left_entry
  right_entry := T.pair.right_entry.trans (mul_lt_mul_of_pos_left
    (seed_selected_first_cut_entry_order hS hband true)
    (T.pair.radiusL_pos.trans_le T.pair.radius_order))
  middle_germ := T.pair.middle_germ
  left_tail := by
    intro r hr
    have ht := T.pair.left_tail r ⟨hr.1,
      hr.2.trans (seed_selected_first_cut_entry_order hS hband false)⟩
    refine ⟨ht.1, ht.2.trans ?_⟩
    rw [T.left.natural_retained hr]
  right_tail := by
    intro r hr
    have ht := T.pair.right_tail r
      ⟨(seed_selected_first_cut_entry_order hS hband true).trans hr.1, hr.2⟩
    refine ⟨ht.1, ht.2.trans ?_⟩
    rw [T.right.natural_retained hr]

@[simp] theorem SeedRetainedPair.toEntryPair_profile {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (T : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) :
    (T.toEntryPair hS hband).profile = T.pair.profile := rfl

@[simp] theorem SeedRetainedPair.toEntryPair_height {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (T : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) :
    (T.toEntryPair hS hband).height = T.pair.height := rfl

theorem seedRescale_eq_radialRadiusScale (R A : ℝ) (f : ℝ → ℝ) :
    seedRescale R A f = radialRadiusScale R A f := by
  funext r
  unfold seedRescale radialRadiusScale
  rw [div_eq_mul_inv, mul_comm r R⁻¹]

theorem SeedRetainedPair.left_profile_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length r : ℝ} (T : SeedRetainedPair S K q length)
    (hr : 0 < r) (hi : r ≤ T.left.inner) :
    T.pair.profile =ᶠ[𝓝 (T.pair.radiusL * r)]
      radialRadiusScale T.pair.radiusL (T.pair.heightL * T.pair.radiusL) T.left.tail.profile := by
  rw [← seedRescale_eq_radialRadiusScale]
  exact (T.left_germ _ (mul_pos T.pair.radiusL_pos hr)
    (mul_le_mul_of_nonneg_left (hi.trans T.left.pure_cut.le) T.pair.radiusL_pos.le)).1

theorem SeedRetainedPair.right_profile_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length r : ℝ} (T : SeedRetainedPair S K q length)
    (hi : T.right.inner ≤ r) :
    T.pair.profile =ᶠ[𝓝 (T.pair.radiusR * r)]
      radialRadiusScale T.pair.radiusR (T.pair.heightR * T.pair.radiusR) T.right.tail.profile := by
  rw [← seedRescale_eq_radialRadiusScale]
  exact (T.right_germ _ (mul_le_mul_of_nonneg_left (T.right.pure_cut.le.trans hi)
    (T.pair.radiusL_pos.trans_le T.pair.radius_order).le)).1

/-- The cone coefficient transforms by profile height only. This is a
germ identity, so it also fixes every coefficient derivative used by the lift. -/
theorem radialRadiusScale_cone_germ {w : ℝ → ℝ} {κ β C r : ℝ}
    (hκ : κ ≠ 0) (hw : w =ᶠ[𝓝 r] (fun t => C * t)) :
    radialRadiusScale κ (β * κ) w =ᶠ[𝓝 (κ * r)] (fun t => (β * C) * t) := by
  have he : κ * r / κ = r := by field_simp [hκ] <;> ring
  have ht : Tendsto (fun t : ℝ => t / κ) (𝓝 (κ * r)) (𝓝 r) := by
    simpa only [id_eq, he] using (continuous_id.div_const κ).tendsto (κ * r)
  filter_upwards [hw.comp_tendsto ht] with t h
  change (β * κ) * w (t / κ) = (β * C) * t
  change w (t / κ) = C * (t / κ) at h
  rw [h]
  field_simp [hκ]
  <;> ring

end ContinuousFlexibility.Radial
