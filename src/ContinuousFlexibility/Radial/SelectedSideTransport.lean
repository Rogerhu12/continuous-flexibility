import ContinuousFlexibility.Radial.SeedRetainedReference
import ContinuousFlexibility.Radial.SelectedFirstConeLift

/-! # One side of the retained pair on its actual common reference -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def SeedRetainedPair.side {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (right : Bool) : SeedRetainedFirstCone S right length :=
  match right with
  | false => P.left
  | true => P.right

def SeedRetainedPair.sideRadius {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (right : Bool) : ℝ :=
  if right then P.pair.radiusR else P.pair.radiusL

def SeedRetainedPair.sideHeight {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (right : Bool) : ℝ :=
  if right then P.pair.heightR else P.pair.heightL

theorem SeedRetainedPair.sideRadius_pos {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length) (right : Bool) :
    0 < P.sideRadius right := by
  cases right
  · exact P.pair.radiusL_pos
  · exact P.pair.radiusL_pos.trans_le P.pair.radius_order

theorem SeedRetainedPair.sideHeight_pos {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length) (right : Bool) :
    0 < P.sideHeight right := by
  cases right
  · exact P.pair.heightL_pos
  · exact P.pair.heightR_pos

theorem radialRadiusScale_germ {u v : ℝ → ℝ} {κ α r : ℝ}
    (hκ : κ ≠ 0) (hu : u =ᶠ[𝓝 r] v) :
    radialRadiusScale κ α u =ᶠ[𝓝 (κ * r)] radialRadiusScale κ α v := by
  have he : κ * r / κ = r := by field_simp [hκ] <;> ring
  have ht : Tendsto (fun t : ℝ => t / κ) (𝓝 (κ * r)) (𝓝 r) := by
    simpa only [id_eq, he] using (continuous_id.div_const κ).tendsto (κ * r)
  filter_upwards [hu.comp_tendsto ht] with t h
  simp only [Function.comp_apply] at h
  change α * u (t / κ) = α * v (t / κ)
  rw [h]

theorem contDiff_radialRadiusScale {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (κ α : ℝ) :
    ContDiff ℝ ∞ (radialRadiusScale κ α u) :=
  contDiff_const.mul (hu.comp (contDiff_id.div_const κ))

theorem SeedRetainedPair.reference_side_profile_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (right : Bool) {r : ℝ}
    (hr : 0 < r) (hi : if right then (P.side right).inner ≤ r else r ≤ (P.side right).inner) :
    D.w =ᶠ[𝓝 (P.sideRadius right * r)]
      radialRadiusScale (P.sideRadius right) (P.sideHeight right * P.sideRadius right)
        (P.side right).tail.profile := by
  rw [hw]
  cases right
  · exact P.left_profile_germ hr hi
  · exact P.right_profile_germ hi

theorem SeedRetainedPair.reference_side_old_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S) (right : Bool) {r : ℝ}
    (hr : r ∈ radialCore (S.family S.sigma))
    (ho : if right then S.cut right S.chain.index ≤ r else r ≤ S.cut right S.chain.index) :
    D.w =ᶠ[𝓝 (P.sideRadius right * r)]
      radialRadiusScale (P.sideRadius right) (P.sideHeight right * P.sideRadius right)
        (S.family S.sigma).w := by
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hi : if right then (P.side right).inner ≤ r else r ≤ (P.side right).inner := by
    cases right
    · exact ho.trans (P.side false).inner_order.le
    · exact (P.side true).inner_order.le.trans ho
  exact (P.reference_side_profile_germ hw right (hD₀.1.trans hr.1) hi).trans
    (radialRadiusScale_germ (P.sideRadius_pos right).ne' ((P.side right).profile_old_germ hr ho))

theorem SeedRetainedPair.reference_side_old_value {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S) (right : Bool) {r : ℝ}
    (hr : r ∈ radialCore (S.family S.sigma))
    (ho : if right then S.cut right S.chain.index ≤ r else r ≤ S.cut right S.chain.index) :
    D.w (P.sideRadius right * r) =
      (P.sideHeight right * P.sideRadius right) * (S.family S.sigma).w r :=
  (P.reference_side_old_germ hw hS right hr ho).eq_of_nhds.trans
    (radialRadiusScale_apply_mul (P.sideRadius_pos right).ne' _ _ _)

/-- The positive set of a profile determines its two flat endpoints. -/
theorem radialProfileGeometry_endpoints_eq_of_profile_eq {D E : ReferenceData}
    (hD : RadialProfileGeometry D) (hE : RadialProfileGeometry E) (hw : D.w = E.w) :
    D.a = E.a ∧ D.b = E.b := by
  have hDE : Ioo D.a D.b ⊆ Ioo E.a E.b := by
    intro r hr
    apply radialCore_mem_of_profile_pos hE
    rw [← hw]
    exact hD.2.2.2.2.1 r hr
  have hED : Ioo E.a E.b ⊆ Ioo D.a D.b := by
    intro r hr
    apply radialCore_mem_of_profile_pos hD
    rw [hw]
    exact hE.2.2.2.2.1 r hr
  have h₁ := (Ioo_subset_Ioo_iff hD.2.1).mp hDE
  have h₂ := (Ioo_subset_Ioo_iff hE.2.1).mp hED
  exact ⟨le_antisymm h₂.1 h₁.1, le_antisymm h₁.2 h₂.2⟩

theorem SeedRetainedPair.reference_side_endpoint {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hD : RadialProfileGeometry D) (hw : D.w = P.pair.profile)
    (right : Bool) :
    (if right then D.b else D.a) =
      P.sideRadius right * (if right then (S.family S.sigma).b else (S.family S.sigma).a) := by
  have h := radialProfileGeometry_endpoints_eq_of_profile_eq hD P.pair.geometry hw
  cases right
  · exact h.1
  · exact h.2

theorem mem_uIcc_div_pos {κ a b x : ℝ} (hκ : 0 < κ) :
    x / κ ∈ uIcc a b ↔ x ∈ uIcc (κ * a) (κ * b) := by
  rcases le_total a b with h | h
  · rw [uIcc_of_le h, uIcc_of_le (mul_le_mul_of_nonneg_left h hκ.le)]
    simp only [mem_Icc, le_div_iff₀ hκ, div_le_iff₀ hκ, mul_comm a κ, mul_comm b κ]
  · rw [uIcc_of_ge h, uIcc_of_ge (mul_le_mul_of_nonneg_left h hκ.le)]
    simp only [mem_Icc, le_div_iff₀ hκ, div_le_iff₀ hκ, mul_comm a κ, mul_comm b κ]

end ContinuousFlexibility.Radial
