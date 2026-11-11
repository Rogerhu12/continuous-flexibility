import ContinuousFlexibility.Radial.MorseHeightAngleExclusion
import Mathlib.Order.Interval.Set.Infinite

/-!
# Choosing the finite first-band matching angles

After the infinite height selection, only finitely many first-band lines
remain. A cone height in any nonempty open interval avoids the finitely
many affine determinant zeros. A common positive tolerance can then be
chosen and preserved by sufficiently short positive joins.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

theorem r07_exists_avoid_affine_zeros {ι : Type*} (I : Finset ι)
    (α β : ι → ℝ) (hpair : ∀ i ∈ I, α i ≠ 0 ∨ β i ≠ 0)
    {l h : ℝ} (hlh : l < h) :
    ∃ t ∈ Ioo l h, ∀ i ∈ I, α i - β i * t ≠ 0 := by
  classical
  let bad : Finset ℝ := I.image (fun i => α i / β i)
  have hout : ∃ t ∈ Ioo l h, t ∉ bad := by
    by_contra hn
    push_neg at hn
    exact (Ioo_infinite hlh) (bad.finite_toSet.subset hn)
  obtain ⟨t, ht, hnot⟩ := hout
  refine ⟨t, ht, fun i hi hz => ?_⟩
  by_cases hb : β i = 0
  · have ha := (hpair i hi).resolve_right (not_not_intro hb)
    exact ha (by simpa only [hb, zero_mul, sub_zero] using hz)
  · have he : t = α i / β i := (eq_div_iff hb).mpr (by linarith only [hz])
    apply hnot
    rw [he]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem radialAngleSine_pos_of_det_ne {u v : ℝ × ℝ}
    (hdet : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    0 < Statements.radialAngleSine u v := by
  have hlength (z : ℝ × ℝ) (hz : z ≠ (0, 0)) : 0 < sqrt (z.1 ^ 2 + z.2 ^ 2) := by
    apply sqrt_pos.mpr
    by_cases h₁ : z.1 = 0
    · have h₂ : z.2 ≠ 0 := fun h => hz (Prod.ext h₁ h)
      rw [h₁, zero_pow (by decide : 2 ≠ 0), zero_add]
      exact sq_pos_of_ne_zero h₂
    · exact (sq_pos_of_ne_zero h₁).trans_le (le_add_of_nonneg_right (sq_nonneg z.2))
  have hu : u ≠ (0, 0) := by intro h; apply hdet; simp only [h, zero_mul, sub_zero]
  have hv : v ≠ (0, 0) := by intro h; apply hdet; simp only [h, mul_zero, sub_zero]
  exact div_pos (abs_pos.mpr hdet) (mul_pos (hlength u hu) (hlength v hv))

/-- A fixed physical endpoint height and any finite collection of nonzero
natural states admit a cone reference height avoiding every degeneracy. -/
theorem r07_exists_finite_cone_height {ι : Type*} (I : Finset ι)
    (a : ι → ℝ) (B : ι → ℝ × ℝ) (ha : ∀ i ∈ I, a i ≠ 0)
    (hB : ∀ i ∈ I, B i ≠ (0, 0)) {H l h : ℝ}
    (hH : 0 < H) (hl : 0 < l) (hlh : l < h) :
    ∃ W ∈ Ioo l h, ∀ i ∈ I,
      0 < Statements.radialAngleSine (1, a i) ((B i).1, H / W * (B i).2) := by
  obtain ⟨W, hW, hdet⟩ := r07_exists_avoid_affine_zeros I
    (fun i => H * (B i).2) (fun i => a i * (B i).1) (by
      intro i hi
      by_cases h₁ : (B i).1 = 0
      · exact Or.inl (mul_ne_zero hH.ne' (fun h₂ => hB i hi (Prod.ext h₁ h₂)))
      · exact Or.inr (mul_ne_zero (ha i hi) h₁)) hlh
  have hW₀ : W ≠ 0 := (hl.trans hW.1).ne'
  refine ⟨W, hW, fun i hi => radialAngleSine_pos_of_det_ne ?_⟩
  intro hz
  apply hdet i hi
  have hm := congrArg (fun z : ℝ => z * W) hz
  dsimp only at hm
  field_simp [hW₀] at hm
  nlinarith only [hm]

theorem r07_exists_finite_angle_tolerance {ι : Type*} (I : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 48 ∧ ∀ i ∈ I, 2 * δ ≤ f i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1 / 48, by norm_num, le_rfl, by simp⟩
  | @insert i I hi ih =>
      have hfi : 0 < f i := hf i (Finset.mem_insert_self _ _)
      obtain ⟨δ, hδ, hδs, hδf⟩ := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      refine ⟨min δ (f i / 4), lt_min hδ (by positivity),
        (min_le_left _ _).trans hδs, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · have hb := min_le_right δ (f k / 4)
        linarith only [hb, hfi]
      · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)).trans (hδf k hk)

/-- The finite first-band choice survives the same coordinate error used
in the infinite selection argument. -/
theorem r07_angle_lower_of_near {a δ : ℝ} {Y B : ℝ × ℝ}
    (hB : B ≠ (0, 0)) (hδ : 0 < δ) (hδs : δ ≤ 1 / 48)
    (hY : |Y.1 - 1| ≤ δ / 4 ∧ |Y.2 - a| ≤ δ / 4)
    (hangle : 2 * δ ≤ Statements.radialAngleSine (1, a) B) :
    δ ≤ Statements.radialAngleSine Y B := by
  by_contra h
  have hbad : (1 : ℝ) ∈ morseHeightAngleBadSet 1 δ (fun _ => Y) B := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    simpa only [morseHeightOuterState, one_mul] using lt_of_not_ge h
  have hbad' := morseHeightAngle_bad_subset_ideal (a := a) (Ξ := 1) (η := δ / 4)
    (Y := fun _ => Y) (by norm_num) hB hδ hδs (by positivity) le_rfl
    (fun _ _ => hY) hbad
  have hlt : Statements.radialAngleSine (1, a) B < 2 * δ := by
    simpa only [morseHeightOuterState, one_mul] using hbad'.2
  exact (not_lt_of_ge hangle) hlt

end ContinuousFlexibility.Radial
