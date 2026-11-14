module

public import ContinuousFlexibility.Radial.R07MorseCapGeometry
public import ContinuousFlexibility.Radial.R07BandSelection

/-!
# The actual normalized incoming solution on a preceding Morse cell

The fixed cap constant is `1000`. The band inequality supplies this
frequency action on every earlier cell. The profile identity then turns
the concrete cap geometry into a normalized physical radial solution,
with positive profile derivative on the cut-to-join span and an initial
join state `(1,a)` whose slope is in the interval needed for selection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

theorem r07_cap_action_of_later_band (T : Statements.MorseChainData) {C : ℝ}
    (hC : 1000 ≤ C) (hstart : 1 ≤ T.index)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {n m j : ℕ}
    (hband : Statements.radialFrequencyBand T C n j) (hm : T.index ≤ m) (hmn : m < n) :
    1000 ≤ (j : ℝ) * sqrt (Statements.morseChainA T m) := by
  have hC₀ : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hstart.trans hm
  have hQ : 1 ≤ Statements.radialQ m := by
    have hs : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm₁ 2
    exact hs.trans (radial_nat_sq_le_Q m)
  exact (hC.trans (le_mul_of_one_le_right hC₀.le hQ)).trans
    (morseTransition_earlier_cap_action T hC₀ hd hband hm hmn)

/-- Positive curvature of the oriented cap holds strictly away from its
Dirichlet endpoint, including for the cap that starts at a turning point. -/
theorem r07CapRadius_second_pos (right : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Ioo 0 (r07CapLength right A)) :
    0 < deriv (deriv (r07CapRadius right A B s r)) t := by
  have ht' := Ioo_subset_Icc_self ht
  rw [r07CapRadius_equation right hB hAB hr ht']
  apply mul_pos _ (r07CapRadius_model_bounds right hB hAB hs hr ht').1
  have hm := r07CapPoint_mem (B := B) right ht'
  cases right
  · have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
    exact (div_pos hA (by norm_num)).trans_le (morseShortLeftCap_negRho_lower hB hAB hm.2)
  · apply neg_pos.mpr (morseRho_neg_after_right_turn hB hAB ?_)
    simpa [r07CapPoint, r07CapCut, r07OutwardSign] using ht.1

/-- The profile is strictly increasing on the physical open span of an
oriented positive cap. The derivative identity is used once for both sides. -/
theorem r07_cap_profile_increasing (right : Bool) {R w : ℝ → ℝ} {scale L : ℝ}
    (hL : 0 < L) (hR : ContDiff ℝ ∞ R) (hw : ContDiff ℝ ∞ w)
    (hdir : ∀ t ∈ Icc 0 L, if right then 0 < deriv R t else deriv R t < 0)
    (hweight : ∀ t ∈ Icc 0 L, w (R t) = scale * deriv R t)
    (hpos : ∀ t ∈ Icc 0 L, 0 < w (R t))
    (hsecond : ∀ t ∈ Ioo 0 L, 0 < deriv (deriv R) t) :
    ∀ y ∈ Statements.radialOpenSpan (R 0) (R L), 0 < deriv w y := by
  have horder := r07_cap_order right hL hR hdir
  have himage : R '' Ioo 0 L = Statements.radialOpenSpan (R 0) (R L) := by
    cases right
    · have hanti : StrictAntiOn R (Icc 0 L) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc 0 L) hR.continuous.continuousOn
        intro t ht
        exact hdir t (interior_subset ht)
      simpa only [Statements.radialOpenSpan, min_eq_right horder.le, max_eq_left horder.le] using
        ContinuousOn.image_Ioo_of_strictAntiOn hL.le hR.continuous.continuousOn hanti
    · have hmono : StrictMonoOn R (Icc 0 L) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc 0 L) hR.continuous.continuousOn
        intro t ht
        exact hdir t (interior_subset ht)
      simpa only [Statements.radialOpenSpan, min_eq_left horder.le, max_eq_right horder.le] using
        ContinuousOn.image_Ioo_of_strictMonoOn hL.le hR.continuous.continuousOn hmono
  intro y hy
  rw [← himage] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have ht' := Ioo_subset_Icc_self ht
  have hd := r07_cap_weight_derivative hL hR hw hweight ht'
  have he : deriv w (R t) * deriv R t ^ 2 = w (R t) * deriv (deriv R) t := by
    calc
      _ = (deriv w (R t) * deriv R t) * deriv R t := by ring
      _ = (scale * deriv (deriv R) t) * deriv R t := by rw [hd]
      _ = (scale * deriv R t) * deriv (deriv R) t := by ring
      _ = _ := by rw [← hweight t ht']
  have hprod : 0 < deriv w (R t) * deriv R t ^ 2 := by
    rw [he]
    exact mul_pos (hpos t ht') (hsecond t ht)
  apply lt_of_not_ge
  intro hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hnonpos (sq_nonneg _))) hprod

/-- Actual model geometry and the cell/profile identity supply every cap
hypothesis. The final state is the project's `radialState`, at the physical
join and scaled by its actual profile height. -/
theorem exists_r07_normalized_morse_incoming (right : Bool) {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {A B s lam l h : ℝ} {j : ℕ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hBA : B ≤ A ^ 9) (hs : 0 < s) (hlam : 0 < lam)
    (hj : 2 ≤ j) (hr : IsNormalizedMorseCell A B r)
    (hl : D.a < l) (hlh : l ≤ h) (hh : h < D.b)
    (hmap : ∀ t ∈ Icc 0 (r07CapLength right A),
      r07CapRadius right A B s r t ∈ Icc l h)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      D.w (s * r x) = lam * (s * deriv r x))
    (haction : 1000 ≤ (j : ℝ) * sqrt A) :
    ∃ (u : ℝ → ℝ) (a : ℝ), ContDiff ℝ ∞ u ∧
      u (s * r (r07CapCut right A B)) = 0 ∧ u (s * r (r07CapEnd right A B)) = 1 ∧
      (if right then 0 < deriv u (s * r (r07CapCut right A B))
        else deriv u (s * r (r07CapCut right A B)) < 0) ∧
      (if right then s * r (r07CapCut right A B) < s * r (r07CapEnd right A B)
        else s * r (r07CapEnd right A B) < s * r (r07CapCut right A B)) ∧
      (∀ y ∈ Statements.radialOpenSpan
        (s * r (r07CapCut right A B)) (s * r (r07CapEnd right A B)), 0 < deriv D.w y) ∧
      Statements.RadialHomogeneousOn D j (Icc l h) u ∧
      a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) ∧
      Statements.radialState D j (s * r (r07CapEnd right A B))
        (D.w (s * r (r07CapEnd right A B))) u = (1, a) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  let R := r07CapRadius right A B s r
  let L := r07CapLength right A
  let M := r07CapRiccatiBound right A (j : ℝ)
  let scale := lam * r07OutwardSign right
  have hL : 0 < L := r07CapLength_pos right hA
  have hM : 0 < M := r07CapRiccatiBound_pos right hA hj₀
  have hR : ContDiff ℝ ∞ R := r07CapRadius_smooth right A B s hr.smooth
  have hdir : ∀ t ∈ Icc 0 L, if right then 0 < deriv R t else deriv R t < 0 :=
    fun t ht => (r07CapRadius_model_bounds right hB hAB hs hr ht).2
  have hscale : scale ≠ 0 := mul_ne_zero hlam.ne'
    (by cases right <;> norm_num [r07OutwardSign])
  have hweight' : ∀ t ∈ Icc 0 L, D.w (R t) = scale * deriv R t := by
    intro t ht
    rw [r07CapRadius_deriv right A B s t hr.smooth]
    change D.w (s * r (r07CapPoint right A B t)) =
      (lam * r07OutwardSign right) * (s * deriv r (r07CapPoint right A B t) * r07OutwardSign right)
    rw [hweight _ (r07CapPoint_mem_cell right hB hAB ht)]
    calc
      _ = lam * (s * deriv r (r07CapPoint right A B t)) * r07OutwardSign right ^ 2 := by
        rw [r07OutwardSign_sq, mul_one]
      _ = _ := by ring
  have hpos : ∀ t ∈ Icc 0 L, 0 < D.w (R t) := by
    intro t ht
    exact hD.2.2.2.2.1 (R t) ⟨hl.trans_le (hmap t ht).1, (hmap t ht).2.trans_lt hh⟩
  have hwpos := r07_cap_profile_increasing right hL hR hD.2.2.1.1 hdir hweight' hpos
    (fun t ht => r07CapRadius_second_pos right hB hAB hs hr ht)
  obtain ⟨u, hu, hu₀, huL, hsign, horder, hode, _, ha⟩ :=
    exists_r07_normalized_incoming_cap right hD hl hlh hh hL (sq_pos_of_pos hj₀) hM hscale
      hR hmap hdir hweight'
      (fun t ht => r07CapRadius_scalar_bound right hB hAB hBA hs hr ht)
      (r07CapRadius_slope_small right hB hAB hs hj₀ hr haction)
  have hR₀ : R 0 = s * r (r07CapCut right A B) := by simp [R, r07CapRadius, r07CapPoint_zero]
  have hRL : R L = s * r (r07CapEnd right A B) := by
    dsimp only [R, L, r07CapRadius]
    rw [r07CapPoint_end]
  let a := R L * deriv u (R L) / (j : ℝ) ^ 2 - 1
  have hstate : Statements.radialState D j (R L) (D.w (R L)) u = (1, a) := by
    simp [Statements.radialState, huL, (hpos L ⟨hL.le, le_rfl⟩).ne', a]
  rw [hR₀] at hu₀ hsign
  rw [hRL] at huL hstate
  rw [hR₀, hRL] at horder hwpos
  exact ⟨u, a, hu, hu₀, huL, hsign, horder, hwpos, ⟨hu.contDiffOn, hode⟩, ha, hstate⟩

end ContinuousFlexibility.Radial
