module

public import ContinuousFlexibility.Analysis.ParameterizedCircleInverse

/-!
# Angular intervals from actual axis fibers

A continuous degree-one lift has bounded displacement. If the fiber of
a fixed level consists only of that same point, the lift cannot cross
that level on either side. This requires no monotonicity assumption and
will be applied to the angular component of a two-dimensional inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem periodicLift_displacement_bounded
    {f : ℝ → ℝ} {T : ℝ} (hT : T ≠ 0) (hf : Continuous f)
    (hperiod : ∀ θ, f (θ + T) = f θ + T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, |f θ - θ| ≤ M := by
  have hc : Continuous (fun p : ℝ × ℝ => f p.2 - p.2) :=
    (hf.comp continuous_snd).sub continuous_snd
  obtain ⟨M, hM, hb⟩ := exists_norm_bound_periodic_compact
    (S := ({0} : Set ℝ)) (F := fun p : ℝ × ℝ => f p.2 - p.2)
    isCompact_singleton hT hc.continuousOn
    (fun _ _ θ => by
      change f (θ + T) - (θ + T) = f θ - θ
      rw [hperiod θ]
      ring)
  exact ⟨M, hM, fun θ => by
    simpa only [Real.norm_eq_abs] using hb 0 (by simp) θ⟩

private theorem fixedLevel_lt_of_lt
    {f : ℝ → ℝ} (hf : Continuous f) {M c t : ℝ}
    (hbound : ∀ θ, |f θ - θ| ≤ M)
    (hfiber : ∀ θ, f θ = c → θ = c) (ht : c < t) : c < f t := by
  by_contra h
  have hft : f t ≤ c := le_of_not_gt h
  let b := max t (c + M) + 1
  have htb : t ≤ b := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hfb : c < f b := by
    have hb := (abs_le.mp (hbound b)).1
    have hc : c + M ≤ max t (c + M) := le_max_right _ _
    dsimp only [b] at hb
    linarith
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc htb hf.continuousOn
    (show c ∈ Icc (f t) (f b) from ⟨hft, hfb.le⟩)
  have he := hfiber u hfu
  rw [he] at hu
  exact (not_le_of_gt ht) hu.1

/-- The location relative to a fixed level is preserved when that level
has a unique fiber and the actual displacement stays bounded. -/
theorem fixedLevel_lt_iff_of_bounded_displacement
    {f : ℝ → ℝ} (hf : Continuous f) {M c t : ℝ}
    (hbound : ∀ θ, |f θ - θ| ≤ M) (hc : f c = c)
    (hfiber : ∀ θ, f θ = c → θ = c) : c < f t ↔ c < t := by
  refine ⟨?_, fixedLevel_lt_of_lt hf hbound hfiber⟩
  intro hft
  by_contra h
  have htc : t ≤ c := le_of_not_gt h
  rcases lt_or_eq_of_le htc with hlt | heq
  · have hreflect : Continuous (fun θ : ℝ => -f (-θ)) :=
      (hf.comp continuous_neg).neg
    have hb : ∀ θ : ℝ, |-f (-θ) - θ| ≤ M := by
      intro θ
      have he : -f (-θ) - θ = -(f (-θ) - (-θ)) := by ring
      rw [he, abs_neg]
      exact hbound (-θ)
    have hz : ∀ θ : ℝ, -f (-θ) = -c → θ = -c := by
      intro θ hθ
      have hfc : f (-θ) = c := neg_injective hθ
      have hh := hfiber (-θ) hfc
      linarith
    have hh := fixedLevel_lt_of_lt hreflect hb hz (neg_lt_neg hlt)
    simp only [neg_neg] at hh
    linarith
  · rw [heq, hc] at hft
    exact lt_irrefl c hft

/-- The reflected version uses the same level-fiber argument. -/
theorem lt_fixedLevel_iff_of_bounded_displacement
    {f : ℝ → ℝ} (hf : Continuous f) {M c t : ℝ}
    (hbound : ∀ θ, |f θ - θ| ≤ M) (hc : f c = c)
    (hfiber : ∀ θ, f θ = c → θ = c) : f t < c ↔ t < c := by
  have hb : ∀ θ : ℝ, |-f (-θ) - θ| ≤ M := by
    intro θ
    have he : -f (-θ) - θ = -(f (-θ) - (-θ)) := by ring
    rw [he, abs_neg]
    exact hbound (-θ)
  have he : (fun θ : ℝ => -f (-θ)) (-c) = -c := by
    simp only [neg_neg, hc]
  have hz : ∀ θ : ℝ, -f (-θ) = -c → θ = -c := by
    intro θ hθ
    have hh := hfiber (-θ) (neg_injective hθ)
    linarith
  have hh := fixedLevel_lt_iff_of_bounded_displacement
    (f := fun θ : ℝ => -f (-θ)) (t := -t)
    ((hf.comp continuous_neg).neg) hb he hz
  simpa only [neg_neg, neg_lt_neg_iff] using hh

/-- A periodic lift with the two specified axis fibers has exactly the
same open fundamental interval as the identity. -/
theorem mem_Ioo_periodicLift_iff
    {f : ℝ → ℝ} {P t : ℝ} (hP : P ≠ 0) (hf : Continuous f)
    (hperiod : ∀ θ, f (θ + P) = f θ + P)
    (hf0 : f 0 = 0) (hfP : f P = P)
    (hzero : ∀ θ, f θ = 0 → θ = 0)
    (hPfiber : ∀ θ, f θ = P → θ = P) :
    f t ∈ Ioo 0 P ↔ t ∈ Ioo 0 P := by
  obtain ⟨M, _, hb⟩ := periodicLift_displacement_bounded hP hf hperiod
  exact and_congr (fixedLevel_lt_iff_of_bounded_displacement hf hb hf0 hzero)
    (lt_fixedLevel_iff_of_bounded_displacement hf hb hfP hPfiber)

end ContinuousFlexibility.Analysis
