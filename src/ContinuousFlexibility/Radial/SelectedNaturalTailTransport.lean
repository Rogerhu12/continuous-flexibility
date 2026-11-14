module

public import ContinuousFlexibility.Radial.SelectedReferenceEquation
public import ContinuousFlexibility.Radial.SelectedTailRadiusMeasure

/-!
# Natural radial solutions under the actual R08 dilation

The equation, entrance smoothness, restricted radial L² condition and
nontriviality are transported together. The profile identity is needed
only on the retained open tail, and only its corresponding endpoint
must scale. Pulling back by the inverse dilation proves the converse.

The final theorem transports a proved natural-line uniqueness statement.
It does not assert uniqueness merely from the existence of a natural
solution or from the R08 profile identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The inverse physical dilation also inverts the solution amplitude. -/
theorem radialRadiusScale_inverse {κ α : ℝ} (hκ : κ ≠ 0) (hα : α ≠ 0)
    (u : ℝ → ℝ) :
    radialRadiusScale κ⁻¹ α⁻¹ (radialRadiusScale κ α u) = u := by
  funext r
  have harg : r / κ⁻¹ / κ = r := by field_simp [hκ] <;> ring
  change α⁻¹ * (α * u (r / κ⁻¹ / κ)) = u r
  rw [harg, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]

/-- The inverse dilation is also a right inverse on arbitrary functions. -/
theorem radialRadiusScale_inverse_reverse {κ α : ℝ}
    (hκ : κ ≠ 0) (hα : α ≠ 0) (u : ℝ → ℝ) :
    radialRadiusScale κ α (radialRadiusScale κ⁻¹ α⁻¹ u) = u := by
  simpa only [inv_inv] using
    radialRadiusScale_inverse (inv_ne_zero hκ) (inv_ne_zero hα) u

/-- The same open-interval argument applies to both endpoint orientations. -/
theorem radialHomogeneousOn_reference_scaled_tail {D E : ReferenceData}
    {κ β entry : ℝ} (hκ : 0 < κ) (right : Bool)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    {j : ℕ} {u : ℝ → ℝ}
    (hu : RadialHomogeneousOn D j (radialTailInterval D right entry) u) (α : ℝ) :
    RadialHomogeneousOn E j (radialTailInterval E right (κ * entry))
      (radialRadiusScale κ α u) := by
  cases right
  · change E.a = κ * D.a at hend
    change RadialHomogeneousOn E j (Ioo E.a (κ * entry))
      (radialRadiusScale κ α u)
    rw [hend]
    exact radialHomogeneousOn_reference_scaled_interval hκ hprofile hu α
  · change E.b = κ * D.b at hend
    change RadialHomogeneousOn E j (Ioo (κ * entry) E.b)
      (radialRadiusScale κ α u)
    rw [hend]
    exact radialHomogeneousOn_reference_scaled_interval hκ hprofile hu α

/-- The full natural-tail predicate, including its genuine radial L²
condition and a nonzero value, is preserved by a nonzero amplitude. -/
theorem radialNaturalTail_reference_scaled {D E : ReferenceData}
    {κ β α entry : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0)
    (right : Bool) (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    {j : ℕ} {u : ℝ → ℝ} (hu : RadialNaturalTail D right j entry u) :
    RadialNaturalTail E right j (κ * entry) (radialRadiusScale κ α u) := by
  refine ⟨contDiffAt_radialRadiusScale hκ.ne' hu.1 α,
    radialHomogeneousOn_reference_scaled_tail hκ right hend hprofile hu.2.1 α,
    (memLp_radialRadiusScale_tail_iff hκ hβ hα right hD hE hend hprofile).mpr
      hu.2.2.1, ?_⟩
  rcases hu.2.2.2 with ⟨r, hr, hnonzero⟩
  refine ⟨κ * r, ?_, ?_⟩
  · rw [← radialTailInterval_radius_image hκ right hend]
    exact ⟨r, hr, rfl⟩
  · rw [radialRadiusScale_apply_mul hκ.ne']
    exact mul_ne_zero hα hnonzero

/-- The actual profile identity can be inverted on the actual image tail.
Neither profile is required to agree with a dilation away from this set. -/
theorem referenceProfile_radiusScale_inverse_tail {D E : ReferenceData}
    {κ β entry : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (right : Bool)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r) :
    ∀ s ∈ radialTailInterval E right (κ * entry),
      D.w (κ⁻¹ * s) = (β⁻¹ * κ⁻¹) * E.w s := by
  intro s hs
  have hs' : s ∈ (fun r : ℝ => κ * r) '' radialTailInterval D right entry := by
    rw [radialTailInterval_radius_image hκ right hend]
    exact hs
  rcases hs' with ⟨r, hr, rfl⟩
  rw [hprofile r hr]
  have hcancel : κ⁻¹ * (κ * r) = r := by
    rw [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
  rw [hcancel]
  field_simp [hκ.ne', hβ.ne'] <;> ring

/-- Pulling an arbitrary natural solution on the new reference back to
the old reference preserves all four parts of the natural-tail predicate. -/
theorem radialNaturalTail_reference_pullback {D E : ReferenceData}
    {κ β α entry : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0)
    (right : Bool) (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    {j : ℕ} {v : ℝ → ℝ} (hv : RadialNaturalTail E right j (κ * entry) v) :
    RadialNaturalTail D right j entry (radialRadiusScale κ⁻¹ α⁻¹ v) := by
  have hentry : κ⁻¹ * (κ * entry) = entry := by
    rw [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
  have hend' : (if right then D.b else D.a) =
      κ⁻¹ * (if right then E.b else E.a) := by
    rw [hend, ← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
  have hD' : κ⁻¹ * (κ * entry) ∈ radialCore D := by
    simpa only [hentry] using hD
  have h := radialNaturalTail_reference_scaled
    (D := E) (E := D) (κ := κ⁻¹) (β := β⁻¹) (α := α⁻¹)
    (entry := κ * entry) (inv_pos.mpr hκ) (inv_pos.mpr hβ) (inv_ne_zero hα)
    right hE hD' hend'
    (referenceProfile_radiusScale_inverse_tail hκ hβ right hend hprofile) hv
  simpa only [hentry] using h

/-- A dilation of the genuine natural L² problem is an equivalence of
natural solutions, not only a forward construction of candidates. -/
theorem radialNaturalTail_reference_scaled_iff {D E : ReferenceData}
    {κ β α entry : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0)
    (right : Bool) (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    {j : ℕ} {u : ℝ → ℝ} :
    RadialNaturalTail E right j (κ * entry) (radialRadiusScale κ α u) ↔
      RadialNaturalTail D right j entry u := by
  constructor
  · intro hu
    have h := radialNaturalTail_reference_pullback
      hκ hβ hα right hD hE hend hprofile hu
    rw [radialRadiusScale_inverse hκ.ne' hα u] at h
    exact h
  · exact radialNaturalTail_reference_scaled hκ hβ hα right hD hE hend hprofile

/-- A proved one-dimensional natural solution space on the old tail gives
the corresponding one-dimensional space on the new, actually scaled tail.
The scalar relating two solutions remains the same under conjugation. -/
theorem radialNaturalTail_line_unique_radiusScale {D E : ReferenceData}
    {κ β α entry : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0)
    (right : Bool) (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    {j : ℕ} {u : ℝ → ℝ}
    (hunique : ∀ v : ℝ → ℝ, RadialNaturalTail D right j entry v →
      ∃ c : ℝ, c ≠ 0 ∧ ∀ r ∈ radialTailInterval D right entry, v r = c * u r) :
    ∀ v : ℝ → ℝ, RadialNaturalTail E right j (κ * entry) v →
      ∃ c : ℝ, c ≠ 0 ∧ ∀ s ∈ radialTailInterval E right (κ * entry),
        v s = c * radialRadiusScale κ α u s := by
  intro v hv
  have hback := radialNaturalTail_reference_pullback
    hκ hβ hα right hD hE hend hprofile hv
  rcases hunique _ hback with ⟨c, hc, hline⟩
  refine ⟨c, hc, ?_⟩
  intro s hs
  have hs' : s ∈ (fun r : ℝ => κ * r) '' radialTailInterval D right entry := by
    rw [radialTailInterval_radius_image hκ right hend]
    exact hs
  rcases hs' with ⟨r, hr, rfl⟩
  have h := hline r hr
  change α⁻¹ * v (r / κ⁻¹) = c * u r at h
  have harg : r / κ⁻¹ = κ * r := by
    simp only [div_eq_mul_inv, inv_inv, mul_comm]
  rw [harg] at h
  have hm := congrArg (fun z : ℝ => α * z) h
  have hcancel : α * (α⁻¹ * v (κ * r)) = v (κ * r) := by
    rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul]
  rw [hcancel] at hm
  rw [radialRadiusScale_apply_mul hκ.ne']
  calc
    v (κ * r) = α * (c * u r) := hm
    _ = c * (α * u r) := by ring

end ContinuousFlexibility.Radial
