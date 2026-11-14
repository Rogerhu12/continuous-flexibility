module

public import ContinuousFlexibility.Analysis.SpacesHeightBounds
public import ContinuousFlexibility.Analysis.SpacesCutoff
public import ContinuousFlexibility.Analysis.TameTransfer

/-!
# The reciprocal from smooth composition on one fixed neighborhood

A globally smooth scalar function agrees with `1 / (1 + x) - 1` for
`|x| ≤ 1/2`. The order-two height bound then puts every point of the
annulus inside that interval on one fixed grading neighborhood. Thus
the reciprocal clause follows from the smooth composition clause without
introducing a separate family of neighborhoods at higher orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def spacesScalarCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (4 * x + 3) * Real.smoothTransition (3 - 4 * x)

theorem spacesScalarCutoff_contDiff : ContDiff ℝ ∞ spacesScalarCutoff :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem spacesScalarCutoff_nonneg (x : ℝ) : 0 ≤ spacesScalarCutoff x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem spacesScalarCutoff_le_one (x : ℝ) : spacesScalarCutoff x ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul _)

theorem spacesScalarCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) :
    spacesScalarCutoff x = 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  rw [spacesScalarCutoff,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4 * x + 3),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 - 4 * x), one_mul]

theorem spacesScalarCutoff_eq_zero {x : ℝ} (hx : 3 / 4 ≤ |x|) :
    spacesScalarCutoff x = 0 := by
  rcases le_abs.mp hx with hx | hx
  · rw [spacesScalarCutoff,
      Real.smoothTransition.zero_of_nonpos (by linarith : 3 - 4 * x ≤ 0), mul_zero]
  · rw [spacesScalarCutoff,
      Real.smoothTransition.zero_of_nonpos (by linarith : 4 * x + 3 ≤ 0), zero_mul]

theorem spaces_scalar_clipped_bound (x : ℝ) : |x * spacesScalarCutoff x| ≤ 3 / 4 := by
  by_cases hx : |x| < 3 / 4
  · rw [abs_mul, abs_of_nonneg (spacesScalarCutoff_nonneg x)]
    exact (mul_le_mul_of_nonneg_left (spacesScalarCutoff_le_one x) (abs_nonneg _)).trans
      (by simpa only [mul_one] using hx.le)
  · rw [spacesScalarCutoff_eq_zero (le_of_not_gt hx), mul_zero, abs_zero]
    norm_num

def spacesScalarReciprocal (x : ℝ) : ℝ :=
  (1 + x * spacesScalarCutoff x)⁻¹ - 1

theorem spaces_scalar_denominator_pos (x : ℝ) : 0 < 1 + x * spacesScalarCutoff x := by
  have h := (abs_le.mp (spaces_scalar_clipped_bound x)).1
  linarith

theorem spacesScalarReciprocal_contDiff : ContDiff ℝ ∞ spacesScalarReciprocal :=
  ((contDiff_const.add (contDiff_id.mul spacesScalarCutoff_contDiff)).inv
    (fun x => (spaces_scalar_denominator_pos x).ne')).sub contDiff_const

theorem spacesScalarReciprocal_zero : spacesScalarReciprocal 0 = 0 := by
  simp only [spacesScalarReciprocal, zero_mul, add_zero, inv_one, sub_self]

theorem spacesScalarReciprocal_eq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    spacesScalarReciprocal x = 1 / (1 + x) - 1 := by
  rw [spacesScalarReciprocal, spacesScalarCutoff_eq_one hx, mul_one, one_div]

/-- The full reciprocal assertion for one exact physical model, derived
from its general smooth scalar-composition assertion. -/
theorem spaces_reciprocal_of_composition {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ)
    {H : SobolevModelData} (hH : IsSobolevModel D T γ H)
    (hcomp : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ comp : H.Space → H.Space,
        (∀ u, H.grading base u < ε → ∀ p, H.decode (comp u) p = F (H.decode u p)) ∧
        SmoothTameOn H.grading H.grading {u | H.grading base u < ε} comp) :
    ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ inv : H.Space → H.Space,
      (∀ u, H.grading base u < ε → ∀ p ∈ annularOpen D,
        1 / 2 < 1 + H.decode u p ∧
        H.decode (inv u) p = 1 / (1 + H.decode u p) - 1) ∧
      SmoothTameOn H.grading H.grading {u | H.grading base u < ε} inv := by
  obtain ⟨b, ε, hε, comp, hdecode, htame⟩ :=
    hcomp spacesScalarReciprocal spacesScalarReciprocal_contDiff spacesScalarReciprocal_zero
  obtain ⟨δ, hδ, hsmall⟩ := spaces_positive_denominator_neighborhood hT hγ hH
  let B : ℕ := max b 2
  let η : ℝ := min ε δ
  have hεsub : {u : H.Space | H.grading B u < η} ⊆ {u | H.grading b u < ε} := by
    intro u hu
    exact (Analysis.gradedSeminorm_monotone _ _ (le_max_left b 2) u).trans_lt
      (hu.trans_le (min_le_left ε δ))
  have hδsub : ∀ u : H.Space, H.grading B u < η → H.grading 2 u < δ := by
    intro u hu
    exact (Analysis.gradedSeminorm_monotone _ _ (le_max_right b 2) u).trans_lt
      (hu.trans_le (min_le_right ε δ))
  refine ⟨B, η, lt_min hε hδ, comp, ?_, ?_⟩
  · intro u hu p hp
    have hpoint := hsmall u (hδsub u hu) p
    exact ⟨hpoint.2, (hdecode u (hεsub hu) p).trans (spacesScalarReciprocal_eq hpoint.1.le)⟩
  · apply Analysis.smoothTameOn_mono htame
    · exact isOpen_lt ((Analysis.withSeminorms_graded _ _).continuous_seminorm B) continuous_const
    · exact hεsub

end ContinuousFlexibility.Statements
