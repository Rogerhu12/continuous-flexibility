module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Algebraic selection of the two null characteristic directions

Positive angular derivatives and a nonzero differential determinant exclude
equal characteristic directions. Their oriented radial difference then
selects the positive direction for the first coordinate and the negative
direction for the second. No transport equation is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

theorem n05_ordered_null_slopes
    {v nrp ntp nrm ntm : ℝ} (hv : 0 < v) (htp : 0 < ntp) (htm : 0 < ntm)
    (hp : nrp ^ 2 = (v * ntp) ^ 2) (hm : nrm ^ 2 = (v * ntm) ^ 2)
    (hdet : nrp * ntm - ntp * nrm ≠ 0) (horder : 0 < nrp - nrm) :
    nrp = v * ntp ∧ nrm = -(v * ntm) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp with hp | hp
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hm with hm | hm
    · exact False.elim (hdet (by rw [hp, hm]; ring))
    · exact ⟨hp, hm⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hm with hm | hm
    · rw [hp, hm] at horder
      have hplus := mul_pos hv htp
      have hminus := mul_pos hv htm
      exact False.elim (by linarith only [horder, hplus, hminus])
    · exact False.elim (hdet (by rw [hp, hm]; ring))

/-- Multiplying the radial direction by an orientation of square one treats
both halves by the same algebraic characteristic-selection lemma. -/
theorem n05_oriented_null_slopes
    {v nrp ntp nrm ntm orientation : ℝ}
    (hv : 0 < v) (htp : 0 < ntp) (htm : 0 < ntm)
    (ho : orientation ^ 2 = 1)
    (hp : nrp ^ 2 = (v * ntp) ^ 2) (hm : nrm ^ 2 = (v * ntm) ^ 2)
    (hdet : nrp * ntm - ntp * nrm ≠ 0)
    (horder : 0 < orientation * (nrp - nrm)) :
    orientation * nrp = v * ntp ∧ orientation * nrm = -(v * ntm) := by
  have ho0 : orientation ≠ 0 := by
    intro hz
    rw [hz] at ho
    norm_num at ho
  have hp' : (orientation * nrp) ^ 2 = (v * ntp) ^ 2 := by
    simpa only [mul_pow, ho, one_mul] using hp
  have hm' : (orientation * nrm) ^ 2 = (v * ntm) ^ 2 := by
    simpa only [mul_pow, ho, one_mul] using hm
  have hdet' : (orientation * nrp) * ntm - ntp * (orientation * nrm) ≠ 0 := by
    have heq : (orientation * nrp) * ntm - ntp * (orientation * nrm) =
        orientation * (nrp * ntm - ntp * nrm) := by ring
    rw [heq]
    exact mul_ne_zero ho0 hdet
  exact n05_ordered_null_slopes hv htp htm hp' hm' hdet'
    (by simpa only [mul_sub] using horder)

end ContinuousFlexibility.Statements
