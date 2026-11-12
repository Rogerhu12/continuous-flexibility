import ContinuousFlexibility.Analysis.N04bStateProfileType

/-!
# The exact optical lower test furnished by the original N01 state ball

The direction below belongs to the actual supplied state space.  Positivity
on the whole original ball bounds its logarithmic-profile derivative by
the reference optical radicand.  No arbitrary profile perturbation or
uniform simple-root lower bound is assumed or concluded.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

set_option backward.isDefEq.respectTransparency false

/-- The common N01 radius controls every available logarithmic-profile
test direction, before taking a square root. -/
theorem N01Properties.profileDirection_optical_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : AnnularState S) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ε * |-(deriv (n04bStateLogExponent D S C v) r) / r| ≤
      (-deriv D.w r / (r * D.w r)) * stateGrading S base v := by
  let a : ℝ := -deriv D.w r / (r * D.w r)
  let b : ℝ := -(deriv (n04bStateLogExponent D S C v) r) / r
  let P : ℝ := stateGrading S base v
  have hP : 0 ≤ P := apply_nonneg (stateGrading S base) v
  have ha : 0 < a := by
    have h := hN.n04b_stateLine_radicand_pos hS hT v m hr
      (t := (0 : ℝ)) (by simpa only [abs_zero, zero_mul] using hN.2.1)
    simpa only [mul_zero, add_zero] using h
  change ε * |b| ≤ a * P
  by_contra hle
  have hlt : a * P < ε * |b| := lt_of_not_ge hle
  have hb : b ≠ 0 := by
    intro hzero
    have hh : a * P < 0 := by simpa only [hzero, abs_zero, mul_zero] using hlt
    exact (not_lt_of_ge (mul_nonneg ha.le hP)) hh
  have hab : 0 < |b| := abs_pos.mpr hb
  have ht : |(-a / b)| * P < ε := by
    rw [abs_div, abs_neg, abs_of_pos ha, div_mul_eq_mul_div]
    exact (div_lt_iff₀ hab).mpr hlt
  have hpositive := hN.n04b_stateLine_radicand_pos hS hT v m hr
    (t := -a / b) ht
  change 0 < a + b * (-a / b) at hpositive
  have heq : a + b * (-a / b) = 0 := by
    field_simp [hb]
    <;> ring
  rw [heq] at hpositive
  exact (lt_irrefl (0 : ℝ)) hpositive

end ContinuousFlexibility.Statements
