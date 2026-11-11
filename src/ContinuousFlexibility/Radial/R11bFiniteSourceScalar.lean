import ContinuousFlexibility.Radial.R11bFiniteSource

/-!
# The scalar row of a finite derivative source

The compatible-field conditions are independent of the source's scalar row.
Its contribution to the norm is exactly its square.
-/

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem r11b_sineCosineSource_member_scalar {D : ReferenceData} (hab : D.a ≤ D.b)
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) {γ M : ℝ}
    {f : PolarPoint → ℝ} (hf : SourceDerivativeMember D γ M f) (c : ℝ) :
    SourceMember D γ M (r11bSineCosineSource J f, c) ∧
      sourceNormSquare D γ M (r11bSineCosineSource J f, c) ≤
        c ^ 2 + sourceNormSquare D γ M (f, 0) := by
  obtain ⟨hmember, hbound⟩ := r11b_sineCosineSource_member hab J hJ hf
  refine ⟨hmember, ?_⟩
  simp only [sourceNormSquare, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at hbound ⊢
  exact add_le_add le_rfl hbound

end ContinuousFlexibility.Radial
