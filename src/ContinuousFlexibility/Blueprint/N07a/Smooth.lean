import ContinuousFlexibility.Statements.N07aRegularity

/-!
# N07a: the smooth tame family of the same physical inverse

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 790–815.
Task: `docs/tasks/N07a-Smooth.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

variable (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
  (C : NonlinearGeometryData S) (R : ReturnEquationData S)
  (L : ReturnCorrectionData S) (K : CanonicalData S) (V : VolumeModelData S K)
  (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
  (base loss : ℕ) (ε : ℝ)

theorem N07aSmooth
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h06 : NonlinearPropertiesThrough06 A.val T S C R L K V b B P base loss ε)
    (G : ScalarInverseData S)
    (hLinear : ScalarLinearInverseProperties A.val S C L G base ε)
    (hTame : H01Statement ∧ H02Statement) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ScalarInverseProperties A.val S C L G base' ε' := by
  sorry

end ContinuousFlexibility.Blueprint
