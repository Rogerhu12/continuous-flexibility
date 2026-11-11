import ContinuousFlexibility.Statements.N07aRegularity

/-!
# N07a: the original inverse has all angular orders and material weights

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 489–635.
Task: `docs/tasks/N07a-Angular.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

variable (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
  (C : NonlinearGeometryData S) (R : ReturnEquationData S)
  (L : ReturnCorrectionData S) (K : CanonicalData S) (V : VolumeModelData S K)
  (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
  (base loss : ℕ) (ε : ℝ)

theorem N07aAngular
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h06 : NonlinearPropertiesThrough06 A.val T S C R L K V b B P base loss ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      N07aAngularProperties S C K V b B P base' ε' := by
  sorry

end ContinuousFlexibility.Blueprint
