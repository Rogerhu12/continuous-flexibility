import ContinuousFlexibility.Statements.N07aRegularity

/-!
# N07a: the normalized physical linear inverse and its fixed loss

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 637–790.
Task: `docs/tasks/N07a-Linear.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

variable (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
  (C : NonlinearGeometryData S) (R : ReturnEquationData S)
  (L : ReturnCorrectionData S) (K : CanonicalData S) (V : VolumeModelData S K)
  (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
  (base loss : ℕ) (ε : ℝ)

theorem N07aLinear
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h06 : NonlinearPropertiesThrough06 A.val T S C R L K V b B P base loss ε)
    (hAngular : N07aAngularProperties S C K V b B P base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ G : ScalarInverseData S,
        ScalarLinearInverseProperties A.val S C L G base' ε' := by
  sorry

end ContinuousFlexibility.Blueprint
