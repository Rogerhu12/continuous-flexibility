import ContinuousFlexibility.Analysis.N07aAngularConstruction

/-!
# N07a: the original inverse has all angular orders and material weights

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 489–635.
Task: `docs/tasks/N07a-Angular.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

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
  have h01 : N01Properties A.val T S C base loss ε := h06.1.1.1.1.1
  have h02 : N02Properties A.val T S C R base ε := h06.1.1.1.1.2
  have h03 : N03Properties A.val T S C R L base ε := h06.1.1.1.2
  have h04 : N04Properties A.val T S C L K base loss ε := h06.1.1.2.2.2.2.1
  have hprimitive : CanonicalGeometry.PrimitiveGeometryProperties A.val T S C L K base ε :=
    h06.1.1.2.2.2.2.2
  exact n07a_angular_construction A.property.1 A.property.2.2.2.1 hS hT
    h01 h02 h03 h04 hprimitive.2.2.1 hprimitive.2.2.2.1
    hprimitive.2.1 hprimitive.1 hprimitive.2.2.2.2.1 h06.1.2 h06.2

end ContinuousFlexibility.Blueprint
