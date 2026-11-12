import ContinuousFlexibility.Analysis.N07bBridgeNeighborhood
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Blueprint node N07b

The physical scalar inverse is the chosen Banach solution. All witnesses
are retained; only the common low order and neighborhood radius change.
The coordinate stage retains its actual primitive geometric estimates,
and the weak physical relation uses the full angular period of RadialTest.

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 774–806.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem N07b (hN07a : N07aStatement) : N07Statement := by
  obtain ⟨A, T, S, C, R, L, K, V, b, B, P, G, base, loss, ε,
    hT, hS, hthrough, hG⟩ := hN07a
  have h04 : NonlinearPropertiesThrough04 A.val T S C R L K base loss ε :=
    hthrough.1.1
  have hK : N04PartA A.val S C K base ε := h04.2.2.2.2.1.1
  have hprimitive : CanonicalPrimitiveGeometry A.val T S C L K base ε :=
    h04.2.2.2.2.2.2
  have hstate : referenceStateConditions A.val S C := h04.1.1.1.2.2.1
  obtain ⟨base', ε', hb, hε', hεle, hbridge⟩ :=
    n07b_exists_scalarBanachBridge_on_smaller A.property.1 hT hS
      A.property.2.2.2.1 hK hthrough.1.2 hthrough.2 hG hprimitive hstate.stateSector
  exact ⟨A, T, S, C, R, L, K, V, b, B, P, G, base', loss, ε', hT, hS,
    n07b_NonlinearPropertiesThrough06_mono hT hthrough hb hε' hεle,
    n07b_ScalarInverseProperties_mono hG hb hεle, hbridge⟩

#print axioms ContinuousFlexibility.Blueprint.N07b

end ContinuousFlexibility.Blueprint
