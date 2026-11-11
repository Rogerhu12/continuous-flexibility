import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Blueprint.N07a.Angular
import ContinuousFlexibility.Blueprint.N07a.Linear
import ContinuousFlexibility.Blueprint.N07a.Smooth
import ContinuousFlexibility.Analysis.N07aConstructionRestriction

/-!
# Blueprint node N07a

The three subnodes prove the angular/material estimate, the actual physical
linear inverse, and its smooth tame parameter dependence. The original
statement and the original N06 construction are retained throughout.

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 489–815.
Task file: `docs/tasks/N07a.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem N07a (hN06 : N06Statement) (hTame : H01Statement ∧ H02Statement) : N07aStatement := by
  obtain ⟨A, T, S, C, R, L, K, V, b, B, P, base, loss, ε, hT, hS, h06⟩ := hN06
  obtain ⟨base₁, hb₁, ε₁, he₁, he₁ε, hAngular⟩ :=
    N07aAngular A T S C R L K V b B P base loss ε hT hS h06
  have h06₁ := n07a_through06_restrict hT h06 hb₁ he₁ε he₁
  obtain ⟨base₂, hb₂, ε₂, he₂, he₂ε, G, hLinear⟩ :=
    N07aLinear A T S C R L K V b B P base₁ loss ε₁ hT hS h06₁ hAngular
  have h06₂ := n07a_through06_restrict hT h06₁ hb₂ he₂ε he₂
  obtain ⟨base₃, hb₃, ε₃, he₃, he₃ε, hSmooth⟩ :=
    N07aSmooth A T S C R L K V b B P base₂ loss ε₂ hT hS h06₂ G hLinear hTame
  have h06₃ := n07a_through06_restrict hT h06₂ hb₃ he₃ε he₃
  exact ⟨A, T, S, C, R, L, K, V, b, B, P, G, base₃, loss, ε₃, hT, hS, h06₃, hSmooth⟩

end ContinuousFlexibility.Blueprint
