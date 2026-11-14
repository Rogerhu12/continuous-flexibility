module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Analysis.N04bOpticalFieldRealization

/-!
# N04b: realization of the actual smooth corrected field

Retain one complete N01--N03 construction and realize its actual corrected
coefficients with spatial smoothness, angular periodicity, a positive radial
coefficient and strict hyperbolicity on each entire negative component.
The explicit correction also retains the actual radial optical flow at
the reference state on every closed component.
The output does not contain canonical coordinates or assume their existence.

The existential witnesses may be chosen again. A proof cannot silently
assume regularity of an arbitrary coefficient representative in N03.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, the type
completion and optical residual completion preceding lines 992--1003.
Task: docs/tasks/N04b-FieldRealization.md.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04bFieldRealization (hN04a : N04aStatement) :
    N04bFieldDataStatement := by
  rcases hN04a with
    ⟨A, T, S, C, R, _L, _K, base, loss, ε, hT, hS, h03, _hA⟩
  have hN : N01Properties A.val T S C base loss ε := h03.1.1
  have hR : N02Properties A.val T S C R base ε := h03.1.2
  obtain ⟨base', ε', hb, _hε', hε, hN', ⟨Q⟩⟩ :=
    hN.exists_n04b_opticalCutoffData hS hT
  have hR' : N02Properties A.val T S C R base' ε' :=
    hR.restrict_neighborhood hb hε
  obtain ⟨E, hL, hfield⟩ := Q.exists_field hN' hS hT hR'
  refine ⟨A, T, S, C, R, Q.field E, base', loss, ε', hT, hS, ?_, hfield⟩
  exact ⟨⟨hN', hR'⟩, hL⟩

/--
info: 'ContinuousFlexibility.Blueprint.N04bFieldRealization' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N04bFieldRealization

end ContinuousFlexibility.Blueprint
