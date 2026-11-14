import ContinuousFlexibility.Analysis.WholeComponentFieldSelection

/-!
# Symmetries using only the selected component domains

The actual selector tests only the radius. Its chosen index comes with
membership in the corresponding closed negative or open positive piece.
Thus no symmetry of a stored endpoint field outside that piece is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeComponentField_equivariant_on_components
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {E : Type*} (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E) (σ : PolarPoint → PolarPoint) (Ψ : E → E)
    (hr : ∀ p, (σ p).1 = p.1)
    (hneg : ∀ m p, p.1 ∈ Icc (C.left m) (C.right m) →
      Fneg m (σ p) = Ψ (Fneg m p))
    (hpos : ∀ i p, p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) →
      Fpos i (σ p) = Ψ (Fpos i p))
    (hfb : ∀ p, fallback (σ p) = Ψ (fallback p)) (p : PolarPoint) :
    n04WholeComponentField C Fneg Fpos fallback (σ p) =
      Ψ (n04WholeComponentField C Fneg Fpos fallback p) := by
  classical
  simp only [n04WholeComponentField, hr p]
  split_ifs with hn hp
  · exact hneg (Classical.choose hn) p (Classical.choose_spec hn)
  · exact hpos (Classical.choose hp) p (Classical.choose_spec hp)
  · exact hfb p

end ContinuousFlexibility.Analysis
