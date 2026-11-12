import ContinuousFlexibility.Analysis.WholeComponentCriticalCover

/-!
# Symmetries and physical range of the actual component selector

The selector only uses the physical radius. Every radius-preserving
action therefore commutes with it whenever it commutes with the actual
component fields and the fallback. The true component cover also
transfers the component range properties to the whole open annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n04WholeComponentField_equivariant {E : Type*}
    (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E) (σ : PolarPoint → PolarPoint) (ψ : E → E)
    (hr : ∀ p, (σ p).1 = p.1)
    (hneg : ∀ m p, Fneg m (σ p) = ψ (Fneg m p))
    (hpos : ∀ i p, Fpos i (σ p) = ψ (Fpos i p))
    (hfb : ∀ p, fallback (σ p) = ψ (fallback p)) (p : PolarPoint) :
    n04WholeComponentField C Fneg Fpos fallback (σ p) =
      ψ (n04WholeComponentField C Fneg Fpos fallback p) := by
  classical
  simp only [n04WholeComponentField, hr p]
  split_ifs
  · exact hneg _ p
  · exact hpos _ p
  · exact hfb p

theorem n04WholeComponentField_mapsTo_annulus
    (hN : N01Properties D T S C base loss ε)
    (Fneg : ℕ → PolarPoint → PolarPoint)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (fallback : PolarPoint → PolarPoint)
    (hneg : ∀ m, MapsTo (Fneg m)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hpos : ∀ i, MapsTo (Fpos i)
      (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ))
      (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ))) :
    MapsTo (n04WholeComponentField C Fneg Fpos fallback) (annularOpen D) (annularOpen D) := by
  have hD : RadialProfileGeometry D := (Classical.choose_spec hN.1.1).1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  intro p hp
  change p.1 ∈ radialCore D ∧ p.2 ∈ (univ : Set ℝ) at hp
  change (n04WholeComponentField C Fneg Fpos fallback p).1 ∈ radialCore D ∧
    (n04WholeComponentField C Fneg Fpos fallback p).2 ∈ (univ : Set ℝ)
  refine ⟨?_, mem_univ _⟩
  rcases n04_wholeComponent_cover hD hC hp.1 with ⟨m, hm⟩ | ⟨i, hi⟩
  · rw [n04WholeComponentField_eq_negative hN Fneg Fpos fallback hm]
    have hb := (hneg m ⟨hm, mem_univ _⟩).1
    exact ⟨(hC.1 m).1.trans_le hb.1, hb.2.trans_lt (hC.1 m).2.2⟩
  · rw [n04WholeComponentField_eq_positive hf hC Fneg Fpos fallback hi]
    have hb := (hpos i ⟨hi, mem_univ _⟩).1
    have hiBound := n04PositiveComponent_bounds hf i
    exact ⟨hiBound.1.trans_lt hb.1, hb.2.trans_le hiBound.2.2⟩

end ContinuousFlexibility.Analysis
