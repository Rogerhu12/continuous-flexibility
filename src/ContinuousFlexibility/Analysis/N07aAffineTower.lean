module

public import ContinuousFlexibility.Analysis.SolveNewtonBridge

/-!
# Actual directional towers on an affine parameter slice

Translation of the base point and a continuous linear tangent inclusion
transport genuine difference quotients directly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

def n07aSmoothDirectionsAffine {U : Set Y} {f : Y → Z}
    (J : SmoothDirections U f) (c : Y) (L : X →L[ℝ] Y) :
    SmoothDirections ((fun x => c + L x) ⁻¹' U) (fun x => f (c + L x)) where
  open_domain := J.open_domain.preimage (continuous_const.add L.continuous)
  D := fun n x => (J.D n (c + L x)).compContinuousLinearMap (fun _ => L)
  zero := by
    intro x hx
    have e : (fun i : Fin 0 => L (Fin.elim0 i)) = Fin.elim0 := by
      funext i
      exact i.elim0
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, e] using
      J.zero (c + L x) hx
  continuous := by
    intro n
    have hc : Continuous (fun p : X × (Fin n → X) =>
        (c + L p.1, fun i => L (p.2 i))) :=
      (continuous_const.add (L.continuous.comp continuous_fst)).prodMk
        (continuous_pi fun i => L.continuous.comp ((continuous_apply i).comp continuous_snd))
    exact (J.continuous n).comp hc.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)
  derivative := by
    intro n x hx v w
    have e : (fun i => L ((Fin.cons w v : Fin (n + 1) → X) i)) =
        (Fin.cons (L w) (fun i => L (v i)) : Fin (n + 1) → Y) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    have hd := J.derivative n (c + L x) hx (fun i => L (v i)) (L w)
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, e,
      map_add, map_smul, add_assoc] using hd

theorem n07aSmoothDirectionsAffine_D {U : Set Y} {f : Y → Z}
    (J : SmoothDirections U f) (c : Y) (L : X →L[ℝ] Y)
    (k : ℕ) (x : X) (v : Fin k → X) :
    (n07aSmoothDirectionsAffine J c L).D k x v =
      J.D k (c + L x) (fun i => L (v i)) := rfl

end ContinuousFlexibility.Analysis
