module

public import ContinuousFlexibility.Analysis.N07aFixedDirection
public import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# A fixed derivative retains the uniform neighborhood

The existing fixed-direction tower differentiates the actual map. Its
one-high estimate also remains uniform on the original domain, with
the original base and loss. The fixed vector only changes the numerical
constant at each spatial order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {f : E → F} {base loss : ℕ}

/-- The last slot is fixed before choosing the parameter order. In
particular, the domain, base and loss are independent of that order. -/
theorem n04Realization_uniformTower_fixedDirection
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p q U base loss f J) (w : E) :
    UniformScalarTowerEstimate p q U base loss
      (fun x => J.D 1 x (Fin.snoc Fin.elim0 w)) (n07aFixedDirectionTower J w) := by
  intro k s hs
  obtain ⟨C, hC, hbound⟩ := hJ (k + 1) s hs
  refine ⟨C * (p base w + p (s + loss) w),
    mul_nonneg hC (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)), ?_⟩
  intro x hx v
  rw [n07aFixedDirectionTower_D_apply]
  calc
    _ ≤ C * tameJetSize p (k + 1) s loss base x (Fin.snoc v w) :=
      hbound x hx _
    _ ≤ C * ((p base w + p (s + loss) w) * tameJetSize p k s loss base x v) :=
      mul_le_mul_of_nonneg_left (n07a_tameJetSize_snoc_le p k s loss base x w v) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- Keep the supplied uniform tower when taking its fixed derivative. -/
theorem n04Realization_fixedNeighborhood_fixedDirection
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p q U base loss f J) (w : E) :
    FixedNeighborhoodSmoothTame p q U base loss
      (fun x => J.D 1 x (Fin.snoc Fin.elim0 w)) :=
  fixedNeighborhoodSmoothTame_of_uniform (n07aFixedDirectionTower J w)
    (n04Realization_uniformTower_fixedDirection J hJ w)

end ContinuousFlexibility.Analysis
