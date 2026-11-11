import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.SolveNewtonBridge

/-!
# Reflection and periodicity of the actual parameter coefficient jets

Uniqueness of the genuine directional towers propagates the existing
pointwise identities. In particular, each parameter derivative has odd
mixed coefficient and even angular coefficient, and both remain periodic.
No symmetry is imposed separately on a candidate formal derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

section JetIdentity

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [T2Space G]
  {U : Set E} {f : E → F} {g : E → G}

theorem SmoothDirections.jets_eq_of_postcomp
    (J : SmoothDirections U f) (K : SmoothDirections U g) (L : F →L[ℝ] G)
    (hfg : EqOn (fun x => L (f x)) g U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = L (J.D n x v) := by
  have h := K.unique ((solveSmoothDirectionsPostcomp J L).congrOn hfg) n x hx
  exact congrArg (fun A : E [×n]→L[ℝ] G => A v) h

end JetIdentity

/-- The coefficient pair transforms by a fixed continuous linear map. -/
def returnCoefficientReflectionLinear : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (-ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem returnCoefficientReflectionLinear_apply (q : ℝ × ℝ) :
    returnCoefficientReflectionLinear q = (-q.1, q.2) := rfl

section ActualJets

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {U : Set E}

theorem returnCorrectionCoefficientError_jets_reflection
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : E → AnnularState S × ℝ) (ρ : E → CircleSpace S)
    (J : ∀ p : PolarPoint, SmoothDirections U
      (fun x => returnCorrectionCoefficientError D S C R χ (z x) p (ρ x)))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (r θ : ℝ) :
    (J (r, -θ)).D n x v =
      (-((J (r, θ)).D n x v).1, ((J (r, θ)).D n x v).2) := by
  apply (J (r, θ)).jets_eq_of_postcomp (J (r, -θ))
    returnCoefficientReflectionLinear ?_ n x hx v
  intro y hy
  apply Prod.ext
  · exact (returnCorrectionCoefficientError_reflection hS C R χ
      (z y) (ρ y) r θ).1.symm
  · exact (returnCorrectionCoefficientError_reflection hS C R χ
      (z y) (ρ y) r θ).2.symm

theorem N01Properties.returnCorrectionCoefficientError_jets_periodic
    {base loss : ℕ} {ε : ℝ} (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (z : E → AnnularState S × ℝ) (ρ : E → CircleSpace S)
    (hz : MapsTo z U (stateNeighborhood S C base ε))
    (hs : ∀ x ∈ U, stateSector S (z x).1)
    (J : ∀ p : PolarPoint, SmoothDirections U
      (fun x => returnCorrectionCoefficientError D S C R χ (z x) p (ρ x)))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (r θ : ℝ) :
    (J (r, θ + Real.pi)).D n x v = (J (r, θ)).D n x v := by
  apply (J (r, θ)).jets_eq_of_postcomp (J (r, θ + Real.pi))
    (ContinuousLinearMap.id ℝ (ℝ × ℝ)) ?_ n x hx v
  intro y hy
  exact (hN.returnCorrectionCoefficientError_periodic hS R χ
    (hz hy) (hs y hy) hχ (ρ y) r θ).symm

end ActualJets

end ContinuousFlexibility.Statements
