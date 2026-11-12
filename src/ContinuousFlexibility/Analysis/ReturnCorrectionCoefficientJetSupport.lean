import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientJetSymmetry
import ContinuousFlexibility.Analysis.ReturnOpticalCutoffPatching

/-!
# Spatial support and locality of the actual coefficient parameter jets

All statements concern the given genuine parameter towers. Uniqueness
transfers a spatially local identity of the actual coefficient maps to
every parameter order. The zero neighborhoods are uniform over the
parameter domain because the cutoff family is independent of state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

section Locality

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
  {U : Set E} {f g : E → F}

theorem SmoothDirections.jets_eq_of_eqOn
    (J : SmoothDirections U f) (K : SmoothDirections U g) (hfg : EqOn f g U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    J.D n x v = K.D n x v := by
  have heq := J.unique (K.congrOn (fun y hy => (hfg hy).symm)) n x hx
  exact congrArg (fun A : E [×n]→L[ℝ] F => A v) heq

theorem SmoothDirections.jets_zero_of_eqOn_zero
    (J : SmoothDirections U f) (hf : EqOn f (fun _ => 0) U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    J.D n x v = 0 := by
  have hh := J.jets_eq_of_postcomp J (0 : F →L[ℝ] F)
    (fun y hy => by
      change (0 : F) = f y
      exact (hf hy).symm) n x hx v
  simpa only [ContinuousLinearMap.zero_apply] using hh

theorem SmoothDirections.jets_eventuallyEq_of_spatial_eqOn
    {P : Type*} [TopologicalSpace P] {f g : P → E → F}
    (J : ∀ p, SmoothDirections U (f p)) (K : ∀ p, SmoothDirections U (g p))
    {p : P} (hfg : ∀ᶠ q in 𝓝 p, EqOn (f q) (g q) U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (fun q => (J q).D n x v) =ᶠ[𝓝 p] fun q => (K q).D n x v := by
  filter_upwards [hfg] with q hq
  exact (J q).jets_eq_of_eqOn (K q) hq n x hx v

end Locality

section ActualCoefficient

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {U : Set E}
  (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
  (z : E → AnnularState S × ℝ) (ρ : E → CircleSpace S)
  (J : ∀ p : PolarPoint, SmoothDirections U
    (fun x => returnCorrectionCoefficientError D S C R χ (z x) p (ρ x)))

theorem returnCorrectionCoefficientError_jets_zero_of_inactive
    (p : PolarPoint)
    (hinactive : ¬ ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (J p).D n x v = 0 := by
  classical
  apply (J p).jets_zero_of_eqOn_zero _ n x hx v
  intro y hy
  simp only [returnCorrectionCoefficientError, dif_neg hinactive, LinearMap.zero_apply]

theorem returnCorrectionCoefficientError_jets_eventually_zero
    {p : PolarPoint} (hχ : ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (fun q => (J q).D n x v) =ᶠ[𝓝 p] fun _ => 0 := by
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hχ] with q hq
  apply returnCorrectionCoefficientError_jets_zero_of_inactive R χ z ρ J q _ n x hx v
  rintro ⟨m, _, hm⟩
  exact hm (hq m)

theorem returnCorrectionCoefficientError_jets_eq_local
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (K : SmoothDirections U
      (fun x => returnCorrectionLocalCoefficientError D S C R χ (z x) m p (ρ x)))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (J p).D n x v = K.D n x v := by
  apply (J p).jets_eq_of_eqOn K _ n x hx v
  intro y hy
  change returnCorrectionCoefficientError D S C R χ (z y) p (ρ y) =
    returnCorrectionLocalCoefficientError D S C R χ (z y) m p (ρ y)
  exact congrArg (fun L : CircleSpace S →ₗ[ℝ] (ℝ × ℝ) => L (ρ y))
    (returnCorrectionCoefficientError_eq_local hdisj R χ (z y) m p hp)

theorem N01Properties.returnCorrectionCoefficientError_jets_eventually_zero_of_nonnegative
    {base loss : ℕ} {ε : ℝ} (hN : N01Properties D T S C base loss ε)
    (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hpositive : 0 ≤ deriv D.w p.1)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (fun q => (J q).D n x v) =ᶠ[𝓝 p] fun _ => 0 :=
  returnCorrectionCoefficientError_jets_eventually_zero R χ z ρ J
    (hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hp.1 hpositive) n x hx v

end ActualCoefficient

end ContinuousFlexibility.Statements
