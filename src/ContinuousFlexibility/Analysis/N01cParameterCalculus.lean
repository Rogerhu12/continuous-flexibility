module

public import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus

/-!
# Parameter calculus for the actual finite coefficient inputs

Precomposition by a continuous linear map pulls every direction back by
that same map.  This applies to the projection from the joint state and
real parameter to the state; no inverse or norm on the state is needed.
Scalar products are obtained by composing the genuine two-input tower
with the smooth multiplication map on a finite-dimensional space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

section LinearPrecomposition

variable {E E' F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Pullback of the actual directional tower by any continuous linear map. -/
def smoothDirections_precompCLM {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (L : E' →L[ℝ] E) :
    SmoothDirections (L ⁻¹' U) (f ∘ L) where
  open_domain := J.open_domain.preimage L.continuous
  D := fun n y => (J.D n (L y)).compContinuousLinearMap (fun _ => L)
  zero := by
    intro y hy
    have e : (fun i : Fin 0 => L (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → E) := by
      funext i
      exact i.elim0
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_apply]
    rw [e]
    exact J.zero (L y) hy
  continuous := by
    intro n
    have hg : Continuous (fun q : E' × (Fin n → E') =>
        (L q.1, fun i => L (q.2 i))) :=
      (L.continuous.comp continuous_fst).prodMk
        (continuous_pi fun i => L.continuous.comp ((continuous_apply i).comp continuous_snd))
    have hm : MapsTo (fun q : E' × (Fin n → E') => (L q.1, fun i => L (q.2 i)))
        ((L ⁻¹' U) ×ˢ (univ : Set (Fin n → E'))) (U ×ˢ univ) :=
      fun _ hq => ⟨hq.1, mem_univ _⟩
    exact (J.continuous n).comp hg.continuousOn hm
  derivative := by
    intro n y hy v w
    have h := J.derivative n (L y) hy (fun i => L (v i)) (L w)
    have e : (fun i => L ((Fin.cons w v : Fin (n + 1) → E') i)) =
        (Fin.cons (L w) (fun i => L (v i)) : Fin (n + 1) → E) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at h ⊢
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, e, map_add, map_smul]
    exact h

/-- The pulled-back tower retains the exact multilinear input formula. -/
theorem smoothDirections_precompCLM_D_apply {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (L : E' →L[ℝ] E)
    (n : ℕ) (y : E') (v : Fin n → E') :
    (smoothDirections_precompCLM J L).D n y v =
      J.D n (L y) (fun i => L (v i)) := rfl

end LinearPrecomposition

section LinearPostcomposition

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- Linear postcomposition transports the genuine tower term by term. -/
def smoothDirections_postcompCLM {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (L : F →L[ℝ] G) :
    SmoothDirections U (L ∘ f) where
  open_domain := J.open_domain
  D := fun n x => L.compContinuousMultilinearMap (J.D n x)
  zero := by
    intro x hx
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply] using congrArg (fun y : F => L y) (J.zero x hx)
  continuous := by
    intro n
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply] using L.continuous.comp_continuousOn' (J.continuous n)
  derivative := by
    intro n x hx v w
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply] using (J.derivative n x hx v w).clm_comp L

theorem smoothDirections_postcompCLM_D_apply {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (L : F →L[ℝ] G)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirections_postcompCLM J L).D n x v = L (J.D n x v) := by
  change L.compContinuousMultilinearMap (J.D n x) v = _
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]

end LinearPostcomposition

section ScalarProducts

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Genuine scalar multiplication of two actual parameter towers. -/
def smoothDirections_realMul {U : Set E} {f g : E → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => f x * g x) := by
  let u : Fin 2 → E → ℝ := Fin.cases f (fun _ => g)
  let Ju : ∀ i : Fin 2, SmoothDirections U (u i) :=
    fun i => Fin.cases J (fun _ => K) i
  let JT := smoothDirections_scalarTuple J.open_domain Ju
  have hm : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 0 * y 1) :=
    (contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)
  let JM := smoothDirections_contDiff_comp JT isOpen_univ hm.contDiffOn
    (fun _ _ => mem_univ _)
  exact JM.congr (fun _ _ => rfl)

def smoothDirections_realConstMul {U : Set E} {f : E → ℝ}
    (c : ℝ) (J : SmoothDirections U f) :
    SmoothDirections U (fun x => c * f x) := by
  have hc : ContDiff ℝ ∞ (fun y : ℝ => c * y) := contDiff_const.mul contDiff_id
  let JC := smoothDirections_contDiff_comp J isOpen_univ hc.contDiffOn
    (fun _ _ => mem_univ _)
  exact JC.congr (fun _ _ => rfl)

end ScalarProducts

end ContinuousFlexibility.Analysis
