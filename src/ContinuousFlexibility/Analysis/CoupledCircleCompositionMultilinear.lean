import ContinuousFlexibility.Analysis.CoupledCircleCompositionCurveDerivative
import ContinuousFlexibility.Analysis.CoupledCircleAngularDerivative
import ContinuousFlexibility.Analysis.SpacesNemytskiiSmooth

/-!
# Multilinear circle kernels and their joint continuity

The outer circle function and all direction factors are linear inputs.
The genuine derivative in the chart parameter, together with the local
product bounds, proves joint continuity in the original projective
topology.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}

def coupledCircleIteratedDerivativeLinear (hM : IsCircleModel T γ M) :
    ℕ → M.Space →ₗ[ℝ] M.Space
  | 0 => LinearMap.id
  | n + 1 => (coupledCircleDerivativeLinear hM).comp (coupledCircleIteratedDerivativeLinear hM n)

theorem coupledCircleIteratedDerivativeLinear_decode (hM : IsCircleModel T γ M)
    (n : ℕ) (v : M.Space) (m : ℕ) :
    M.decode (coupledCircleIteratedDerivativeLinear hM n v) m =
      iteratedDeriv n (M.decode v m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change M.decode (coupledCircleDerivativeLinear hM
      (coupledCircleIteratedDerivativeLinear hM n v)) m = _
    exact (coupledCircleDerivativeLinear_decode hM
      (coupledCircleIteratedDerivativeLinear hM n v) m).trans
        ((congrArg (fun f : ℝ → ℝ => deriv f) ih).trans
          (iteratedDeriv_succ (n := n) (f := M.decode v m)).symm)

theorem coupled_fin_cons_head_tail {X : Type*} {k : ℕ} (v : Fin (k + 1) → X) :
    Fin.cons (v 0) (Fin.tail v) = v := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def coupledCircleKernelFieldMultilinear (hM : IsCircleModel T γ M)
    (r k : ℕ) (ψ : M.Space) :
    MultilinearMap ℝ (fun _ : Fin (k + 1) => M.Space) (ℕ → ℝ → ℝ) :=
  MultilinearMap.pi (fun m => MultilinearMap.pi (fun θ =>
    (MultilinearMap.mkPiAlgebra ℝ (Fin (k + 1)) ℝ).compLinearMap
      (Fin.cons
        ((LinearMap.proj (θ + M.decode ψ m θ)).comp
          ((LinearMap.proj m).comp
            (M.decode.comp (coupledCircleIteratedDerivativeLinear hM r))))
        (fun _ : Fin k => (LinearMap.proj θ).comp ((LinearMap.proj m).comp M.decode)))))

theorem coupledCircleKernelFieldMultilinear_apply (hM : IsCircleModel T γ M)
    (r k : ℕ) (ψ : M.Space) (v : Fin (k + 1) → M.Space) :
    coupledCircleKernelFieldMultilinear hM r k ψ v =
      coupledCircleKernelField M r k ψ (v 0) (Fin.tail v) := by
  funext m θ
  change (∏ i : Fin (k + 1),
    ((Fin.cons
      ((LinearMap.proj (θ + M.decode ψ m θ)).comp
        ((LinearMap.proj m).comp (M.decode.comp (coupledCircleIteratedDerivativeLinear hM r))))
      (fun _ : Fin k => (LinearMap.proj θ).comp ((LinearMap.proj m).comp M.decode)) :
        Fin (k + 1) → (M.Space →ₗ[ℝ] ℝ)) i) (v i)) = _
  rw [Fin.prod_univ_succ]
  change M.decode (coupledCircleIteratedDerivativeLinear hM r (v 0)) m
    (θ + M.decode ψ m θ) * (∏ i : Fin k, M.decode (v i.succ) m θ) = _
  rw [coupledCircleIteratedDerivativeLinear_decode]
  rfl

variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

def coupledCircleKernelMultilinear (r k : ℕ) (ψ : M.Space) :
    MultilinearMap ℝ (fun _ : Fin (k + 1) => M.Space) M.Space where
  toFun v := coupledCircleKernel hD hT hγ hM hI r k ψ (v 0) (Fin.tail v)
  map_update_add' := by
    intro _ v i x y
    apply hM.2.2.2.2.2.1
    simp only [map_add, coupledCircleKernel_decode,
      ← coupledCircleKernelFieldMultilinear_apply hM]
    exact (coupledCircleKernelFieldMultilinear hM r k ψ).map_update_add v i x y
  map_update_smul' := by
    intro _ v i c x
    apply hM.2.2.2.2.2.1
    simp only [map_smul, coupledCircleKernel_decode,
      ← coupledCircleKernelFieldMultilinear_apply hM]
    exact (coupledCircleKernelFieldMultilinear hM r k ψ).map_update_smul v i c x

theorem coupledCircleKernelMultilinear_apply (r k : ℕ) (ψ : M.Space)
    (v : Fin (k + 1) → M.Space) :
    coupledCircleKernelMultilinear hD hT hγ hM hI r k ψ v =
      coupledCircleKernel hD hT hγ hM hI r k ψ (v 0) (Fin.tail v) := rfl

def coupledCircleKernelMultilinearDerivative (r k : ℕ) (ψ : M.Space)
    (v : Fin (k + 2) → M.Space) : M.Space :=
  coupledCircleKernel hD hT hγ hM hI (r + 1) (k + 1) ψ (v 1)
    (Fin.cons (v 0) (fun i : Fin k => v i.succ.succ))

theorem coupledCircleKernelMultilinear_continuous (r k : ℕ) :
    Continuous (fun z : M.Space × (Fin (k + 1) → M.Space) =>
      coupledCircleKernelMultilinear hD hT hγ hM hI r k z.1 z.2) := by
  have hexists := coupled_circle_kernel_coarse hD hT hγ hM hI
  let base : ℕ := hexists.choose
  have hb := hexists.choose_spec
  apply spaces_projective_parameter_multilinear_continuous (fun s => M.level s) M.bond base
    (coupledCircleKernelMultilinear hD hT hγ hM hI r k)
    (coupledCircleKernelMultilinearDerivative hD hT hγ hM hI r k)
  · intro ψ v u
    change HasProjectiveLineDerivAt
      (fun x : M.Space => coupledCircleKernelMultilinear hD hT hγ hM hI r k x v)
      (coupledCircleKernelMultilinearDerivative hD hT hγ hM hI r k ψ (Fin.cons u v)) ψ u
    simpa only [coupledCircleKernelMultilinear_apply,
      coupledCircleKernelMultilinearDerivative, Fin.cons_zero, Fin.cons_one, Fin.cons_succ] using
      coupledCircleKernel_hasProjectiveLineDerivAt hD hT hγ hM hI r k ψ u (v 0) (Fin.tail v)
  · intro s R hR
    have hdata := hb r k s R hR
    let N : ℕ := hdata.choose
    have hN : base ≤ N := hdata.choose_spec.1
    let C : ℝ := hdata.choose_spec.2.choose
    have hC : 0 ≤ C := hdata.choose_spec.2.choose_spec.1
    have hc : ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (v : M.Space) (w : Fin k → M.Space),
          M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ v w) ≤
            C * (1 + M.grading N ψ) *
              ∏ i : Fin (k + 1), M.grading N ((Fin.cons v w : Fin (k + 1) → M.Space) i) :=
      hdata.choose_spec.2.choose_spec.2
    refine ⟨N, hN, C, hC, fun ψ hψ v => ?_⟩
    change M.grading s (coupledCircleKernelMultilinear hD hT hγ hM hI r k ψ v) ≤
      C * (1 + M.grading N ψ) * ∏ i : Fin (k + 1), M.grading N (v i)
    simpa only [coupledCircleKernelMultilinear_apply, coupled_fin_cons_head_tail] using
      hc ψ hψ (v 0) (Fin.tail v)
  · intro s R hR
    have hdata := hb (r + 1) (k + 1) s R hR
    let N : ℕ := hdata.choose
    have hN : base ≤ N := hdata.choose_spec.1
    let C : ℝ := hdata.choose_spec.2.choose
    have hC : 0 ≤ C := hdata.choose_spec.2.choose_spec.1
    have hc : ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (v : M.Space) (w : Fin (k + 1) → M.Space),
          M.grading s (coupledCircleKernel hD hT hγ hM hI (r + 1) (k + 1) ψ v w) ≤
            C * (1 + M.grading N ψ) *
              ∏ i : Fin (k + 2), M.grading N ((Fin.cons v w : Fin (k + 2) → M.Space) i) :=
      hdata.choose_spec.2.choose_spec.2
    refine ⟨N, hN, C, hC, fun ψ hψ v => ?_⟩
    have h := hc ψ hψ (v 1) (Fin.cons (v 0) (fun i : Fin k => v i.succ.succ))
    apply h.trans_eq
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
    ac_rfl

def coupledCircleKernelContinuousMultilinear (r k : ℕ) (ψ : M.Space) :
    M.Space [×(k + 1)]→L[ℝ] M.Space :=
  spacesContinuousMultilinearMapOfContinuous
    (coupledCircleKernelMultilinear hD hT hγ hM hI r k ψ)
    (spaces_continuous_fixed_first
      (fun (x : M.Space) (v : Fin (k + 1) → M.Space) =>
        coupledCircleKernelMultilinear hD hT hγ hM hI r k x v)
      (coupledCircleKernelMultilinear_continuous hD hT hγ hM hI r k) ψ)

theorem coupledCircleKernelContinuousMultilinear_apply (r k : ℕ) (ψ : M.Space)
    (v : Fin (k + 1) → M.Space) :
    coupledCircleKernelContinuousMultilinear hD hT hγ hM hI r k ψ v =
      coupledCircleKernel hD hT hγ hM hI r k ψ (v 0) (Fin.tail v) := rfl

end ContinuousFlexibility.Statements
