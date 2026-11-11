import ContinuousFlexibility.Analysis.CoupledCircleJointJetAlgebra
import ContinuousFlexibility.Analysis.TameJetComposition
import ContinuousFlexibility.Statements.Analysis

/-!
# Genuine joint derivatives of the circle kernel tower

The coefficient derivative changes the chart. Linearity accounts for
the single possible derivative of the outer function. All limits take
place in the original topological target.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y]

theorem coupled_lineDeriv_linear_family
    (A : X → X →ₗ[ℝ] Y) (hA : Continuous (fun z : X × X => A z.1 z.2))
    (x v u a : X) (d : Y)
    (hd : HasProjectiveLineDerivAt (fun ψ => A ψ v) d x u) :
    HasProjectiveLineDerivAt (fun z : X × X => A z.1 z.2)
      (d + A x a) (x, v) (u, a) := by
  have hpartial : Tendsto (fun t : ℝ => t⁻¹ • (A (x + t • u) v - A x v))
      (𝓝[≠] (0 : ℝ)) (𝓝 d) := by
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      zero_add, zero_smul, add_zero] using hd
  have hc : Continuous (fun t : ℝ => A (x + t • u) a) :=
    hA.comp ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
  have hfixed : Tendsto (fun t : ℝ => A (x + t • u) a)
      (𝓝[≠] (0 : ℝ)) (𝓝 (A x a)) := by
    simpa only [zero_smul, add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (hpartial.add hfixed).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  change t⁻¹ • (A (x + t • u) v - A x v) + A (x + t • u) a =
    t⁻¹ • (A (x + t • u) (v + t • a) - A x v)
  have he : A (x + t • u) (v + t • a) - A x v =
      (A (x + t • u) v - A x v) + t • A (x + t • u) a := by
    rw [map_add, map_smul]
    abel
  rw [he, smul_add, smul_smul, inv_mul_cancel₀ ht0, one_smul]

def coupledKernelOuterLinear {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y)
    (w : Fin n → X) : X →L[ℝ] Y := A.toContinuousLinearMap (Fin.cons 0 w) 0

theorem coupledKernelOuterLinear_apply {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y)
    (w : Fin n → X) (v : X) :
    coupledKernelOuterLinear A w v = A (Fin.cons v w) := by
  change A (Function.update (Fin.cons 0 w) 0 v) = _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

variable (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y)
  (hK : ∀ n, Continuous (fun z : X × (Fin (n + 1) → X) => K n z.1 z.2))
  (hline : ∀ n x v w u, HasProjectiveLineDerivAt
    (fun ψ => K n ψ (Fin.cons v w))
    (K (n + 1) x (Fin.cons v (Fin.cons u w))) x u)

include hK hline in
theorem coupledKernelBaseJoint_hasLineDerivAt (n : ℕ) (z h : X × X) (w : Fin n → X) :
    HasProjectiveLineDerivAt (fun y : X × X => K n y.1 (Fin.cons y.2 w))
      (K (n + 1) z.1 (Fin.cons z.2 (Fin.cons h.1 w)) +
        K n z.1 (Fin.cons h.2 w)) z h := by
  let A (ψ : X) : X →L[ℝ] Y := coupledKernelOuterLinear (K n ψ) w
  have hc : Continuous (fun y : X × X => (A y.1).toLinearMap y.2) := by
    have hm : Continuous (fun y : X × X =>
        (y.1, (Fin.cons y.2 w : Fin (n + 1) → X))) :=
      continuous_fst.prodMk
        (continuous_snd.finCons (A := fun _ : Fin (n + 1) => X) continuous_const)
    simpa only [Function.comp_def, A, ContinuousLinearMap.coe_coe,
      coupledKernelOuterLinear_apply] using
      (hK n).comp hm
  have hd : HasProjectiveLineDerivAt (fun ψ => (A ψ).toLinearMap z.2)
      (K (n + 1) z.1 (Fin.cons z.2 (Fin.cons h.1 w))) z.1 h.1 := by
    simpa only [A, ContinuousLinearMap.coe_coe, coupledKernelOuterLinear_apply] using
      hline n z.1 z.2 w h.1
  simpa only [A, ContinuousLinearMap.coe_coe, coupledKernelOuterLinear_apply] using
    coupled_lineDeriv_linear_family (fun ψ => (A ψ).toLinearMap) hc
      z.1 z.2 h.1 h.2 _ hd

include hK in
theorem coupledKernelJointJet_continuous (n : ℕ) :
    Continuous (fun z : (X × X) × (Fin n → X × X) =>
      coupledKernelJointJet K n z.1 z.2) := by
  have hbase (k : ℕ) : Continuous (fun z : (X × X) × (Fin k → X × X) =>
      K k z.1.1 (Fin.cons z.1.2 (fun i => (z.2 i).1))) := by
    have htail : Continuous (fun z : (X × X) × (Fin k → X × X) =>
        fun i : Fin k => (z.2 i).1) :=
      continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).fst)
    have hm : Continuous (fun z : (X × X) × (Fin k → X × X) =>
        (z.1.1, (Fin.cons z.1.2 (fun i => (z.2 i).1) : Fin (k + 1) → X))) :=
      continuous_fst.fst.prodMk
        (continuous_fst.snd.finCons (A := fun _ : Fin (k + 1) => X) htail)
    exact (hK k).comp hm
  cases n with
  | zero =>
    have he : (fun z : (X × X) × (Fin 0 → X × X) =>
        coupledKernelJointJet K 0 z.1 z.2) =
        (fun z => K 0 z.1.1 (Fin.cons z.1.2 (fun i => (z.2 i).1))) := rfl
    rw [he]
    exact hbase 0
  | succ n =>
    simp only [coupledKernelJointJet_succ_apply]
    apply (hbase (n + 1)).add
    apply continuous_finsetSum
    intro i _
    have htail : Continuous (fun z : (X × X) × (Fin (n + 1) → X × X) =>
        fun j : Fin n => (z.2 (i.succAbove j)).1) :=
      continuous_pi (fun j => ((continuous_apply (i.succAbove j)).comp continuous_snd).fst)
    have hm : Continuous (fun z : (X × X) × (Fin (n + 1) → X × X) =>
        (z.1.1, (Fin.cons (z.2 i).2 (fun j => (z.2 (i.succAbove j)).1) :
          Fin (n + 1) → X))) :=
      continuous_fst.fst.prodMk
        ((((continuous_apply i).comp continuous_snd).snd).finCons
          (A := fun _ : Fin (n + 1) => X) htail)
    exact (hK n).comp hm

private theorem coupled_cons_fst {n : ℕ} (u : X × X) (v : Fin n → X × X) :
    (fun i : Fin (n + 1) => ((Fin.cons u v : Fin (n + 1) → X × X) i).1) =
      Fin.cons u.1 (fun i => (v i).1) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem coupled_cons_omit {n : ℕ} (u : X × X)
    (v : Fin (n + 1) → X × X) (i : Fin (n + 1)) :
    (fun j : Fin (n + 1) =>
      ((Fin.cons u v : Fin (n + 2) → X × X) (i.succ.succAbove j)).1) =
      Fin.cons u.1 (fun j => (v (i.succAbove j)).1) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.succ_succAbove_zero, Fin.cons_zero]
  · simp only [Fin.succ_succAbove_succ, Fin.cons_succ]

private theorem coupled_cons_joint_value {n : ℕ}
    (A : (Fin (n + 3) → X) → Y) (B : (Fin (n + 2) → X) → Y)
    (v : X) (h : X × X) (w : Fin (n + 1) → X × X) :
    A (Fin.cons v (fun i : Fin (n + 2) =>
      ((Fin.cons h w : Fin (n + 2) → X × X) i).1)) +
        ∑ i : Fin (n + 2), B (Fin.cons
          (((Fin.cons h w : Fin (n + 2) → X × X) i).2)
          (fun j : Fin (n + 1) =>
            ((Fin.cons h w : Fin (n + 2) → X × X) (i.succAbove j)).1)) =
      (A (Fin.cons v (Fin.cons h.1 (fun i => (w i).1))) +
        B (Fin.cons h.2 (fun i => (w i).1))) +
          ∑ i : Fin (n + 1), B (Fin.cons (w i).2
            (Fin.cons h.1 (fun j : Fin n => (w (i.succAbove j)).1))) := by
  rw [coupled_cons_fst, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.zero_succAbove,
    coupled_cons_omit, add_assoc]

include hK hline in
theorem coupledKernelJointJet_hasLineDerivAt (n : ℕ) (z h : X × X)
    (w : Fin n → X × X) :
    HasProjectiveLineDerivAt (fun y => coupledKernelJointJet K n y w)
      (coupledKernelJointJet K (n + 1) z (Fin.cons h w)) z h := by
  cases n with
  | zero =>
    have hd := coupledKernelBaseJoint_hasLineDerivAt K hK hline 0 z h Fin.elim0
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    have hnil : (fun i : Fin 0 => (Fin.elim0 i : X × X).1) =
        (Fin.elim0 : Fin 0 → X) := Subsingleton.elim _ _
    simpa only [coupledKernelJointJet_zero_apply, coupledKernelJointJet_succ_apply,
      coupled_cons_fst, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
      Fin.cons_succ, Fin.zero_succAbove, hnil, add_zero] using hd
  | succ n =>
    have hbase := coupledKernelBaseJoint_hasLineDerivAt K hK hline (n + 1) z h
      (fun i => (w i).1)
    have hterm (i : Fin (n + 1)) : HasProjectiveLineDerivAt
        (fun y : X × X => K n y.1
          (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1)))
        (K (n + 1) z.1 (Fin.cons (w i).2
          (Fin.cons h.1 (fun j => (w (i.succAbove j)).1)))) z h :=
      HasProjectiveLineDerivAt.comp_linear (LinearMap.fst ℝ X X)
        (hline n z.1 (w i).2 (fun j => (w (i.succAbove j)).1) h.1)
    have hsum : HasProjectiveLineDerivAt
        (fun y : X × X => ∑ i : Fin (n + 1), K n y.1
          (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1)))
        (∑ i : Fin (n + 1), K (n + 1) z.1 (Fin.cons (w i).2
          (Fin.cons h.1 (fun j => (w (i.succAbove j)).1)))) z h :=
      HasProjectiveCurveDerivAt.finset_sum Finset.univ (fun i _ => hterm i)
    have hfun : (fun y : X × X => coupledKernelJointJet K (n + 1) y w) =
        (fun y : X × X => K (n + 1) y.1 (Fin.cons y.2 (fun i => (w i).1)) +
          ∑ i : Fin (n + 1), K n y.1
            (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1))) :=
      funext (fun y => coupledKernelJointJet_succ_apply K n y w)
    have hvalue : coupledKernelJointJet K (n + 1 + 1) z (Fin.cons h w) =
        (K (n + 1 + 1) z.1 (Fin.cons z.2 (Fin.cons h.1 (fun i => (w i).1))) +
          K (n + 1) z.1 (Fin.cons h.2 (fun i => (w i).1))) +
          ∑ i : Fin (n + 1), K (n + 1) z.1 (Fin.cons (w i).2
            (Fin.cons h.1 (fun j => (w (i.succAbove j)).1))) := by
      exact (coupledKernelJointJet_succ_apply K (n + 1) z (Fin.cons h w)).trans
        (coupled_cons_joint_value (K (n + 1 + 1) z.1) (K (n + 1) z.1) z.2 h w)
    exact (congrArg₂ (fun (f : X × X → Y) (d : Y) =>
      HasProjectiveLineDerivAt f d z h) hfun hvalue).mpr
        (HasProjectiveLineDerivAt.add hbase hsum)

def coupledKernelSmoothDirections :
    Statements.SmoothDirections univ (fun z : X × X => K 0 z.1 (Fin.cons z.2 Fin.elim0)) where
  open_domain := isOpen_univ
  D := coupledKernelJointJet K
  zero := fun z _ => coupledKernelJointJet_zero_apply K z Fin.elim0
  continuous := fun n => (coupledKernelJointJet_continuous K hK n).continuousOn
  derivative := fun n z _ w u => coupledKernelJointJet_hasLineDerivAt K hK hline n z u w

end ContinuousFlexibility.Analysis
