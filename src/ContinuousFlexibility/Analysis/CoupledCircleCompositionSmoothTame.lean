import ContinuousFlexibility.Analysis.CoupledCircleCompositionLocalTame
import ContinuousFlexibility.Analysis.CoupledCircleJointJetDerivative
import ContinuousFlexibility.Analysis.TamePairTopology

/-!
# Joint smooth tameness of the actual circle composition

The kernel tower differentiates both the chart displacement and the outer
circle function. Local affine estimates for these actual jets give the
frozen homogeneous smooth-tame bounds in the original sum grading.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators
open ContinuousFlexibility.Statements

private theorem coupled_joint_jet_coordinates_le
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (n s : ℕ) (z : (X × X) × (Fin n → X × X)) :
    p s z.1.1 ≤ jetGrading (pairGrading p p) n s z ∧
    p s z.1.2 ≤ jetGrading (pairGrading p p) n s z ∧
    (∀ i, p s (z.2 i).1 ≤ jetGrading (pairGrading p p) n s z) ∧
    (∀ i, p s (z.2 i).2 ≤ jetGrading (pairGrading p p) n s z) := by
  have hfst (x : X × X) : p s x.1 ≤ pairGrading p p s x := by
    rw [pairGrading_apply]
    exact le_add_of_nonneg_right (apply_nonneg _ _)
  have hsnd (x : X × X) : p s x.2 ≤ pairGrading p p s x := by
    rw [pairGrading_apply]
    exact le_add_of_nonneg_left (apply_nonneg _ _)
  have hbase : pairGrading p p s z.1 ≤ jetGrading (pairGrading p p) n s z := by
    rw [jetGrading_apply]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  have hdir (i : Fin n) : pairGrading p p s (z.2 i) ≤
      jetGrading (pairGrading p p) n s z := by
    rw [jetGrading_apply]
    exact (Finset.single_le_sum (fun j _ => apply_nonneg (pairGrading p p s) (z.2 j))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left (apply_nonneg _ _))
  exact ⟨(hfst z.1).trans hbase, (hsnd z.1).trans hbase,
    fun i => (hfst (z.2 i)).trans (hdir i),
    fun i => (hsnd (z.2 i)).trans (hdir i)⟩

private theorem coupled_joint_jet_grading_continuous
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : ∀ s, Continuous (p s)) (n s : ℕ) :
    Continuous (jetGrading (pairGrading p p) n s) := by
  have hbase : Continuous (fun z : (X × X) × (Fin n → X × X) =>
      p s z.1.1 + p s z.1.2) :=
    ((hp s).comp continuous_fst.fst).add ((hp s).comp continuous_fst.snd)
  have hdirs : Continuous (fun z : (X × X) × (Fin n → X × X) =>
      ∑ i, (p s (z.2 i).1 + p s (z.2 i).2)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hp s).comp (((continuous_apply i).comp continuous_snd).fst)).add
      ((hp s).comp (((continuous_apply i).comp continuous_snd).snd))
  have hsum := hbase.add hdirs
  change Continuous (fun z : (X × X) × (Fin n → X × X) =>
    (p s z.1.1 + p s z.1.2) + ∑ i, (p s (z.2 i).1 + p s (z.2 i).2)) at hsum
  change Continuous (fun z : (X × X) × (Fin n → X × X) =>
    jetGrading (pairGrading p p) n s z)
  simpa only [jetGrading_apply, pairGrading_apply] using hsum

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

theorem coupled_circleComposition_decode (ψ v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleKernel hD hT hγ hM hI 0 0 ψ v Fin.elim0) m θ =
      M.decode v m (θ + M.decode ψ m θ) := by
  simpa only [iteratedDeriv_zero, Fin.prod_univ_zero, mul_one] using
    coupledCircleKernel_decode_apply hD hT hγ hM hI 0 0 ψ v Fin.elim0 m θ

/-- Composition by a circle displacement is jointly smooth tame in the
displacement and the outer circle function, on their full original space. -/
theorem coupled_circleComposition_smoothTameOn :
    SmoothTameOn (pairGrading M.grading M.grading) M.grading univ
      (fun z : M.Space × M.Space =>
        coupledCircleKernel hD hT hγ hM hI 0 0 z.1 z.2 Fin.elim0) := by
  let K : ∀ n : ℕ, M.Space → M.Space [×(n + 1)]→L[ℝ] M.Space :=
    fun n ψ => coupledCircleKernelContinuousMultilinear hD hT hγ hM hI n n ψ
  have hc : ∀ n, Continuous
      (fun z : M.Space × (Fin (n + 1) → M.Space) => K n z.1 z.2) := by
    intro n
    simpa only [K, coupledCircleKernelContinuousMultilinear_apply,
      coupledCircleKernelMultilinear_apply] using
      coupledCircleKernelMultilinear_continuous hD hT hγ hM hI n n
  have hl : ∀ n x v w u, HasProjectiveLineDerivAt
      (fun ψ => K n ψ (Fin.cons v w))
      (K (n + 1) x (Fin.cons v (Fin.cons u w))) x u := by
    intro n x v w u
    simpa only [K, coupledCircleKernelContinuousMultilinear_apply,
      Fin.cons_zero, Fin.tail_cons] using
      coupledCircleKernel_hasProjectiveLineDerivAt hD hT hγ hM hI n n x u v w
  let J := coupledKernelSmoothDirections K hc hl
  let p := pairGrading M.grading M.grading
  have hmono : Monotone p := tamePairGrading_monotone
    (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _)
  have ht : WithSeminorms p := withSeminorms_pairGrading
    (withSeminorms_graded (fun s => M.level s) M.bond)
    (withSeminorms_graded (fun s => M.level s) M.bond)
  have hg : ∀ s, Continuous (M.grading s) :=
    (withSeminorms_graded (fun s => M.level s) M.bond).continuous_seminorm
  have hbase (n : ℕ) : LocallyTameOn (jetGrading p n) M.grading univ
      (fun z : (M.Space × M.Space) × (Fin n → M.Space × M.Space) =>
        K n z.1.1 (Fin.cons z.1.2 (fun i => (z.2 i).1))) := by
    have hh := coupled_circle_kernel_locallyTame hD hT hγ hM hI
      (jetGrading p n) (coupled_joint_jet_grading_continuous M.grading hg n) n n
      (fun z => z.1.1) (fun z => z.1.2) (fun z i => (z.2 i).1)
      continuous_fst.fst continuous_fst.snd
      (fun i => ((continuous_apply i).comp continuous_snd).fst)
      (fun s z => (coupled_joint_jet_coordinates_le M.grading n s z).1)
      (fun s z => (coupled_joint_jet_coordinates_le M.grading n s z).2.1)
      (fun s z i => (coupled_joint_jet_coordinates_le M.grading n s z).2.2.1 i)
    simpa only [K, coupledCircleKernelContinuousMultilinear_apply,
      Fin.cons_zero, Fin.tail_cons] using hh
  have hdir (n : ℕ) (i : Fin (n + 1)) :
      LocallyTameOn (jetGrading p (n + 1)) M.grading univ
        (fun z : (M.Space × M.Space) × (Fin (n + 1) → M.Space × M.Space) =>
          K n z.1.1 (Fin.cons (z.2 i).2 (fun j => (z.2 (i.succAbove j)).1))) := by
    have hh := coupled_circle_kernel_locallyTame hD hT hγ hM hI
      (jetGrading p (n + 1))
      (coupled_joint_jet_grading_continuous M.grading hg (n + 1)) n n
      (fun z => z.1.1) (fun z => (z.2 i).2) (fun z j => (z.2 (i.succAbove j)).1)
      continuous_fst.fst (((continuous_apply i).comp continuous_snd).snd)
      (fun j => ((continuous_apply (i.succAbove j)).comp continuous_snd).fst)
      (fun s z => (coupled_joint_jet_coordinates_le M.grading (n + 1) s z).1)
      (fun s z => (coupled_joint_jet_coordinates_le M.grading (n + 1) s z).2.2.2 i)
      (fun s z j => (coupled_joint_jet_coordinates_le M.grading (n + 1) s z).2.2.1
        (i.succAbove j))
    simpa only [K, coupledCircleKernelContinuousMultilinear_apply,
      Fin.cons_zero, Fin.tail_cons] using hh
  have hsmooth : SmoothTameOn p M.grading univ
      (fun z : M.Space × M.Space => K 0 z.1 (Fin.cons z.2 Fin.elim0)) := by
    apply smoothTameOn_of_locallyTameOn_jets hmono ht J
    intro n
    have hh : LocallyTameOn (jetGrading p n) M.grading univ
        (fun z : (M.Space × M.Space) × (Fin n → M.Space × M.Space) => J.D n z.1 z.2) := by
      cases n with
      | zero =>
        apply (hbase 0).congr
        intro z _
        change coupledKernelJointJet K 0 z.1 z.2 = _
        exact (coupledKernelJointJet_zero_apply K z.1 z.2).trans
          (congrArg (fun w : Fin 0 → M.Space => K 0 z.1.1 (Fin.cons z.1.2 w))
            (Subsingleton.elim _ _))
      | succ n =>
        have hsum := LocallyTameOn.finset_sum (jetGrading_monotone hmono (n + 1))
          Finset.univ (fun i _ => hdir n i)
        apply ((hbase (n + 1)).add (jetGrading_monotone hmono (n + 1)) hsum).congr
        intro z _
        exact coupledKernelJointJet_succ_apply K n z.1 z.2
    exact hh.mono (subset_univ _)
  exact smoothTameOn_congr hsmooth (fun z _ => by
    simp only [K, coupledCircleKernelContinuousMultilinear_apply, Fin.cons_zero, Fin.tail_cons])

end ContinuousFlexibility.Statements
