module

public import ContinuousFlexibility.Analysis.CoupledCircleCompositionCurveBounds
public import ContinuousFlexibility.Analysis.CoupledCircleLpDerivative
public import ContinuousFlexibility.Analysis.SpacesNemytskiiCurveDerivative

/-!
# Derivatives in the actual circle projective space

Dominated differentiation applies to each angular L² coordinate. The
inverse material weight is summable, so the canonical series of Hilbert
rows can then be differentiated in the original outer lp space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

private theorem coupled_piLp_norm_le_uniform
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (v : PiLp 2 E)
    {A : ℝ} (hA : 0 ≤ A) (hv : ∀ i, ‖v i‖ ≤ A) :
    ‖v‖ ≤ ((Fintype.card ι : ℝ) + 1) * A := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hn' : (Fintype.card ι : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hA)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _i : ι, A ^ 2 := Finset.sum_le_sum
      (fun i _ => (sq_le_sq₀ (norm_nonneg _) hA).mpr (hv i))
    _ = (Fintype.card ι : ℝ) * A ^ 2 := by simp
    _ ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * A ^ 2 :=
      mul_le_mul_of_nonneg_right hn' (sq_nonneg A)
    _ = _ := (mul_pow _ _ _).symm

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

theorem coupledCircleKernel_level (r k : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (s m : ℕ) (j : CircleJetIndex s) :
    ((coupledCircleKernel hD hT hγ hM hI r k ψ v w).val s).val m j =
      coupledCircleKernelJetLp hM r k (j.val 0).val (j.val 1).val ψ v w m := by
  apply Lp.ext
  have he := congrFun (coupledCircleKernel_decode hD hT hγ hM hI r k ψ v w) m
  apply (coupled_circle_model_level_ae hM
    (coupledCircleKernel hD hT hγ hM hI r k ψ v w) s m j).trans
  apply Filter.EventuallyEq.trans _ (coupledCircleKernelJetLp_ae hM r k
    (j.val 0).val (j.val 1).val ψ v w m).symm
  exact Eventually.of_forall (fun θ => congrArg
    (fun f : ℝ → ℝ => (T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) * iteratedDeriv (j.val 0).val f θ) he)

include hD hT hγ hI in
theorem coupledCircleKernelJetLp_affine_hasDerivAt (r k s : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (t₀ : ℝ)
    (m : ℕ) (j : CircleJetIndex s) :
    HasDerivAt
      (fun t => coupledCircleKernelJetLp hM r k (j.val 0).val (j.val 1).val
        (ψ + t • u) v w m)
      (coupledCircleKernelJetLp hM (r + 1) (k + 1) (j.val 0).val (j.val 1).val
        (ψ + t₀ • u) v (Fin.cons u w) m) t₀ := by
  have hAexists := coupled_circle_kernel_affine_jet_bound hD hT hγ hM hI
    (r + 1) (k + 1) s ψ u v (Fin.cons u w)
    (show 0 ≤ |t₀| + 1 by positivity)
  let A : ℝ := hAexists.choose
  have hA : 0 ≤ A := hAexists.choose_spec.1
  have hb : ∀ t : ℝ, |t| ≤ |t₀| + 1 →
      ∀ (m : ℕ) (j : CircleJetIndex s) (θ : ℝ),
        |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
            iteratedDeriv (j.val 0).val
              (coupledCircleKernelField M (r + 1) (k + 1)
                (ψ + t • u) v (Fin.cons u w) m) θ| ≤
          A * (T.M (T.sample m))⁻¹ := hAexists.choose_spec.2
  have hg : MemLp (fun _ : ℝ => A * (T.M (T.sample m))⁻¹) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous continuous_const
  unfold coupledCircleKernelJetLp
  apply spaces_hasDerivAt_toLp_of_dominated_deriv
    (df := fun t θ => (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
      iteratedDeriv (j.val 0).val
        (coupledCircleKernelField M (r + 1) (k + 1) (ψ + t • u) v (Fin.cons u w) m) θ)
    (t₀ := t₀)
    (fun t => (memLp_angleMeasure_iteratedDeriv_of_contDiff
      (coupledCircleKernelField_contDiff hM r k (ψ + t • u) v w m) (j.val 0).val).const_mul
        (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)))
    ((memLp_angleMeasure_iteratedDeriv_of_contDiff
      (coupledCircleKernelField_contDiff hM (r + 1) (k + 1) (ψ + t₀ • u)
        v (Fin.cons u w) m) (j.val 0).val).const_mul
        (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)))
    (by norm_num : (0 : ℝ) < 1) hg
  · filter_upwards [] with θ t ht
    exact coupledCircleKernelField_weightedJet_affine_hasDerivAt hM r k
      (j.val 0).val (j.val 1).val ψ u v w t m θ
  · filter_upwards [] with θ t ht
    exact hb t (abs_le.mpr
      ⟨by linarith [neg_abs_le t₀, ht.1], by linarith [le_abs_self t₀, ht.2]⟩) m j θ

theorem coupledCircleKernel_hilbert_affine_hasDerivAt (r k s : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (t₀ : ℝ) :
    HasDerivAt
      (fun t => ((coupledCircleKernel hD hT hγ hM hI r k (ψ + t • u) v w).val s).val)
      (((coupledCircleKernel hD hT hγ hM hI (r + 1) (k + 1)
        (ψ + t₀ • u) v (Fin.cons u w)).val s).val) t₀ := by
  have hAexists := coupled_circle_kernel_affine_jet_bound hD hT hγ hM hI
    (r + 1) (k + 1) s ψ u v (Fin.cons u w)
    (show 0 ≤ |t₀| + 1 by positivity)
  let A : ℝ := hAexists.choose
  have hA : 0 ≤ A := hAexists.choose_spec.1
  have hb : ∀ t : ℝ, |t| ≤ |t₀| + 1 →
      ∀ (m : ℕ) (j : CircleJetIndex s) (θ : ℝ),
        |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
            iteratedDeriv (j.val 0).val
              (coupledCircleKernelField M (r + 1) (k + 1)
                (ψ + t • u) v (Fin.cons u w) m) θ| ≤
          A * (T.M (T.sample m))⁻¹ := hAexists.choose_spec.2
  let C : ℝ := ((Fintype.card (CircleJetIndex s) : ℝ) + 1) * spacesAngleL2Constant * A
  have hsum : Summable (fun m => C * (T.M (T.sample m))⁻¹) :=
    (spaces_trace_sample_inv_summable hD hT).mul_left C
  apply coupled_hasDerivAt_lp_of_summable_bound
    (df := fun t => ((coupledCircleKernel hD hT hγ hM hI (r + 1) (k + 1)
      (ψ + t • u) v (Fin.cons u w)).val s).val)
    (by norm_num : (0 : ℝ) < 1) hsum
  · intro m t _ht
    apply spaces_hasDerivAt_piLp
    intro j
    simpa only [coupledCircleKernel_level] using
      coupledCircleKernelJetLp_affine_hasDerivAt hD hT hγ hM hI r k s ψ u v w t m j
  · intro m t ht
    have hmt : 0 ≤ (T.M (T.sample m))⁻¹ :=
      inv_nonneg.mpr (zero_le_one.trans
        (hT.2.1 _ (spaces_trace_sample_mem hD hT m)).2.2.2)
    have hat : |t| ≤ |t₀| + 1 := abs_le.mpr
      ⟨by linarith [neg_abs_le t₀, ht.1], by linarith [le_abs_self t₀, ht.2]⟩
    have hcoord (j : CircleJetIndex s) :
        ‖((coupledCircleKernel hD hT hγ hM hI (r + 1) (k + 1)
            (ψ + t • u) v (Fin.cons u w)).val s).val m j‖ ≤
          spacesAngleL2Constant * (A * (T.M (T.sample m))⁻¹) := by
      rw [coupledCircleKernel_level]
      exact coupledCircleKernelJetLp_norm_le hM (r + 1) (k + 1)
        (j.val 0).val (j.val 1).val (ψ + t • u) v (Fin.cons u w) m
        (mul_nonneg hA hmt) (hb t hat m j)
    exact (coupled_piLp_norm_le_uniform _
      (mul_nonneg spacesAngleL2Constant_nonneg (mul_nonneg hA hmt)) hcoord).trans_eq
        (by dsimp only [C]; ac_rfl)

theorem coupledCircleKernel_hasProjectiveLineDerivAt (r k : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) :
    HasProjectiveLineDerivAt
      (fun x => coupledCircleKernel hD hT hγ hM hI r k x v w)
      (coupledCircleKernel hD hT hγ hM hI (r + 1) (k + 1) ψ v (Fin.cons u w)) ψ u := by
  apply (hasProjectiveLineDerivAt_iff_levels _ _ _ _).mpr
  intro s
  apply spaces_hasDerivAt_submodule (M.level s)
  simpa only [zero_smul, add_zero] using
    coupledCircleKernel_hilbert_affine_hasDerivAt hD hT hγ hM hI r k s ψ u v w 0

end ContinuousFlexibility.Statements
