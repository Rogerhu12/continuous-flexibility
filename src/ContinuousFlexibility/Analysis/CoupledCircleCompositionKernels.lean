module

public import ContinuousFlexibility.Analysis.CoupledCircleCompositionJetBounds
public import ContinuousFlexibility.Analysis.SpacesTraceRestriction

/-!
# Composition kernels in the actual weighted circle class

The pointwise jet estimate has a fixed summable sample envelope. Summing
its squares gives membership and one-high-factor estimates in precisely
the circle norms used by the physical model.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def coupledCircleKernelField (M : CircleModelData) (r k : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ) : ℝ :=
  iteratedDeriv r (M.decode v m) (θ + M.decode ψ m θ) * ∏ i, M.decode (w i) m θ

theorem coupledCircleKernelField_contDiff {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (r k : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (m : ℕ) :
    ContDiff ℝ ∞ (coupledCircleKernelField M r k ψ v w m) := by
  exact ((spaces_contDiff_iteratedDeriv ((hM.2.2.2.1 v).1 m).1 r).comp
    (contDiff_id.add ((hM.2.2.2.1 ψ).1 m).1)).mul
      (contDiff_prod (fun i _ => ((hM.2.2.2.1 (w i)).1 m).1))

theorem coupledCircleKernelField_periodic {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (r k : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (m : ℕ) :
    Function.Periodic (coupledCircleKernelField M r k ψ v w m) Real.pi := by
  have he : coupledCircleKernelField M r k ψ v w m =
      (CoupledCircleCompositionTerm.initial r k).evaluate
        (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) := by
    funext θ
    exact (CoupledCircleCompositionTerm.initial_evaluate r k _ _ _ θ).symm
  rw [he]
  exact CoupledCircleCompositionTerm.evaluate_periodic _
    ((hM.2.2.2.1 v).1 m).2 ((hM.2.2.2.1 ψ).1 m).2
    (fun i => ((hM.2.2.2.1 (w i)).1 m).2)

/-- One constant controls all coordinates of a fixed output jet level. -/
theorem coupled_circle_kernel_jet_bounds
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading) :
    ∃ base loss : ℕ, ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (j : CircleJetIndex s) (θ : ℝ),
          |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
              iteratedDeriv (j.val 0).val (coupledCircleKernelField M r k ψ v w m) θ| ≤
            (C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w)) *
              (T.M (T.sample m))⁻¹ := by
  classical
  have hexists := coupled_circle_composition_jet_tame hT hsample hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hraw := hexists.choose_spec.choose_spec
  refine ⟨base, loss, fun r k s R hR => ?_⟩
  have hcoord (j : CircleJetIndex s) := hraw r k (j.val 0).val (j.val 1).val (r + s)
    (by have hj := j.property; omega) R hR
  choose C hC hbound using hcoord
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun ψ hψ v w m j θ => ?_⟩
  have hi : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hsample m)).2.2.2)
  have hc : C j ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)
  have hmajor := coupledCircleKernelMajorant_nonneg M base (r + s + loss) ψ (Fin.cons v w)
  calc
    _ ≤ C j * (T.M (T.sample m))⁻¹ *
        coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) :=
      hbound j ψ hψ v w m θ
    _ ≤ (∑ i, C i) * (T.M (T.sample m))⁻¹ *
        coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hi) hmajor
    _ = _ := by ac_rfl

theorem coupledCircleKernelField_mem
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)
    (r k : ℕ) (ψ v : M.Space) (w : Fin k → M.Space) :
    CircleMember T γ (coupledCircleKernelField M r k ψ v w) := by
  have hs := spaces_trace_sample_mem hD hT
  have hexists := coupled_circle_kernel_jet_bounds hT hs hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hjet := hexists.choose_spec.choose_spec
  have hreg := coupledCircleKernelField_contDiff hM r k ψ v w
  have hw (m : ℕ) : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2)
  have hsum := spaces_trace_sample_inv_sq_summable hD hT
  refine ⟨fun m => ⟨hreg m, coupledCircleKernelField_periodic hM r k ψ v w m⟩,
    fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hreg m) b, fun s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hjet r k s (max 1 (M.grading base ψ)) (le_max_left _ _)
  exact (spaces_circle_energy_le_of_weighted_bound hreg s
    (mul_nonneg hC (coupledCircleKernelMajorant_nonneg M base (r + s + loss) ψ (Fin.cons v w)))
    hw hsum (hb ψ (le_max_right _ _) v w)).trans_lt ENNReal.ofReal_lt_top

/-- The genuine weighted circle norm obeys the same one-high estimate. -/
theorem coupled_circle_kernel_norm_bounds
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading) :
    ∃ base loss : ℕ, ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (v : M.Space) (w : Fin k → M.Space),
          circleNorm T γ s (coupledCircleKernelField M r k ψ v w) ≤
            C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) := by
  have hs := spaces_trace_sample_mem hD hT
  have hexists := coupled_circle_kernel_jet_bounds hT hs hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hjet := hexists.choose_spec.choose_spec
  have hw (m : ℕ) : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2)
  have hsum := spaces_trace_sample_inv_sq_summable hD hT
  refine ⟨base, loss, fun r k s R hR => ?_⟩
  obtain ⟨C, hC, hb⟩ := hjet r k s R hR
  let A : ℝ := Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
    ∑' m, ((T.M (T.sample m))⁻¹) ^ 2) * spacesAngleL2Constant
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) spacesAngleL2Constant_nonneg
  refine ⟨A * C, mul_nonneg hA hC, fun ψ hψ v w => ?_⟩
  exact (spaces_circleNorm_le_of_weighted_bound
    (coupledCircleKernelField_contDiff hM r k ψ v w) s
    (mul_nonneg hC (coupledCircleKernelMajorant_nonneg M base (r + s + loss) ψ (Fin.cons v w)))
    hw hsum (hb ψ hψ v w)).trans_eq (by dsimp only [A]; ac_rfl)

end ContinuousFlexibility.Statements
