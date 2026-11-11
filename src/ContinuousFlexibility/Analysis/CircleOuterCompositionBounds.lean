import ContinuousFlexibility.Analysis.CircleCompositionTameBounds
import ContinuousFlexibility.Analysis.CircleCompositionJetModels

/-!
# Uniform low-order bounds for actual outer-jet composition

A single low order works for every fixed outer derivative order.
The second estimate uses the actual linearity in the outer field;
its direction is unrestricted and appears homogeneously.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleOuterJetCompose_grading_uniform_low_order
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (requestedBase : ℕ) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ n : ℕ, ∃ loss : ℕ,
      ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ e u : S.Space,
        S.grading base e ≤ K → S.grading base u ≤ K →
        S.grading s (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u) ≤
          C * (1 + S.grading (s + loss) e + S.grading (s + loss) u) := by
  classical
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  have hw := material_circle_sample_weights_pos hT hD
  obtain ⟨base, hbase, hb⟩ :=
    circleNorm_comp_outerJet_uniform_low_order hS hw.1 hw.2 hA hHA hinterp travel requestedBase
  refine ⟨base, hbase, ?_⟩
  intro n
  obtain ⟨loss, hl⟩ := hb n
  refine ⟨loss, ?_⟩
  intro K hK
  choose C hC hc using hl K hK
  intro s
  let B : ℝ := ∑ i ∈ Finset.range (s + 1), C i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨B, hB, ?_⟩
  intro e u he hu
  have hsize : 0 ≤ 1 + S.grading (s + loss) e + S.grading (s + loss) u := by
    positivity
  apply (circleGrading_le_iff_circleNorm hS s _ (mul_nonneg hB hsize)).mpr
  intro i hi
  have hnorm :
      circleNorm T γ i
        (S.decode (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u)) ≤
      C i * (1 + S.grading (i + loss) e + S.grading (i + loss) u) := by
    simpa only [circleOuterJetComposeContinuousLinear_decode, circleCompositionPhase,
      circleAffineLift, Function.comp_def, one_mul] using hc i e u he hu
  have hCi : C i ≤ B := Finset.single_le_sum
    (f := C) (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  have hp := gradedSeminorm_monotone (fun j => S.level j) S.bond
  have hsize' : 1 + S.grading (i + loss) e + S.grading (i + loss) u ≤
      1 + S.grading (s + loss) e + S.grading (s + loss) u :=
    add_le_add (add_le_add le_rfl (hp (by omega) e)) (hp (by omega) u)
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hsize' (hC i)).trans
    (mul_le_mul_of_nonneg_right hCi hsize))

private theorem circleComposition_linear_unit_normalization
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (L : E →L[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ u, low u < 1 → q (L u) ≤ C * (a + high u)) (u : E) :
    q (L u) ≤ C * (a * low u + high u) := by
  let A : E [×1]→L[ℝ] F := ContinuousMultilinearMap.ofSubsingleton ℝ E F (0 : Fin 1) L
  have hu (v : Fin 1 → E) (hv : ∀ i, low (v i) < 1) :
      q (A v) ≤ C * (a + ∑ i, high (v i)) := by
    change q (L (v 0)) ≤ _
    rw [Fin.sum_univ_one]
    exact hlocal (v 0) (hv 0)
  have h := multilinear_bound_of_unitBall A q low high hC hu (fun _ : Fin 1 => u)
  simpa [A, multilinearTameSize] using h

/-- One common low order supplies both affine growth when both inputs
are bounded and homogeneous growth in an arbitrary outer direction. -/
theorem circleOuterJetCompose_uniform_bounds
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ,
      ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ e u : S.Space, S.grading base e ≤ K → S.grading base u ≤ K →
          S.grading s (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u) ≤
            C * (1 + S.grading (s + loss) e + S.grading (s + loss) u)) ∧
        (∀ e u : S.Space, S.grading base e ≤ K →
          S.grading s (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u) ≤
            C * (1 + S.grading (s + loss) e) * S.grading (s + loss) u) := by
  obtain ⟨base, _, hb⟩ :=
    circleOuterJetCompose_grading_uniform_low_order hS hT hD hγ hinterp travel 0
  have hp := gradedSeminorm_monotone (fun j => S.level j) S.bond
  refine ⟨base, ?_⟩
  intro n
  obtain ⟨loss, hl⟩ := hb n
  refine ⟨loss + base, ?_⟩
  intro K hK s
  obtain ⟨C, hC, hc⟩ := hl (max K 1) (le_max_of_le_right zero_le_one) s
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_, ?_⟩
  · intro e u he hu
    have h := hc e u (he.trans (le_max_left K 1)) (hu.trans (le_max_left K 1))
    have hsum : 1 + S.grading (s + loss) e + S.grading (s + loss) u ≤
        1 + S.grading (s + (loss + base)) e + S.grading (s + (loss + base)) u :=
      add_le_add (add_le_add le_rfl (hp (by omega) e)) (hp (by omega) u)
    exact h.trans (mul_le_mul (show C ≤ 2 * C by linarith) hsum
      (by positivity) (by positivity))
  · intro e u he
    have hlocal (z : S.Space) (hz : S.grading base z < 1) :
        S.grading s (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e z) ≤
          C * ((1 + S.grading (s + loss) e) + S.grading (s + loss) z) := by
      exact hc e z (he.trans (le_max_left K 1)) (hz.le.trans (le_max_right K 1))
    have h := circleComposition_linear_unit_normalization
      (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e)
      (S.grading s) (S.grading base) (S.grading (s + loss)) hC hlocal u
    have hfirst :
        (1 + S.grading (s + loss) e) * S.grading base u ≤
        (1 + S.grading (s + (loss + base)) e) * S.grading (s + (loss + base)) u :=
      mul_le_mul (add_le_add le_rfl (hp (by omega) e)) (hp (by omega) u)
        (apply_nonneg _ _) (by positivity)
    have hsecond : S.grading (s + loss) u ≤
        (1 + S.grading (s + (loss + base)) e) * S.grading (s + (loss + base)) u :=
      (hp (by omega) u).trans
        (le_mul_of_one_le_left (apply_nonneg _ _)
          (le_add_of_nonneg_right (apply_nonneg _ _)))
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC).trans_eq (by ring))

end ContinuousFlexibility.Statements
