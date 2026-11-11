import ContinuousFlexibility.Analysis.CircleJetEncoding
import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds
import ContinuousFlexibility.Analysis.TameLinear

/-!
# Angular differentiation in the actual weighted circle model

Shifting the angular jet index loses precisely one order and retains the
material weight. The existing realization and its injective decoder then
give a continuous linear angular derivative on every circle model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def coupledCircleAngularIndex (s : ℕ) : CircleJetIndex s ↪ CircleJetIndex (s + 1) where
  toFun j := ⟨![⟨(j.val 0).val + 1, by omega⟩, ⟨(j.val 1).val, by omega⟩], by
    have hj := j.property
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    omega⟩
  inj' := by
    intro j k hjk
    apply Subtype.ext
    funext i
    apply Fin.ext
    fin_cases i
    · have h := congrArg (fun q : CircleJetIndex (s + 1) => (q.val 0).val) hjk
      change (j.val 0).val + 1 = (k.val 0).val + 1 at h
      change (j.val 0).val = (k.val 0).val
      exact Nat.add_right_cancel h
    · exact congrArg (fun q : CircleJetIndex (s + 1) => (q.val 1).val) hjk

theorem coupledCircleAngularIndex_order (s : ℕ) (j : CircleJetIndex s) :
    ((coupledCircleAngularIndex s j).val 0).val = (j.val 0).val + 1 := rfl

theorem coupledCircleAngularIndex_weight (s : ℕ) (j : CircleJetIndex s) :
    ((coupledCircleAngularIndex s j).val 1).val = (j.val 1).val := rfl

private theorem coupledCircleDerivative_energy_le
    (T : MaterialData) (γ : ℝ) (f : ℕ → ℝ → ℝ) (s : ℕ) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (deriv (f m))) 2 angleMeasure ^ 2) ≤
    ∑' m : ℕ, ∑ j : CircleJetIndex (s + 1),
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (f m)) 2 angleMeasure ^ 2 := by
  apply ENNReal.tsum_le_tsum
  intro m
  let term (j : CircleJetIndex (s + 1)) : ℝ≥0∞ :=
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (f m)) 2 angleMeasure ^ 2
  calc
    _ = ∑ j ∈ Finset.univ.map (coupledCircleAngularIndex s), term j := by
      simp only [Finset.sum_map, term, coupledCircleAngularIndex_weight,
        coupledCircleAngularIndex_order, iteratedDeriv_succ']
    _ ≤ ∑ j : CircleJetIndex (s + 1), term j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => zero_le)

theorem CircleMember.coupled_deriv {T : MaterialData} {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) : CircleMember T γ (fun m => deriv (f m)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact ⟨(contDiff_infty_iff_deriv.mp (hf.1 m).1).2,
      by simpa only [iteratedDeriv_one] using spaces_periodic_iteratedDeriv (hf.1 m).2 1⟩
  · intro m b
    simpa only [iteratedDeriv_succ'] using hf.2.1 m (b + 1)
  · intro s
    exact (coupledCircleDerivative_energy_le T γ f s).trans_lt (hf.2.2 (s + 1))

theorem circleNorm_coupled_deriv_le {T : MaterialData} {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) (s : ℕ) :
    circleNorm T γ s (fun m => deriv (f m)) ≤ circleNorm T γ (s + 1) f :=
  Real.sqrt_le_sqrt
    (ENNReal.toReal_mono (hf.2.2 (s + 1)).ne (coupledCircleDerivative_energy_le T γ f s))

variable {T : MaterialData} {γ : ℝ} {M : CircleModelData}

private def coupledCircleDerivativeValue (hM : IsCircleModel T γ M) (u : M.Space) : M.Space :=
  (hM.2.2.2.2.1 (fun m => deriv (M.decode u m))
    (hM.2.2.2.1 u).coupled_deriv).choose

private theorem coupledCircleDerivativeValue_decode (hM : IsCircleModel T γ M) (u : M.Space) :
    M.decode (coupledCircleDerivativeValue hM u) = fun m => deriv (M.decode u m) :=
  (hM.2.2.2.2.1 (fun m => deriv (M.decode u m))
    (hM.2.2.2.1 u).coupled_deriv).choose_spec

def coupledCircleDerivativeLinear (hM : IsCircleModel T γ M) : M.Space →ₗ[ℝ] M.Space where
  toFun := coupledCircleDerivativeValue hM
  map_add' := by
    intro u v
    apply hM.2.2.2.2.2.1
    simp only [coupledCircleDerivativeValue_decode, map_add]
    funext m θ
    change deriv (fun t => M.decode u m t + M.decode v m t) θ =
      deriv (M.decode u m) θ + deriv (M.decode v m) θ
    exact deriv_add (((hM.2.2.2.1 u).1 m).1.differentiable (by simp) θ)
      (((hM.2.2.2.1 v).1 m).1.differentiable (by simp) θ)
  map_smul' := by
    intro c u
    apply hM.2.2.2.2.2.1
    simp only [coupledCircleDerivativeValue_decode, map_smul]
    funext m θ
    change deriv (fun t => c * M.decode u m t) θ = c * deriv (M.decode u m) θ
    exact deriv_const_mul_field c

theorem coupledCircleDerivativeLinear_decode (hM : IsCircleModel T γ M)
    (u : M.Space) (m : ℕ) :
    M.decode (coupledCircleDerivativeLinear hM u) m = deriv (M.decode u m) :=
  congrFun (coupledCircleDerivativeValue_decode hM u) m

theorem coupledCircleDerivativeLinear_grading_le (hM : IsCircleModel T γ M)
    (s : ℕ) (u : M.Space) :
    M.grading s (coupledCircleDerivativeLinear hM u) ≤ M.grading (s + 1) u := by
  apply (gradedSeminorm_le_iff (fun n => M.level n) M.bond s _ (apply_nonneg _ _)).mpr
  intro i hi
  calc
    ‖(coupledCircleDerivativeLinear hM u).val i‖ =
        circleNorm T γ i (M.decode (coupledCircleDerivativeLinear hM u)) :=
      hM.2.2.2.2.2.2.2 _ _
    _ = circleNorm T γ i (fun m => deriv (M.decode u m)) := by
      rw [show M.decode (coupledCircleDerivativeLinear hM u) =
        (fun m => deriv (M.decode u m)) from coupledCircleDerivativeValue_decode hM u]
    _ ≤ circleNorm T γ (i + 1) (M.decode u) :=
      circleNorm_coupled_deriv_le (hM.2.2.2.1 u) i
    _ = ‖u.val (i + 1)‖ := (hM.2.2.2.2.2.2.2 u (i + 1)).symm
    _ ≤ M.grading (s + 1) u := norm_coordinate_le_graded _ _ (by omega) u

theorem coupledCircleDerivativeLinear_isTame (hM : IsCircleModel T γ M) :
    IsTameLinear M.grading M.grading (coupledCircleDerivativeLinear hM) 1 0 := by
  intro s _
  refine ⟨1, fun u => ?_⟩
  simpa only [NNReal.coe_one, one_mul] using coupledCircleDerivativeLinear_grading_le hM s u

def coupledCircleDerivative (hM : IsCircleModel T γ M) : M.Space →L[ℝ] M.Space where
  toLinearMap := coupledCircleDerivativeLinear hM
  cont := continuous_projectiveLimit_of_tame
    (fun s => M.level s) M.bond (fun s => M.level s) M.bond
    (coupledCircleDerivativeLinear hM) (coupledCircleDerivativeLinear_isTame hM)

theorem coupledCircleDerivative_decode (hM : IsCircleModel T γ M)
    (u : M.Space) (m : ℕ) :
    M.decode (coupledCircleDerivative hM u) m = deriv (M.decode u m) :=
  coupledCircleDerivativeLinear_decode hM u m

theorem coupledCircleDerivative_grading_le (hM : IsCircleModel T γ M)
    (s : ℕ) (u : M.Space) :
    M.grading s (coupledCircleDerivative hM u) ≤ M.grading (s + 1) u :=
  coupledCircleDerivativeLinear_grading_le hM s u

end ContinuousFlexibility.Statements
