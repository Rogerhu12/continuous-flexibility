module

public import ContinuousFlexibility.Analysis.CircleDifferentialOperators
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Componentwise contractions in the original circle space

A bounded scalar for each circle acts on its complete weighted energy
without changing any derivative or sample-weight order. In particular,
the values of one fixed radial cutoff at any selector of radii define
an actual continuous linear contraction, uniformly in that selector.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal NNReal

theorem circle_component_contraction_eLpNorm
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1)
    (m b : ℕ) :
    eLpNorm (iteratedDeriv b (fun θ => c m * u m θ)) 2 angleMeasure ≤
      eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure := by
  have hreg : ContDiff ℝ ∞ (fun θ => c m * u m θ) :=
    contDiff_const.mul (hu.1 m).1
  apply eLpNorm_mono (memLp_angleMeasure_iteratedDeriv_of_contDiff hreg b).aestronglyMeasurable
  intro θ
  simp only [Real.norm_eq_abs, iteratedDeriv_const_mul_field, abs_mul]
  exact (mul_le_mul_of_nonneg_right (hc m) (abs_nonneg _)).trans_eq (one_mul _)

theorem circleMember_component_contraction
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) :
    CircleMember T γ (fun m θ => c m * u m θ) := by
  have hreg (m : ℕ) : ContDiff ℝ ∞ (fun θ => c m * u m θ) :=
    contDiff_const.mul (hu.1 m).1
  apply circleMember_of_jet_bound hu 0 0
  · intro m
    refine ⟨hreg m, fun θ => ?_⟩
    change c m * u m (θ + Real.pi) = c m * u m θ
    rw [(hu.1 m).2 θ]
  · exact fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hreg m) b
  · intro s
    refine ⟨1, by norm_num, fun m j => ?_⟩
    simp only [Nat.add_zero, one_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left' (circle_component_contraction_eLpNorm hu c hc m (j.val 0).val) 2)
      zero_le

theorem circleNorm_component_contraction_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) (s : ℕ) :
    circleNorm T γ s (fun m θ => c m * u m θ) ≤ circleNorm T γ s u := by
  have h := circleNorm_le_of_jet_bound (v := fun m θ => c m * u m θ)
    hu s 0 0 (C := 1) (by norm_num) (by
      intro m j
      simp only [Nat.add_zero, one_pow, ENNReal.ofReal_one, one_mul]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left' (circle_component_contraction_eLpNorm hu c hc m (j.val 0).val) 2)
        zero_le)
  simpa only [Nat.add_zero, one_mul] using h

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleComponentContractionFieldLinear (c : ℕ → ℝ) :
    S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u m θ := c m * S.decode u m θ
  map_add' u v := by
    funext m θ
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' a u := by
    funext m θ
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem circleComponentContractionFieldLinear_apply
    (c : ℕ → ℝ) (u : S.Space) (m : ℕ) (θ : ℝ) :
    circleComponentContractionFieldLinear c u m θ = c m * S.decode u m θ := rfl

def circleComponentContractionLinear (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) : S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleComponentContractionFieldLinear c)
    (fun u => circleMember_component_contraction (hS.2.2.2.1 u) c hc)

theorem circleComponentContractionLinear_decode (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) (u : S.Space) :
    S.decode (circleComponentContractionLinear hS c hc u) =
      fun m θ => c m * S.decode u m θ :=
  liftCircleLinear_decode hS (circleComponentContractionFieldLinear c)
    (fun v => circleMember_component_contraction (hS.2.2.2.1 v) c hc) u

theorem circleComponentContractionLinear_grading_le (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) (s : ℕ) (u : S.Space) :
    S.grading s (circleComponentContractionLinear hS c hc u) ≤ S.grading s u := by
  apply (circleGrading_le_iff_circleNorm hS s _ (apply_nonneg _ _)).mpr
  intro i hi
  rw [circleComponentContractionLinear_decode]
  exact (circleNorm_component_contraction_le (hS.2.2.2.1 u) c hc i).trans
    (((circleGrading_le_iff_circleNorm hS s u (apply_nonneg _ _)).mp (le_refl _)) i hi)

theorem circleComponentContractionLinear_isTame (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) :
    IsTameLinear S.grading S.grading (circleComponentContractionLinear hS c hc) 0 0 := by
  intro s hs
  refine ⟨1, fun u => ?_⟩
  simpa only [Nat.add_zero, NNReal.coe_one, one_mul] using
    circleComponentContractionLinear_grading_le hS c hc s u

def circleComponentContractionContinuousLinear (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) : S.Space →L[ℝ] S.Space :=
  (circleComponentContractionLinear_isTame hS c hc).toContinuousLinearMap
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

theorem circleComponentContractionContinuousLinear_apply (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) (u : S.Space) :
    circleComponentContractionContinuousLinear hS c hc u =
      circleComponentContractionLinear hS c hc u :=
  IsTameLinear.toContinuousLinearMap_apply (circleComponentContractionLinear_isTame hS c hc)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond) u

theorem smoothTameOn_circleComponentContractionLinear (hS : IsCircleModel T γ S)
    (c : ℕ → ℝ) (hc : ∀ m, |c m| ≤ 1) :
    SmoothTameOn S.grading S.grading Set.univ (circleComponentContractionLinear hS c hc) := by
  have h := smoothTameOn_continuousLinear
    (circleComponentContractionContinuousLinear hS c hc)
    (circleComponentContractionLinear_isTame hS c hc)
  exact smoothTameOn_congr h (fun u _ => circleComponentContractionContinuousLinear_apply hS c hc u)

end ContinuousFlexibility.Statements
