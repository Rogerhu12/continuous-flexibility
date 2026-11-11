import ContinuousFlexibility.Analysis.CoupledCircleMultiplier
import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds
import ContinuousFlexibility.Analysis.OneHighCircleFourierChangeVariables

/-!
# Fixed translations in the original weighted circle space

Each component may be translated by an arbitrary real angle. Periodic
integration preserves every angular derivative norm, so the resulting
operator preserves every weighted projective seminorm. No bound on the
sequence of translation angles is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators NNReal

private theorem coupled_periodic_translate {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (t : ℝ) :
    Function.Periodic (fun x => f (x + t)) Real.pi := by
  intro x
  change f ((x + Real.pi) + t) = f (x + t)
  calc
    _ = f ((x + t) + Real.pi) := congrArg f (by ring)
    _ = f (x + t) := hp (x + t)

private theorem coupled_integral_sq_translate {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f Real.pi) (t : ℝ) :
    (∫ x in (0 : ℝ)..Real.pi, ‖f (x + t)‖ ^ 2) =
      ∫ x in (0 : ℝ)..Real.pi, ‖f x‖ ^ 2 := by
  have hle := circleLift_integral_comp_sq_le (c := 1) Real.pi_pos f hf hp
    (fun x => x + t) (fun _ => 1)
    (fun x => (hasDerivAt_id x).add_const t) continuous_const
    (fun x => by ring) (fun _ => le_rfl)
  have hge := circleLift_integral_comp_sq_le (c := 1) Real.pi_pos
    (fun x => f (x + t)) (hf.comp (continuous_id.add continuous_const))
    (coupled_periodic_translate hp t) (fun x => x - t) (fun _ => 1)
    (fun x => (hasDerivAt_id x).sub_const t) continuous_const
    (fun x => by ring) (fun _ => le_rfl)
  exact le_antisymm (by simpa only [one_mul] using hle)
    (by simpa only [one_mul, sub_add_cancel] using hge)

/-- Translation preserves the genuine angular `L²` norm over one period. -/
theorem coupled_eLpNorm_translate {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f Real.pi) (t : ℝ) :
    eLpNorm (fun x => f (x + t)) 2 angleMeasure = eLpNorm f 2 angleMeasure := by
  have hm := memLp_angleMeasure_of_continuous hf
  have hmt := memLp_angleMeasure_of_continuous
    (hf.comp (continuous_id.add continuous_const) : Continuous (fun x => f (x + t)))
  have hint : (∫ x, ‖f (x + t)‖ ^ 2 ∂angleMeasure) =
      ∫ x, ‖f x‖ ^ 2 ∂angleMeasure := by
    simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, angleMeasure] using
      coupled_integral_sq_translate hf hp t
  rw [hmt.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hint]

def coupledCircleTranslationField (τ : ℕ → ℝ) (u : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m θ => u m (θ + τ m)

theorem coupledCircleTranslationField_iteratedDeriv (τ : ℕ → ℝ)
    (u : ℕ → ℝ → ℝ) (m b : ℕ) :
    iteratedDeriv b (coupledCircleTranslationField τ u m) =
      fun θ => iteratedDeriv b (u m) (θ + τ m) :=
  iteratedDeriv_comp_add_const b (u m) (τ m)

theorem coupledCircleTranslationField_eLpNorm
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (τ : ℕ → ℝ) (m b : ℕ) :
    eLpNorm (iteratedDeriv b (coupledCircleTranslationField τ u m)) 2 angleMeasure =
      eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure := by
  rw [coupledCircleTranslationField_iteratedDeriv]
  exact coupled_eLpNorm_translate
    (spaces_contDiff_iteratedDeriv (hu.1 m).1 b).continuous
    (spaces_periodic_iteratedDeriv (hu.1 m).2 b) (τ m)

private theorem coupledCircleTranslationField_energy
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (τ : ℕ → ℝ) (s : ℕ) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (coupledCircleTranslationField τ u m))
          2 angleMeasure ^ 2) =
      ∑' m : ℕ, ∑ j : CircleJetIndex s,
        ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
          T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2 := by
  apply tsum_congr
  intro m
  apply Finset.sum_congr rfl
  intro j _
  rw [coupledCircleTranslationField_eLpNorm hu τ m (j.val 0).val]

theorem CircleMember.coupled_translate
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (τ : ℕ → ℝ) :
    CircleMember T γ (coupledCircleTranslationField τ u) := by
  have hs (m : ℕ) : ContDiff ℝ ∞ (coupledCircleTranslationField τ u m) :=
    (hu.1 m).1.comp (contDiff_id.add contDiff_const)
  refine ⟨fun m => ⟨hs m, coupled_periodic_translate (hu.1 m).2 (τ m)⟩, ?_, ?_⟩
  · intro m b
    exact memLp_angleMeasure_iteratedDeriv_of_contDiff (hs m) b
  · intro s
    rw [coupledCircleTranslationField_energy hu τ s]
    exact hu.2.2 s

theorem circleNorm_coupled_translate
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (τ : ℕ → ℝ) (s : ℕ) :
    circleNorm T γ s (coupledCircleTranslationField τ u) = circleNorm T γ s u := by
  unfold circleNorm
  rw [coupledCircleTranslationField_energy hu τ s]

variable {T : MaterialData} {γ : ℝ} {M : CircleModelData}

private def coupledCircleTranslationValue (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (u : M.Space) : M.Space :=
  (hM.2.2.2.2.1 (coupledCircleTranslationField τ (M.decode u))
    ((hM.2.2.2.1 u).coupled_translate τ)).choose

private theorem coupledCircleTranslationValue_decode (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (u : M.Space) :
    M.decode (coupledCircleTranslationValue hM τ u) =
      coupledCircleTranslationField τ (M.decode u) :=
  (hM.2.2.2.2.1 (coupledCircleTranslationField τ (M.decode u))
    ((hM.2.2.2.1 u).coupled_translate τ)).choose_spec

def coupledCircleTranslationLinear (hM : IsCircleModel T γ M) (τ : ℕ → ℝ) :
    M.Space →ₗ[ℝ] M.Space where
  toFun := coupledCircleTranslationValue hM τ
  map_add' := by
    intro u v
    apply hM.2.2.2.2.2.1
    simp only [coupledCircleTranslationValue_decode, map_add,
      coupledCircleTranslationField, Pi.add_apply]
  map_smul' := by
    intro c u
    apply hM.2.2.2.2.2.1
    simp only [coupledCircleTranslationValue_decode, map_smul,
      coupledCircleTranslationField, Pi.smul_apply]

theorem coupledCircleTranslationLinear_decode (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (u : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleTranslationLinear hM τ u) m θ = M.decode u m (θ + τ m) :=
  congrFun (congrFun (coupledCircleTranslationValue_decode hM τ u) m) θ

theorem coupledCircleTranslationLinear_grading_le (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (s : ℕ) (u : M.Space) :
    M.grading s (coupledCircleTranslationLinear hM τ u) ≤ M.grading s u := by
  apply (gradedSeminorm_le_iff (fun n => M.level n) M.bond s _ (apply_nonneg _ _)).mpr
  intro i hi
  calc
    ‖(coupledCircleTranslationLinear hM τ u).val i‖ =
        circleNorm T γ i (M.decode (coupledCircleTranslationLinear hM τ u)) :=
      hM.2.2.2.2.2.2.2 _ _
    _ = circleNorm T γ i (coupledCircleTranslationField τ (M.decode u)) :=
      congrArg (circleNorm T γ i) (coupledCircleTranslationValue_decode hM τ u)
    _ = circleNorm T γ i (M.decode u) := circleNorm_coupled_translate (hM.2.2.2.1 u) τ i
    _ = ‖u.val i‖ := (hM.2.2.2.2.2.2.2 u i).symm
    _ ≤ M.grading s u := norm_coordinate_le_graded _ _ hi u

theorem coupledCircleTranslationLinear_isTame (hM : IsCircleModel T γ M) (τ : ℕ → ℝ) :
    IsTameLinear M.grading M.grading (coupledCircleTranslationLinear hM τ) 0 0 := by
  intro s _
  refine ⟨1, fun u => ?_⟩
  simpa only [Nat.add_zero, NNReal.coe_one, one_mul] using
    coupledCircleTranslationLinear_grading_le hM τ s u

/-- Arbitrary fixed component translations act continuously in the given
projective topology. In particular `τ = C.travel` needs no uniform bound. -/
def coupledCircleTranslation (hM : IsCircleModel T γ M) (τ : ℕ → ℝ) :
    M.Space →L[ℝ] M.Space where
  toLinearMap := coupledCircleTranslationLinear hM τ
  cont := continuous_projectiveLimit_of_tame
    (fun s => M.level s) M.bond (fun s => M.level s) M.bond
    (coupledCircleTranslationLinear hM τ) (coupledCircleTranslationLinear_isTame hM τ)

theorem coupledCircleTranslation_decode (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (u : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleTranslation hM τ u) m θ = M.decode u m (θ + τ m) :=
  coupledCircleTranslationLinear_decode hM τ u m θ

theorem coupledCircleTranslation_grading_le (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (s : ℕ) (u : M.Space) :
    M.grading s (coupledCircleTranslation hM τ u) ≤ M.grading s u :=
  coupledCircleTranslationLinear_grading_le hM τ s u

theorem coupledCircleTranslation_isTame (hM : IsCircleModel T γ M) (τ : ℕ → ℝ) :
    IsTameLinear M.grading M.grading (coupledCircleTranslation hM τ).toLinearMap 0 0 :=
  coupledCircleTranslationLinear_isTame hM τ

theorem coupledCircleTranslation_neg_comp (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (u : M.Space) :
    coupledCircleTranslation hM (fun m => -τ m) (coupledCircleTranslation hM τ u) = u := by
  apply hM.2.2.2.2.2.1
  funext m θ
  simp only [coupledCircleTranslation_decode, ← sub_eq_add_neg, sub_add_cancel]

theorem coupledCircleTranslation_grading_eq (hM : IsCircleModel T γ M)
    (τ : ℕ → ℝ) (s : ℕ) (u : M.Space) :
    M.grading s (coupledCircleTranslation hM τ u) = M.grading s u := by
  apply le_antisymm (coupledCircleTranslation_grading_le hM τ s u)
  have h := coupledCircleTranslation_grading_le hM (fun m => -τ m) s
    (coupledCircleTranslation hM τ u)
  simpa only [coupledCircleTranslation_neg_comp] using h

end ContinuousFlexibility.Statements
