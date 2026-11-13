import ContinuousFlexibility.Analysis.N01ControlCellBounds
import ContinuousFlexibility.Analysis.N01ControlFlowBounds

/-!
# The actual-cell weight constraint forced by optical normalization

The coefficient and flow towers are evaluated on the same unit singleton
control. Their actual derivative bounds combine with the full-component
optical curvature inequality. The resulting weight constraint holds for
any reference cell containing the negative component, without identifying
that cell with the control's own weight label.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance n01ControlWeightConstraintStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01ControlWeightConstraintRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set
open scoped ContDiff BigOperators

theorem oneHighVariationWeight_two_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight p base high 0 (fun _ : Fin 2 => v) =
      (p base v) ^ 2 + 2 * (p high v * p base v) := by
  classical
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  simp [oneHighVariationWeight, hu, pow_two]
  <;> ring

theorem oneHighVariationWeight_state_pair_two_zero_le
    (S : PhysicalSpacesData) (base high : ℕ) (v : AnnularState S) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high 0 (fun _ : Fin 2 => (v, (0 : ℝ))) ≤
        (stateGrading S base v + stateGrading S high v) ^ 2 := by
  have hpair (n : ℕ) :
      pairGrading (stateGrading S) realGrading n (v, (0 : ℝ)) = stateGrading S n v := by
    change stateGrading S n v + realGrading n (0 : ℝ) = _
    exact (congrArg (fun t : ℝ => stateGrading S n v + t) (realGrading n).map_zero').trans
      (add_zero _)
  have hw := oneHighVariationWeight_two_zero
    (pairGrading (stateGrading S) realGrading) base high (v, (0 : ℝ))
  have he := congrArg₂ (fun a b : ℝ => a ^ 2 + 2 * (b * a)) (hpair base) (hpair high)
  exact (hw.trans he).le.trans (by nlinarith only [sq_nonneg (stateGrading S high v)])

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The full optical second derivative has exactly two inverse singleton
height weights and one forward flow weight. -/
theorem N01Properties.controlTravel_second_weight_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ d₂ : ℕ, ∃ K B : ℝ, 0 < K ∧ 0 < B ∧ ∀ m,
      |deriv (deriv (fun t => opticalTravel
        (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m))) 0| ≤
        K * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (T.M (T.sample m) ^ max base (loss + d₂) *
            T.H (T.sample m) ^ (-(3 / 4 : ℝ))) ^ 2 := by
  obtain ⟨d₂, hdata⟩ := hN.controlTravel_second_bound hS hT
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  let G := circleSingletonGradingConstant base + circleSingletonGradingConstant (loss + d₂) + 1
  have hG : 0 < G := by
    have hb := circleSingletonGradingConstant_nonneg base
    have hl := circleSingletonGradingConstant_nonneg (loss + d₂)
    dsimp only [G]
    linarith
  refine ⟨d₂, B * G ^ 2, B, mul_pos hB (sq_pos_of_pos hG), hB, fun m => ?_⟩
  have hsample (i : ℕ) : T.sample i ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hgeom.2.1 i
  have hpM := hT.2.1 (T.sample m) (hsample m)
  have hpC := hT.2.1 (T.sample (C.cell m)) (hsample (C.cell m))
  let v := singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m
  have hgrade := singletonKappaDirection_two_grades_le
    (hS.2.1 (3 / 4 : ℝ)) m base (loss + d₂) hpM.2.2.2 hpM.2.1.le
  have hgrade0 : 0 ≤ stateGrading S base v + stateGrading S (loss + d₂) v :=
    add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hweight :
      oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base (loss + d₂) 0 (fun _ : Fin 2 => (v, (0 : ℝ))) ≤
        G ^ 2 * (T.M (T.sample m) ^ max base (loss + d₂) *
          T.H (T.sample m) ^ (-(3 / 4 : ℝ))) ^ 2 := by
    refine (oneHighVariationWeight_state_pair_two_zero_le S base (loss + d₂) v).trans
      ((pow_le_pow_left₀ hgrade0 hgrade 2).trans_eq ?_)
    dsimp only [G]
    ring
  have hfactor : 0 ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hpC.2.1.le _))
      (Real.rpow_nonneg hpC.2.2.1.le _)
  exact (hdata.choose_spec.2 m).trans
    ((mul_le_mul_of_nonneg_left hweight hfactor).trans_eq (by ring))

/-- This is the quantitative constraint from which the reference-cell
index can be compared to the control sample index.  It is obtained from
the two actual N01 towers and actual optical normalization. -/
theorem N01Properties.control_actual_cell_weight_constraint
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ d₂ : ℕ, ∃ K B A F : ℝ, 0 < K ∧ 0 < B ∧ 0 < A ∧ 0 < F ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      1 ≤ K * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
        radialE (D.cellIndex j) ^ A *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ F *
        ((T.M (T.sample m) ^ max base (1 + loss) *
            T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
          (T.M (T.sample m) ^ max base (loss + d₂) *
            T.H (T.sample m) ^ (-(3 / 4 : ℝ))) ^ 2) := by
  obtain ⟨Kχ, B, A, hKχ, hB, hA, hχ⟩ := hN.control_deriv_actual_cell_bound hS hT
  obtain ⟨d₂, KF, F, hKF, hF, hsecond⟩ := hN.controlTravel_second_weight_bound hS hT
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hinterval := hN.2.2.2.1.1
  let K := (D.b - D.a) ^ 2 / (2 * D.a) * (Kχ * KF)
  have hwidth : 0 < D.b - D.a := sub_pos.mpr hgeom.1.2.1
  have hden : 0 < 2 * D.a := mul_pos zero_lt_two hgeom.1.1
  have hK : 0 < K := mul_pos (div_pos (sq_pos_of_pos hwidth) hden) (mul_pos hKχ hKF)
  refine ⟨d₂, K, B, A, F, hK, hB, hA, hF, fun m j hcell => ?_⟩
  let Pχ := Kχ * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
    radialE (D.cellIndex j) ^ A *
    (T.M (T.sample m) ^ max base (1 + loss) * T.H (T.sample m) ^ (-(3 / 4 : ℝ)))
  let PF := KF * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ F *
    (T.M (T.sample m) ^ max base (loss + d₂) * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) ^ 2
  have hχbound : ∀ r ∈ Ioo (C.left m) (C.right m), |deriv (C.control m) r| ≤ Pχ :=
    fun r hr => hχ m j r (hcell hr)
  have hPχ : 0 ≤ Pχ := by
    have hmid : (C.left m + C.right m) / 2 ∈ Ioo (C.left m) (C.right m) := by
      constructor <;> linarith only [(hinterval m).2.1]
    exact (abs_nonneg _).trans (hχbound _ hmid)
  have hPF : 0 ≤ PF := (abs_nonneg _).trans (hsecond m)
  have hcurv := hN.control_curvature_product_lower_bound m hPχ hχbound (hsecond m)
  have hlength : C.right m - C.left m ≤ D.b - D.a := by
    linarith only [(hinterval m).1, (hinterval m).2.2]
  have hlengthSq : (C.right m - C.left m) ^ 2 ≤ (D.b - D.a) ^ 2 :=
    pow_le_pow_left₀ (sub_pos.mpr (hinterval m).2.1).le hlength 2
  have hlarge : 2 * D.a ≤ (D.b - D.a) ^ 2 * Pχ * PF :=
    (mul_le_mul_of_nonneg_left (hinterval m).1.le (by norm_num : (0 : ℝ) ≤ 2)).trans
      (hcurv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlengthSq hPχ) hPF))
  have hnorm : 1 ≤ ((D.b - D.a) ^ 2 * Pχ * PF) / (2 * D.a) := by
    apply (le_div_iff₀ hden).mpr
    simpa only [one_mul] using hlarge
  exact hnorm.trans_eq (by dsimp only [Pχ, PF, K]; ring)

end ContinuousFlexibility.Statements
