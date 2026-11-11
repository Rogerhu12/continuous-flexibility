import ContinuousFlexibility.Analysis.N01ControlCoefficientVariation

/-!
# A quantitative control-derivative bound on the actual radial cell

The coefficient tower bounds `w χ` and its first radial derivative.
The zeroth and first inverse-profile jets then recover `χ'`.  The
singleton-circle grading contributes precisely one negative power of the
control sample's height weight.  No incidence between a control label and
a reference cell is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance n01ControlCellBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set
open scoped ContDiff

theorem abs_deriv_control_le_inverse_jets
    {w χ : ℝ → ℝ} {r A : ℝ} (hw : DifferentiableAt ℝ w r) (hwr : w r ≠ 0)
    (h0 : |w r * χ r| ≤ A)
    (h1 : |deriv w r * χ r + w r * deriv χ r| ≤ A) :
    |deriv χ r| ≤
      (|(w r)⁻¹| + |deriv (fun s => (w s)⁻¹) r|) * A := by
  have heq : deriv χ r =
      (w r)⁻¹ * (deriv w r * χ r + w r * deriv χ r) +
        deriv (fun s => (w s)⁻¹) r * (w r * χ r) := by
    rw [deriv_fun_inv'' hw hwr]
    field_simp [hwr] <;> ring
  rw [heq]
  calc
    _ ≤ |(w r)⁻¹ * (deriv w r * χ r + w r * deriv χ r)| +
        |deriv (fun s => (w s)⁻¹) r * (w r * χ r)| := abs_add_le _ _
    _ = |(w r)⁻¹| * |deriv w r * χ r + w r * deriv χ r| +
        |deriv (fun s => (w s)⁻¹) r| * |w r * χ r| := by rw [abs_mul, abs_mul]
    _ ≤ |(w r)⁻¹| * A + |deriv (fun s => (w s)⁻¹) r| * A :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
    _ = _ := by ring

/-- Keep the scalar estimate separate from the physical seminorm terms.
This avoids reducing the supplied physical models during ring arithmetic. -/
theorem abs_deriv_control_le_product_weights
    {w χ : ℝ → ℝ} {r A B H E W G : ℝ}
    (hw : DifferentiableAt ℝ w r) (hwr : w r ≠ 0)
    (h0 : |w r * χ r| ≤ B * H * E * G)
    (h1 : |deriv w r * χ r + w r * deriv χ r| ≤ B * H * E * G)
    (hinverse : |(w r)⁻¹| + |deriv (fun s => (w s)⁻¹) r| ≤ A * W) :
    |deriv χ r| ≤ (A * B) * H * E * W * G := by
  have hb := abs_deriv_control_le_inverse_jets hw hwr h0 h1
  have hnonneg : 0 ≤ B * H * E * G := (abs_nonneg _).trans h0
  exact hb.trans ((mul_le_mul_of_nonneg_right hinverse hnonneg).trans_eq (by ring))

/-- Uniform scalar bounds are packaged before substituting physical
seminorms. Both constants keep precisely their original exponents. -/
theorem control_deriv_weight_bound_of_product_bounds
    (cells : ℕ → Set ℝ) (w : ℝ → ℝ) (χ : ℕ → ℝ → ℝ)
    (H E W G : ℕ → ℝ)
    (hw : ∀ j r, r ∈ cells j → DifferentiableAt ℝ w r)
    (hwr : ∀ j r, r ∈ cells j → w r ≠ 0)
    (hproduct : ∃ B : ℝ, 0 < B ∧ ∀ m j r, r ∈ cells j →
      let Q := B * H j * E j ^ B * G m
      |w r * χ m r| ≤ Q ∧ |deriv w r * χ m r + w r * deriv (χ m) r| ≤ Q)
    (hinverse : ∃ A : ℝ, 0 < A ∧ ∀ j r, r ∈ cells j →
      |(w r)⁻¹| + |deriv (fun t => (w t)⁻¹) r| ≤ A * W j ^ A) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m j r, r ∈ cells j →
      |deriv (χ m) r| ≤ (A * B) * H j * E j ^ B * W j ^ A * G m := by
  obtain ⟨B, hB, hb⟩ := hproduct
  obtain ⟨A, hA, ha⟩ := hinverse
  exact ⟨B, A, hB, hA, fun m j r hr =>
    abs_deriv_control_le_product_weights (hw j r hr) (hwr j r hr)
      (hb m j r hr).1 (hb m j r hr).2 (ha j r hr)⟩

theorem IsAccumulatingProfile.inverse_first_jets_cell_bound
    {D : ReferenceData} (hRef : IsAccumulatingProfile D) :
    ∃ A : ℝ, 0 < A ∧ ∀ j r, r ∈ D.cells j →
      |(D.w r)⁻¹| + |deriv (fun s => (D.w s)⁻¹) r| ≤
        A * radialE (D.cellIndex j) ^ A := by
  obtain ⟨C, hdata⟩ := hRef
  rcases hdata with ⟨_, _, hC, _, _, _, _, _, _, hinv, _⟩
  let A := C 0 + C 1
  have hA : 0 < A := add_pos (hC 0) (hC 1)
  refine ⟨A, hA, fun j r hr => ?_⟩
  have hE : 1 ≤ radialE (D.cellIndex j) := by
    have hn : 0 ≤ (D.cellIndex j : ℝ) := Nat.cast_nonneg _
    have he : 1 ≤ Real.exp 1 + (D.cellIndex j : ℝ) :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
        (le_add_of_nonneg_right hn)
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Real.rpow_nonneg hn _) (Real.log_nonneg he))
  have h0 : |(D.w r)⁻¹| ≤ C 0 * radialE (D.cellIndex j) ^ C 0 := by
    simpa only [radialJet] using hinv j r hr 0
  have h1 : |deriv (fun s => (D.w s)⁻¹) r| ≤ C 1 * radialE (D.cellIndex j) ^ C 1 := by
    simpa only [radialJet] using hinv j r hr 1
  have he0 : radialE (D.cellIndex j) ^ C 0 ≤ radialE (D.cellIndex j) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right (hC 1).le)
  have he1 : radialE (D.cellIndex j) ^ C 1 ≤ radialE (D.cellIndex j) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left (hC 0).le)
  calc
    _ ≤ C 0 * radialE (D.cellIndex j) ^ C 0 + C 1 * radialE (D.cellIndex j) ^ C 1 :=
      add_le_add h0 h1
    _ ≤ C 0 * radialE (D.cellIndex j) ^ A + C 1 * radialE (D.cellIndex j) ^ A :=
      add_le_add (mul_le_mul_of_nonneg_left he0 (hC 0).le)
        (mul_le_mul_of_nonneg_left he1 (hC 1).le)
    _ = _ := by dsimp only [A]; ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.control_deriv_cell_bound_with_grading
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m j r, r ∈ D.cells j →
      let v := singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m
      |deriv (C.control m) r| ≤
        (A * B) * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
          radialE (D.cellIndex j) ^ A *
          (stateGrading S base v + stateGrading S (1 + loss) v) := by
  have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hcell : ∀ j r, r ∈ D.cells j → r ∈ radialCore D :=
    hN.1.1.choose_spec.2.1.2.2.2.1
  exact control_deriv_weight_bound_of_product_bounds D.cells D.w C.control
    (fun j => T.H (T.sample j) ^ (3 / 4 : ℝ)) (fun j => T.E0 (T.sample j))
    (fun j => radialE (D.cellIndex j))
    (fun m => stateGrading S base (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m) +
      stateGrading S (1 + loss) (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m))
    (fun _ r _ => hgeom.2.2.1.1.differentiable (by simp) r)
    (fun j r hr => (hgeom.2.2.2.2.1 r (hcell j r hr)).ne')
    (hN.control_product_jets_cell_bound hS hT) hN.1.1.inverse_first_jets_cell_bound

/-- Uniform normalization of the two singleton direction grades. -/
theorem singletonKappaDirection_two_grades_le
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m b c : ℕ) (hM : 1 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    stateGrading S b (singletonKappaDirection hS m) +
        stateGrading S c (singletonKappaDirection hS m) ≤
      (circleSingletonGradingConstant b + circleSingletonGradingConstant c + 1) *
        (T.M (T.sample m) ^ max b c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) := by
  have hHpow : 0 ≤ T.H (T.sample m) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hH _
  have hM0 : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  have hb := singletonKappaDirection_grading_le hS m b hM hH
  have hc := singletonKappaDirection_grading_le hS m c hM hH
  have hMb : T.M (T.sample m) ^ b ≤ T.M (T.sample m) ^ max b c :=
    pow_le_pow_right₀ hM (Nat.le_max_left _ _)
  have hMc : T.M (T.sample m) ^ c ≤ T.M (T.sample m) ^ max b c :=
    pow_le_pow_right₀ hM (Nat.le_max_right _ _)
  have hW : 0 ≤ T.M (T.sample m) ^ max b c * T.H (T.sample m) ^ (-(3 / 4 : ℝ)) :=
    mul_nonneg (pow_nonneg hM0 _) hHpow
  calc
    _ ≤ circleSingletonGradingConstant b *
          (T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) +
        circleSingletonGradingConstant c *
          (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) :=
      add_le_add hb hc
    _ ≤ circleSingletonGradingConstant b *
          (T.M (T.sample m) ^ max b c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) +
        circleSingletonGradingConstant c *
          (T.M (T.sample m) ^ max b c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMb hHpow)
          (circleSingletonGradingConstant_nonneg b))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMc hHpow)
          (circleSingletonGradingConstant_nonneg c))
    _ = (circleSingletonGradingConstant b + circleSingletonGradingConstant c) *
        (T.M (T.sample m) ^ max b c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hW

/-- The actual-cell height weight survives after taking a unit singleton
control direction.  All other losses have explicit coefficient powers. -/
theorem N01Properties.control_deriv_actual_cell_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ K B A : ℝ, 0 < K ∧ 0 < B ∧ 0 < A ∧ ∀ m j r, r ∈ D.cells j →
      |deriv (C.control m) r| ≤
        K * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
          radialE (D.cellIndex j) ^ A *
          (T.M (T.sample m) ^ max base (1 + loss) *
            T.H (T.sample m) ^ (-(3 / 4 : ℝ))) := by
  let hdata := hN.control_deriv_cell_bound_with_grading hS hT
  let B : ℝ := hdata.choose
  let A : ℝ := hdata.choose_spec.choose
  have hB : 0 < B := hdata.choose_spec.choose_spec.1
  have hA : 0 < A := hdata.choose_spec.choose_spec.2.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  let G := circleSingletonGradingConstant base + circleSingletonGradingConstant (1 + loss) + 1
  have hG : 0 < G := by
    have hb := circleSingletonGradingConstant_nonneg base
    have hc := circleSingletonGradingConstant_nonneg (1 + loss)
    dsimp only [G]
    linarith
  refine ⟨(A * B) * G, B, A, mul_pos (mul_pos hA hB) hG, hB, hA, fun m j r hr => ?_⟩
  have hsample (i : ℕ) : T.sample i ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hgeom.2.1 i
  have hpM := hT.2.1 (T.sample m) (hsample m)
  have hpJ := hT.2.1 (T.sample j) (hsample j)
  have hgrade := singletonKappaDirection_two_grades_le
    (hS.2.1 (3 / 4 : ℝ)) m base (1 + loss) hpM.2.2.2 hpM.2.1.le
  have hfactor : 0 ≤ (A * B) * T.H (T.sample j) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample j) ^ B * radialE (D.cellIndex j) ^ A := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hA.le hB.le) (Real.rpow_nonneg hpJ.2.1.le _))
        (Real.rpow_nonneg hpJ.2.2.1.le _))
      (Real.rpow_nonneg (Real.exp_pos _).le _)
  exact (hdata.choose_spec.choose_spec.2.2 m j r hr).trans
    ((mul_le_mul_of_nonneg_left hgrade hfactor).trans_eq (by dsimp only [G]; ring))

end ContinuousFlexibility.Statements
