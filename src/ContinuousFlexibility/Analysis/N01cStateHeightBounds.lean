module

public import ContinuousFlexibility.Analysis.N01cCutoffJetBounds
public import ContinuousFlexibility.Analysis.N01cStateHeightJets
public import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Fixed-loss bounds for the actual state height direction

The scalar cutoff contributes only compactly supported positive-order
jets. Combining these with the decoded physical height gives a bound
for every positive-order mixed jet of stateU with exactly two additional
input grading orders and the original H^(3/4) weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

open Set

private theorem paired_height_component_le
    {H K : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup K] [Module ℝ K]
    (p : Seminorm ℝ H) (q : Seminorm ℝ K)
    (x : (H × ℝ) × (ℝ × (K × K))) :
    p x.1.1 ≤ (p x.1.1 + ‖x.1.2‖) +
      (‖x.2.1‖ + (q x.2.2.1 + q x.2.2.2)) := by
  have hc := norm_nonneg x.1.2
  have hν := norm_nonneg x.2.1
  have hκ := apply_nonneg q x.2.2.1
  have hh := apply_nonneg q x.2.2.2
  linarith only [hc, hν, hκ, hh]

private theorem paired_height_scalar_le
    {H K : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup K] [Module ℝ K]
    (p : Seminorm ℝ H) (q : Seminorm ℝ K)
    (x : (H × ℝ) × (ℝ × (K × K))) :
    |x.1.2| ≤ (p x.1.1 + ‖x.1.2‖) +
      (‖x.2.1‖ + (q x.2.2.1 + q x.2.2.2)) := by
  have hf := apply_nonneg p x.1.1
  have hν := norm_nonneg x.2.1
  have hκ := apply_nonneg q x.2.2.1
  have hh := apply_nonneg q x.2.2.2
  rw [Real.norm_eq_abs]
  linarith only [hf, hν, hκ, hh]

theorem state_height_grading_le (S : PhysicalSpacesData) (n : ℕ)
    (x : AnnularState S) :
    (S.height (3 / 4 : ℝ)).grading n x.1.1 ≤ stateGrading S n x :=
  (paired_height_component_le ((S.height (3 / 4 : ℝ)).grading n)
    ((S.circle (3 / 4 : ℝ)).grading n) x).trans_eq
      (stateGrading_apply S n x).symm

theorem abs_stateHeightScalar_le_stateGrading (S : PhysicalSpacesData) (n : ℕ)
    (x : AnnularState S) :
    |x.1.2| ≤ stateGrading S n x :=
  (paired_height_scalar_le ((S.height (3 / 4 : ℝ)).grading n)
    ((S.circle (3 / 4 : ℝ)).grading n) x).trans_eq
      (stateGrading_apply S n x).symm

/-- The scalar estimate is proved before specializing the model to a
component of the full state. The only transfer data are the two component
inequalities and the already proved exact mixed-jet formula. -/
private theorem decodedCutoff_family_positiveMixedJets_bound
    {D : ReferenceData} {T : MaterialData} {M : SobolevModelData}
    {χ : ℝ → ℝ} {γ : ℝ} {X : Type*}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (hχ : CutoffConditions D χ)
    (f : X → PolarPoint → ℝ) (u : X → M.Space) (c : X → ℝ)
    (G : ℕ → X → ℝ)
    (hu : ∀ n x, M.grading n (u x) ≤ G n x)
    (hc : ∀ n x, |c x| ≤ G n x)
    (hjets : ∀ x a b p, mixedDerivative a b (f x) p =
      mixedDerivative a b (M.decode (u x)) p +
        c x * (if b = 0 then iteratedDeriv a χ p.1 else 0))
    (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : X, ∀ a b : ℕ,
      0 < a + b → a + b ≤ s → ∀ p ∈ annularOpen D,
        |mixedDerivative a b (f x) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ γ * G (s + 2) x := by
  obtain ⟨C₀, A, hC₀, hA, hheight⟩ :=
    sobolevModel_physicalMixedJets_le_E0_grading
      (D := D) (T := T) (γ := γ) (M := M) hT hM s
  obtain ⟨Cχ, hCχ, hcutoff⟩ :=
    cutoff_positiveJets_le_materialHeight hT hχ γ s
  obtain ⟨K, hK, hEraise⟩ := materialE0_rpow_le_of_exponent_le hT (A := 0) hA
  refine ⟨C₀ + Cχ * K, A, add_nonneg hC₀ (mul_nonneg hCχ hK), hA,
    fun x a b hab horder p hp => ?_⟩
  have hH : 0 ≤ T.H p.1 ^ γ :=
    Real.rpow_nonneg (hT.2.1 _ hp.1).2.1.le _
  have hE : 0 ≤ T.E0 p.1 ^ A :=
    Real.rpow_nonneg (hT.2.1 _ hp.1).2.2.1.le _
  have hG : 0 ≤ G (s + 2) x :=
    (apply_nonneg (M.grading (s + 2)) (u x)).trans (hu (s + 2) x)
  have hscale : 1 ≤ K * T.E0 p.1 ^ A := by
    simpa only [Real.rpow_zero] using hEraise p.1 hp.1
  have hcut :
      |if b = 0 then iteratedDeriv a χ p.1 else 0| ≤
        Cχ * T.H p.1 ^ γ := by
    split_ifs with hb
    · exact hcutoff a (by omega) (by omega) p.1 hp.1
    · rw [abs_zero]
      exact mul_nonneg hCχ hH
  have hcutraise : Cχ * T.H p.1 ^ γ ≤
      (Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ γ := by
    calc
      _ = (Cχ * T.H p.1 ^ γ) * 1 := (mul_one _).symm
      _ ≤ (Cχ * T.H p.1 ^ γ) * (K * T.E0 p.1 ^ A) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg hCχ hH)
      _ = _ := by ring
  have hdecoded :
      |mixedDerivative a b (M.decode (u x)) p| ≤
        C₀ * T.E0 p.1 ^ A * T.H p.1 ^ γ * G (s + 2) x :=
    (hheight (u x) a b horder p hp).trans
      (mul_le_mul_of_nonneg_left (hu (s + 2) x)
        (mul_nonneg (mul_nonneg hC₀ hE) hH))
  have hscalar :
      |c x * (if b = 0 then iteratedDeriv a χ p.1 else 0)| ≤
        (Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ γ * G (s + 2) x := by
    rw [abs_mul]
    calc
      _ ≤ G (s + 2) x * ((Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ γ) :=
        mul_le_mul (hc (s + 2) x) (hcut.trans hcutraise) (abs_nonneg _) hG
      _ = _ := mul_comm _ _
  rw [hjets x a b p]
  calc
    _ ≤ |mixedDerivative a b (M.decode (u x)) p| +
        |c x * (if b = 0 then iteratedDeriv a χ p.1 else 0)| :=
      abs_add_le _ _
    _ ≤ C₀ * T.E0 p.1 ^ A * T.H p.1 ^ γ * G (s + 2) x +
        (Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ γ * G (s + 2) x :=
      add_le_add hdecoded hscalar
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency true in
/-- The raw product bound for a single genuine state-height jet. The
constant and E0 power are spatially uniform and the input loss is two. -/
theorem stateU_positiveMixedJets_le_E0_stateGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : AnnularState S, ∀ a b : ℕ,
      0 < a + b → a + b ≤ s → ∀ p ∈ annularOpen D,
        |mixedDerivative a b (stateU S x) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
            stateGrading S (s + 2) x := by
  have hM : IsSobolevModel D T (3 / 4 : ℝ) (S.height (3 / 4 : ℝ)) :=
    hS.1 (3 / 4 : ℝ)
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  exact decodedCutoff_family_positiveMixedJets_bound
    (D := D) (T := T) (M := S.height (3 / 4 : ℝ))
    (χ := S.chiLeft) (γ := (3 / 4 : ℝ)) (X := AnnularState S)
    hT hM hχ (stateU S) (fun x => x.1.1) (fun x => x.1.2)
    (fun n x => stateGrading S n x)
    (fun n x => state_height_grading_le S n x)
    (fun n x => abs_stateHeightScalar_le_stateGrading S n x)
    (fun x a b p => mixedDerivative_stateU hT hS a b p x) s

end ContinuousFlexibility.Statements
