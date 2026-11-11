import ContinuousFlexibility.Analysis.N01cCoefficientRadialPowerInputs

/-!
# Actual polar-height inputs at the common interpolation indices

The existing physical bounds have fixed loss four. Interpolation is
applied to the actual assigned spatial order before products are formed.
The scalar perturbation parameter is controlled by the original
neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem oneHighVariationWeight_unit_le_power
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) {K k : ℕ} (hk : k ≤ K)
    (x : X) (v : Fin k → X) (hv : ∀ i, p base (v i) ≤ 1)
    {C P : ℝ} (hC : 0 ≤ C) (hP : 1 ≤ P)
    (hx : p high x ≤ C * P) (hhigh : ∀ i, p high (v i) ≤ C * P) :
    oneHighVariationWeight p base high x v ≤ (1 + (K + 1 : ℝ) * C) * P := by
  have hprod : (∏ i, p base (v i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => apply_nonneg _ _) (fun i _ => hv i)
  have herase (i : Fin k) : (∏ j ∈ Finset.univ.erase i, p base (v j)) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => apply_nonneg _ _) (fun j _ => hv j)
  have hs : (∑ i : Fin k, p high (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j)) ≤
      (k : ℝ) * (C * P) := by
    calc
      _ ≤ ∑ i : Fin k, C * P :=
        Finset.sum_le_sum (fun i _ =>
          (mul_le_mul_of_nonneg_left (herase i) (apply_nonneg _ _)).trans
            (by simpa only [mul_one] using hhigh i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkR : (k : ℝ) ≤ K := by exact_mod_cast hk
  unfold oneHighVariationWeight
  have hp := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 1 + p high x by positivity)
  have hCP : 0 ≤ C * P := mul_nonneg hC (zero_le_one.trans hP)
  nlinarith [mul_le_mul_of_nonneg_right hkR hCP]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

def coefficientPolarInput_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hD : 0 < D.a)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) (i : Fin 5) :
    MixedJetRegularity (stateNeighborhood S C base ε) (annularOpen D)
      (fun z q => z.2 * stateUPolarInput S i z.1 q) where
  spatial z _ := contDiffOn_const.mul (contDiffOn_stateUPolarInput hT hS hD z.1 i)
  parameter a b q hq :=
    ((qStateUPolarMixedJetSmoothDirections hT hS a b q hq
      (hD.trans hq.1.1).ne' i).restrict
        (isOpen_stateNeighborhood S C base ε) (subset_univ _)).congr
      (fun z _ => (mixedDerivative_const_mul z.2 (stateUPolarInput S i z.1) a b q).symm)

/-- Scalar weight rearrangement is independent of the state-space instances. -/
private theorem coefficientPolarInput_norm_weight_order
    {u C E V W M I P : ℝ}
    (h : |u| ≤ C * E * (V * W) * M * (I * P)) :
    ‖u‖ ≤ (C * M * V * I) * E * W * P := by
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by ring)

/-- All quantitative selection and interpolation takes place before the
abstract state is specialized to the physical projective-limit model. -/
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientPolarInput_powerBounds_of_raw
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (p : ℕ → Seminorm ℝ Y) (hp : Monotone p)
    (F : Fin 5 → Y → PolarPoint → ℝ) (Ω : Set PolarPoint)
    (H E : PolarPoint → ℝ) (U : Set (Y × ℝ)) (x0 : Y) (base loss : ℕ)
    (hscalar : ∀ z ∈ U, |z.2| ≤ 1)
    (hHbound : ∃ RH : ℝ, 0 < RH ∧ ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH)
    (hE : ∀ q ∈ Ω, 1 ≤ E q)
    (hI : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, n ≤ s → ∀ x : Y × ℝ,
      pairGrading p realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading p realGrading (s + loss) x ≤ R →
        pairGrading p realGrading (n + 4) x ≤
          C * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (hraw : ∀ s : ℕ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 5, ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ Ω,
      ∀ V : Set (Y × ℝ),
      ∀ J : SmoothDirections V (fun z => z.2 * mixedDerivative a b (F i z.1) q),
      ∀ k b0 : ℕ, ∀ y0 : Y, ∀ z ∈ V, |z.2| ≤ 1 →
      ∀ v : Fin k → Y × ℝ,
        |J.D k z v| ≤ C * E q ^ A * H q * (1 + p (s + 4) y0) *
          oneHighVariationWeight (pairGrading p realGrading)
            b0 (s + 4) (z - (y0, 0)) v)
    (i : Fin 5) :
    MixedPowerBounds (pairGrading p realGrading) (x0, 0) base loss U Ω H E
      (fun z q => z.2 * F i z.1 q) := by
  classical
  let pjoint := pairGrading p realGrading
  obtain ⟨RH, hRH, hH⟩ := hHbound
  intro K s
  choose c A hc hA hb using (fun n : Fin (s + 1) => hraw n.val)
  let C₁ : ℝ := 1 + ∑ n : Fin (s + 1), c n
  let A₁ : ℝ := ∑ n : Fin (s + 1), A n
  have hsumC : 0 ≤ ∑ n : Fin (s + 1), c n :=
    Finset.sum_nonneg (fun n _ => hc n)
  have hC₁ : 1 ≤ C₁ := le_add_of_nonneg_right hsumC
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg (fun n _ => hA n)
  have hcC (n : Fin (s + 1)) : c n ≤ C₁ :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ n)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAA (n : Fin (s + 1)) : A n ≤ A₁ :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ n)
  obtain ⟨CI, hCI, hIb⟩ := hI s
  let M : ℝ := 1 + p (s + 4) x0
  let B : ℝ := C₁ * M * (max 1 RH) * (1 + (K + 1 : ℝ) * CI)
  have hM : 1 ≤ M := le_add_of_nonneg_right (apply_nonneg _ _)
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC₁ hM)
      (le_max_left _ _))
    (le_add_of_nonneg_right (mul_nonneg (by positivity) (zero_le_one.trans hCI)))
  refine ⟨B, A₁, hB, hA₁, ?_⟩
  intro k hk a b hab q hq J z hz hlow v hv R hR hhigh hvhigh
  let n : Fin (s + 1) := ⟨a + b, Nat.lt_succ_of_le hab⟩
  let Jq : SmoothDirections U (fun y => y.2 * mixedDerivative a b (F i y.1) q) :=
    J.congr (fun y _ => mixedDerivative_const_mul y.2 (F i y.1) a b q)
  have hrawq := hb n i a b le_rfl q hq U Jq k base x0 z hz (hscalar z hz) v
  let P : ℝ := R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hP : 1 ≤ P := Real.one_le_rpow hR (spatialOrder_fraction_nonneg (a + b) s)
  have hoh := oneHighVariationWeight_unit_le_power pjoint base (a + b + 4)
    hk (z - (x0, 0)) v hv (zero_le_one.trans hCI) hP
    (hIb (a + b) hab _ hlow R hR hhigh)
    (fun j => hIb (a + b) hab _ (hv j) R hR (hvhigh j))
  have hMle : 1 + p (a + b + 4) x0 ≤ M :=
    add_le_add le_rfl ((hp (by omega)) x0)
  have hweight : H q ≤ max 1 RH * parameterHeightWeight (H q) k := by
    by_cases hk0 : k = 0
    · simpa only [parameterHeightWeight, if_pos hk0, mul_one] using
        (hH q hq).2.trans (le_max_right _ _)
    · simpa only [parameterHeightWeight, if_neg hk0] using
        le_mul_of_one_le_left (hH q hq).1 (le_max_left 1 RH)
  have hEpos : 0 < E q := zero_lt_one.trans_le (hE q hq)
  have hEpow : E q ^ A n ≤ E q ^ A₁ :=
    Real.rpow_le_rpow_of_exponent_le (hE q hq) (hAA n)
  have hCE : c n * E q ^ A n ≤ C₁ * E q ^ A₁ :=
    mul_le_mul (hcC n) hEpow (Real.rpow_nonneg hEpos.le _) (zero_le_one.trans hC₁)
  have hCE0 : 0 ≤ C₁ * E q ^ A₁ :=
    mul_nonneg (zero_le_one.trans hC₁) (Real.rpow_nonneg hEpos.le _)
  have hCH := mul_le_mul hCE hweight (hH q hq).1 hCE0
  have hCH0 : 0 ≤ C₁ * E q ^ A₁ * (max 1 RH * parameterHeightWeight (H q) k) :=
    mul_nonneg hCE0 (mul_nonneg (zero_le_one.trans (le_max_left 1 RH))
      (parameterHeightWeight_nonneg (hH q hq).1 k))
  have hCHM := mul_le_mul hCH hMle
    (show 0 ≤ 1 + p (a + b + 4) x0 by positivity) hCH0
  have hmid := mul_le_mul hCHM hoh
    (oneHighVariationWeight_nonneg pjoint base (a + b + 4) (z - (x0, 0)) v)
    (mul_nonneg hCH0 (zero_le_one.trans hM))
  have hh := coefficientPolarInput_norm_weight_order (hrawq.trans hmid)
  simpa only [Jq, SmoothDirections.congr, B, P] using hh

/-- The material-only bound is selected independently of the state-space type. -/
private theorem coefficientPolarInput_height_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ RH : ℝ, 0 < RH ∧ ∀ q ∈ annularOpen D,
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) ∧ T.H q.1 ^ (3 / 4 : ℝ) ≤ RH := by
  obtain ⟨RH, hRH, hb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  refine ⟨RH, hRH, fun q hq => ⟨Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _, ?_⟩⟩
  simpa only [Real.rpow_zero, mul_one] using hb q.1 hq.1

/-- All five actual polar inputs have the distributed mixed bound on the
same neighbourhood and at the same fixed interpolation indices. -/
theorem coefficientPolarInput_powerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hD : 0 < D.a)
    (C : NonlinearGeometryData S) (base loss : ℕ) {ε : ℝ} (hε : ε ≤ 1)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hI : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          C * R ^ ((n : ℝ) / ((s : ℝ) + 1))) (i : Fin 5) :
    MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
      (fun z q => z.2 * stateUPolarInput S i z.1 q) := by
  exact coefficientPolarInput_powerBounds_of_raw
    (Y := AnnularState S)
    (stateGrading S) (stateGrading_monotone S) (stateUPolarInput S) (annularOpen D)
    (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
    (stateNeighborhood S C base ε) C.referenceState base loss
    (fun z hz => hz.2.le.trans hε)
    (coefficientPolarInput_height_bound hT) (fun q hq => hE q.1 hq.1) hI
    (fun s => stateU_qPolarMixedJets_oneHigh_bound hT hS hD s) i

end ContinuousFlexibility.Statements
