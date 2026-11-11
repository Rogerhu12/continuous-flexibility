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
  classical
  letI : TopologicalSpace (AnnularState S) := inferInstance
  letI : AddCommGroup (AnnularState S) := inferInstance
  letI : Module ℝ (AnnularState S) := inferInstance
  letI : IsTopologicalAddGroup (AnnularState S) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S) := inferInstance
  letI : TopologicalSpace (AnnularState S × ℝ) := inferInstance
  letI : AddCommGroup (AnnularState S × ℝ) := inferInstance
  letI : Module ℝ (AnnularState S × ℝ) := inferInstance
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  let p := pairGrading (stateGrading S) realGrading
  obtain ⟨RH, hRH, hRHb⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hH (q : PolarPoint) (hq : q ∈ annularOpen D) :
      0 ≤ T.H q.1 ^ (3 / 4 : ℝ) ∧ T.H q.1 ^ (3 / 4 : ℝ) ≤ RH := by
    refine ⟨Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _, ?_⟩
    simpa only [Real.rpow_zero, mul_one] using hRHb q.1 hq.1
  intro K s
  choose c A hc hA hb using
    (fun n : Fin (s + 1) => stateU_qPolarMixedJets_oneHigh_bound hT hS hD n.val)
  let C₁ : ℝ := 1 + ∑ n : Fin (s + 1), c n
  let A₁ : ℝ := ∑ n : Fin (s + 1), A n
  have hC₁ : 1 ≤ C₁ := le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => hc n))
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg (fun n _ => hA n)
  have hcC (n) : c n ≤ C₁ :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ n)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAA (n) : A n ≤ A₁ := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ n)
  obtain ⟨CI, hCI, hIb⟩ := hI s
  let M : ℝ := 1 + stateGrading S (s + 4) C.referenceState
  let B : ℝ := C₁ * M * (max 1 RH) * (1 + (K + 1 : ℝ) * CI)
  have hM : 1 ≤ M := le_add_of_nonneg_right (apply_nonneg _ _)
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC₁ hM)
      (le_max_left _ _))
    (le_add_of_nonneg_right (mul_nonneg (by positivity) (zero_le_one.trans hCI)))
  refine ⟨B, A₁, hB, hA₁, ?_⟩
  intro k hk a b hab q hq J z hz hlow v hv R hR hhigh hvhigh
  let n : Fin (s + 1) := ⟨a + b, Nat.lt_succ_of_le hab⟩
  let Jq := J.congr (fun y _ =>
    mixedDerivative_const_mul y.2 (stateUPolarInput S i y.1) a b q)
  have hqparam : |z.2| ≤ 1 := hz.2.le.trans hε
  have hraw := hb n i a b le_rfl q hq (stateNeighborhood S C base ε) Jq
    k base C.referenceState z hz hqparam v
  let P : ℝ := R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hP : 1 ≤ P := Real.one_le_rpow hR (spatialOrder_fraction_nonneg (a + b) s)
  have hoh := oneHighVariationWeight_unit_le_power p base (a + b + 4)
    hk (z - (C.referenceState, 0)) v hv (zero_le_one.trans hCI) hP
    (hIb (a + b) hab _ hlow R hR hhigh)
    (fun j => hIb (a + b) hab _ (hv j) R hR (hvhigh j))
  have hMle : 1 + stateGrading S (a + b + 4) C.referenceState ≤ M :=
    add_le_add le_rfl ((stateGrading_monotone S (by omega)) C.referenceState)
  have hweight : T.H q.1 ^ (3 / 4 : ℝ) ≤
      max 1 RH * parameterHeightWeight (T.H q.1 ^ (3 / 4 : ℝ)) k := by
    by_cases hk0 : k = 0
    · simpa only [parameterHeightWeight, if_pos hk0, mul_one] using
        (hH q hq).2.trans (le_max_right _ _)
    · simpa only [parameterHeightWeight, if_neg hk0] using
        le_mul_of_one_le_left (hH q hq).1 (le_max_left 1 RH)
  have hEpow : T.E0 q.1 ^ A n ≤ T.E0 q.1 ^ A₁ :=
    Real.rpow_le_rpow_of_exponent_le (hE q.1 hq.1) (hAA n)
  have hmid :
      c n * T.E0 q.1 ^ A n * T.H q.1 ^ (3 / 4 : ℝ) *
          (1 + stateGrading S (a + b + 4) C.referenceState) *
          oneHighVariationWeight p base (a + b + 4) (z - (C.referenceState, 0)) v ≤
      C₁ * T.E0 q.1 ^ A₁ *
          (max 1 RH * parameterHeightWeight (T.H q.1 ^ (3 / 4 : ℝ)) k) *
          M * ((1 + (K + 1 : ℝ) * CI) * P) := by
    gcongr
    · exact hcC n
    · exact hEpow
    · exact hweight
    · exact hMle
    · exact hoh
  have hh := coefficientPolarInput_norm_weight_order (hraw.trans hmid)
  simpa only [Jq, SmoothDirections.congr, B, P] using hh

end ContinuousFlexibility.Statements
