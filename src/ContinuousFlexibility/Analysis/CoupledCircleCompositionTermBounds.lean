import ContinuousFlexibility.Analysis.CoupledCircleCompositionTerms
import ContinuousFlexibility.Analysis.SpacesInterpolationProducts

/-!
# One high factor in the weighted circle composition terms

The outer function is a distinguished linear factor. All repeated factors
come from the chart displacement. An extra sample weight supplies the
fixed square-summable envelope without imposing an inverse-chart condition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

namespace CoupledCircleCompositionTerm

variable {k : ℕ}

def factorOrder (t : CoupledCircleCompositionTerm k) (c : ℕ) :
    Fin t.baseFactors ⊕ Fin (k + 1) → ℕ :=
  Sum.elim t.baseOrder (Fin.cons (t.outerOrder + c) t.directionOrder)

def factorFamily {E : Type*} (t : CoupledCircleCompositionTerm k)
    (v ψ : E) (w : Fin k → E) : Fin t.baseFactors ⊕ Fin (k + 1) → E :=
  Sum.elim (fun _ => ψ) (Fin.cons v w)

theorem factorOrder_sum (t : CoupledCircleCompositionTerm k) (c : ℕ) :
    (∑ i, t.factorOrder c i) = t.order + c := by
  simp only [factorOrder, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, order]
  omega

private theorem abs_prod_le {ι : Type*} [Fintype ι]
    (f B : ι → ℝ) (h : ∀ i, |f i| ≤ B i) :
    |∏ i, f i| ≤ ∏ i, B i := by
  calc
    _ = ‖∏ i, f i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∏ i, ‖f i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, B i := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h i)

theorem weightedEvaluate_prebound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hM : IsCircleModel T γ M) {K : ℝ} (hK : 0 ≤ K)
    (hjet : ∀ (u : M.Space) (m b : ℕ) (θ : ℝ),
      |iteratedDeriv b (M.decode u m) θ| ≤ K * M.grading (b + 1) u)
    (t : CoupledCircleCompositionTerm k) (c : ℕ)
    (v ψ : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ) :
    |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
      (anglePairEvaluationConstant * K ^ (t.baseFactors + k)) *
        (T.M (T.sample m))⁻¹ *
        ∏ i, M.grading (t.factorOrder c i + 2) (t.factorFamily v ψ w i) := by
  have hp : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hsample m)).2.2.2)
  have hb : |∏ i, iteratedDeriv (t.baseOrder i + 1) (M.decode ψ m) θ| ≤
      K ^ t.baseFactors * ∏ i, M.grading (t.baseOrder i + 2) ψ := by
    calc
      _ ≤ ∏ i, K * M.grading (t.baseOrder i + 2) ψ := by
        apply abs_prod_le
        intro i
        simpa only [Nat.add_assoc] using hjet ψ m (t.baseOrder i + 1) θ
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hd : |∏ i, iteratedDeriv (t.directionOrder i) (M.decode (w i) m) θ| ≤
      K ^ k * ∏ i, M.grading (t.directionOrder i + 2) (w i) := by
    calc
      _ ≤ ∏ i, K * M.grading (t.directionOrder i + 2) (w i) := by
        apply abs_prod_le
        intro i
        exact (hjet (w i) m (t.directionOrder i) θ).trans
          (mul_le_mul_of_nonneg_left
            (gradedSeminorm_monotone _ _ (by omega : t.directionOrder i + 1 ≤
              t.directionOrder i + 2) (w i)) hK)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have ho := coupled_circle_weighted_jet_envelope hT hsample hM v m t.outerOrder c
    (θ + M.decode ψ m θ)
  have hbo : 0 ≤ K ^ t.baseFactors * ∏ i, M.grading (t.baseOrder i + 2) ψ :=
    mul_nonneg (pow_nonneg hK _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  have hoo : 0 ≤ (T.M (T.sample m))⁻¹ *
      (anglePairEvaluationConstant * M.grading (t.outerOrder + c + 2) v) :=
    mul_nonneg hp (mul_nonneg anglePairEvaluationConstant_nonneg (apply_nonneg _ _))
  calc
    _ = (|(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv t.outerOrder (M.decode v m) (θ + M.decode ψ m θ)| *
          |∏ i, iteratedDeriv (t.baseOrder i + 1) (M.decode ψ m) θ|) *
        |∏ i, iteratedDeriv (t.directionOrder i) (M.decode (w i) m) θ| := by
      simp only [evaluate, ← mul_assoc, abs_mul]
    _ ≤ (((T.M (T.sample m))⁻¹ *
        (anglePairEvaluationConstant * M.grading (t.outerOrder + c + 2) v)) *
          (K ^ t.baseFactors * ∏ i, M.grading (t.baseOrder i + 2) ψ)) *
        (K ^ k * ∏ i, M.grading (t.directionOrder i + 2) (w i)) :=
      mul_le_mul (mul_le_mul ho hb (abs_nonneg _) hoo) hd (abs_nonneg _)
        (mul_nonneg hoo hbo)
    _ = _ := by
      simp only [factorOrder, factorFamily, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, pow_add]
      ac_rfl

end CoupledCircleCompositionTerm

/-- The loss and low base are independent of the number of repeated
chart factors and of the requested angular derivative order. -/
theorem coupled_circle_composition_term_one_high
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading) :
    ∃ base loss : ℕ, ∀ (k : ℕ) (t : CoupledCircleCompositionTerm k) (c s : ℕ),
      t.order + c ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v ψ : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
        |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
          C * (T.M (T.sample m))⁻¹ *
            ∑ i, M.grading (s + loss) (t.factorFamily v ψ w i) *
              ∏ j ∈ Finset.univ.erase i, M.grading base (t.factorFamily v ψ w j) := by
  classical
  obtain ⟨K, hK, hjet⟩ := coupled_circle_jet_uniform_bound hT hsample hγ hM
  obtain ⟨base, loss, hprod⟩ := spaces_interpolation_product_bound M.grading
    (fun u i j hij => gradedSeminorm_monotone _ _ hij u) hI
  refine ⟨base, loss, fun k t c s horder => ?_⟩
  letI : Nonempty (Fin t.baseFactors ⊕ Fin (k + 1)) := ⟨Sum.inr 0⟩
  have hbudget : (∑ i, t.factorOrder c i) ≤ s := by
    rw [t.factorOrder_sum]
    exact horder
  obtain ⟨C, hC, hbound⟩ := hprod (t.factorOrder c) s hbudget
  let A : ℝ := anglePairEvaluationConstant * K ^ (t.baseFactors + k)
  have hA : 0 ≤ A := mul_nonneg anglePairEvaluationConstant_nonneg
    (pow_nonneg (zero_le_one.trans hK) _)
  refine ⟨A * C, mul_nonneg hA hC, fun v ψ w m θ => ?_⟩
  have hp : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hsample m)).2.2.2)
  calc
    _ ≤ A * (T.M (T.sample m))⁻¹ *
        ∏ i, M.grading (t.factorOrder c i + 2) (t.factorFamily v ψ w i) :=
      t.weightedEvaluate_prebound hT hsample hM (zero_le_one.trans hK) hjet c v ψ w m θ
    _ ≤ A * (T.M (T.sample m))⁻¹ *
        (C * ∑ i, M.grading (s + loss) (t.factorFamily v ψ w i) *
          ∏ j ∈ Finset.univ.erase i, M.grading base (t.factorFamily v ψ w j)) :=
      mul_le_mul_of_nonneg_left (hbound (t.factorFamily v ψ w)) (mul_nonneg hA hp)
    _ = _ := by ac_rfl

end ContinuousFlexibility.Statements
