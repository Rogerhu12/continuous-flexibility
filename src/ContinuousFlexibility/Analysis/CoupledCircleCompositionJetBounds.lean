module

public import ContinuousFlexibility.Analysis.CoupledCircleCompositionExpansion
public import ContinuousFlexibility.Analysis.CoupledCircleCompositionTermBounds
public import ContinuousFlexibility.Analysis.SpacesNemytskiiLowFactors

/-!
# Fixed-loss bounds for the complete angular composition jets

The chart factors are bounded in one fixed low seminorm. The outer
function and each direction retain exactly one linear occurrence, with
one high seminorm among them or on the chart displacement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def coupledCircleKernelMajorant (M : CircleModelData) (base high : ℕ)
    (ψ : M.Space) {n : ℕ} (v : Fin n → M.Space) : ℝ :=
  (1 + M.grading high ψ) * ∏ i, M.grading base (v i) +
    ∑ i, M.grading high (v i) * ∏ j ∈ Finset.univ.erase i, M.grading base (v j)

theorem coupledCircleKernelMajorant_nonneg (M : CircleModelData) (base high : ℕ)
    (ψ : M.Space) {n : ℕ} (v : Fin n → M.Space) :
    0 ≤ coupledCircleKernelMajorant M base high ψ v := by
  apply add_nonneg
  · exact mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  · exact Finset.sum_nonneg (fun _ _ => mul_nonneg (apply_nonneg _ _)
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))

private theorem coupled_factor_family_bound
    {E : Type*} (p q : E → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    {k : ℕ} (t : CoupledCircleCompositionTerm k) (ψ v : E) (w : Fin k → E)
    {R : ℝ} (hR : 1 ≤ R) (hψ : p ψ ≤ R) :
    (∑ i, q (t.factorFamily v ψ w i) *
      ∏ j ∈ Finset.univ.erase i, p (t.factorFamily v ψ w j)) ≤
      ((t.baseFactors : ℝ) + 1) * R ^ t.baseFactors *
        ((1 + q ψ) * ∏ i : Fin (k + 1), p ((Fin.cons v w : Fin (k + 1) → E) i) +
          ∑ i : Fin (k + 1), q ((Fin.cons v w : Fin (k + 1) → E) i) *
            ∏ j ∈ Finset.univ.erase i, p ((Fin.cons v w : Fin (k + 1) → E) j)) := by
  have hmap (f : E → ℝ) (i : Fin t.baseFactors ⊕ Fin (k + 1)) :
      f (t.factorFamily v ψ w i) =
        Sum.elim (fun _ : Fin t.baseFactors => f ψ)
          (fun j => f ((Fin.cons v w : Fin (k + 1) → E) j)) i := by
    cases i <;> rfl
  have he : (∑ i, q (t.factorFamily v ψ w i) *
      ∏ j ∈ Finset.univ.erase i, p (t.factorFamily v ψ w j)) =
      ∑ i : Fin t.baseFactors ⊕ Fin (k + 1),
        Sum.elim (fun _ : Fin t.baseFactors => q ψ)
          (fun j => q ((Fin.cons v w : Fin (k + 1) → E) j)) i *
          ∏ j ∈ Finset.univ.erase i,
            Sum.elim (fun _ : Fin t.baseFactors => p ψ)
              (fun j => p ((Fin.cons v w : Fin (k + 1) → E) j)) j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hmap q i]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => hmap p j)
  exact he.trans_le (spaces_repeated_low_factors_bound t.baseFactors (k + 1)
    (p ψ) (q ψ) R (fun i => p ((Fin.cons v w : Fin (k + 1) → E) i))
    (fun i => q ((Fin.cons v w : Fin (k + 1) → E) i))
    hR (hp ψ) hψ (hq ψ) (fun _ => hp _) (fun _ => hq _))

private theorem coupled_circle_composition_term_local_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading) :
    ∃ base loss : ℕ, ∀ (k : ℕ) (t : CoupledCircleCompositionTerm k) (c s : ℕ),
      t.order + c ≤ s → ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : M.Space), M.grading base ψ ≤ R →
      ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
        |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
          C * (T.M (T.sample m))⁻¹ *
            coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) := by
  classical
  have hexists := coupled_circle_composition_term_one_high hT hsample hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hterm : ∀ (k : ℕ) (t : CoupledCircleCompositionTerm k) (c s : ℕ),
      t.order + c ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v ψ : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
        |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
          C * (T.M (T.sample m))⁻¹ *
            ∑ i, M.grading (s + loss) (t.factorFamily v ψ w i) *
              ∏ j ∈ Finset.univ.erase i, M.grading base (t.factorFamily v ψ w j) :=
    hexists.choose_spec.choose_spec
  refine ⟨base, loss, fun k t c s ht R hR => ?_⟩
  have hAexists := hterm k t c s ht
  let A : ℝ := hAexists.choose
  have hA : 0 ≤ A := hAexists.choose_spec.1
  have hbound : ∀ (v ψ : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
      |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
          t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
        A * (T.M (T.sample m))⁻¹ *
          ∑ i, M.grading (s + loss) (t.factorFamily v ψ w i) *
            ∏ j ∈ Finset.univ.erase i, M.grading base (t.factorFamily v ψ w j) :=
    hAexists.choose_spec.2
  let B : ℝ := ((t.baseFactors : ℝ) + 1) * R ^ t.baseFactors
  have hB : 0 ≤ B := mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hR) _)
  refine ⟨A * B, mul_nonneg hA hB, fun ψ hψ v w m θ => ?_⟩
  have hi : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hsample m)).2.2.2)
  have hsum :
      (∑ i, M.grading (s + loss) (t.factorFamily v ψ w i) *
        ∏ j ∈ Finset.univ.erase i, M.grading base (t.factorFamily v ψ w j)) ≤
      B * coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) :=
    coupled_factor_family_bound (M.grading base) (M.grading (s + loss))
      (fun _ => apply_nonneg _ _) (fun _ => apply_nonneg _ _) t ψ v w hR hψ
  exact (hbound v ψ w m θ).trans
    ((mul_le_mul_of_nonneg_left hsum (mul_nonneg hA hi)).trans_eq (by ac_rfl))

/-- Every differentiated composition kernel has the same low base and the
same interpolation loss. The outer angular order is included in its
explicit derivative budget. -/
theorem coupled_circle_composition_jet_tame
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading) :
    ∃ base loss : ℕ, ∀ (r k b c s : ℕ), r + b + c ≤ s →
      ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : M.Space), M.grading base ψ ≤ R →
      ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
        |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            iteratedDeriv b (fun θ => iteratedDeriv r (M.decode v m)
              (θ + M.decode ψ m θ) * ∏ i, M.decode (w i) m θ) θ| ≤
          C * (T.M (T.sample m))⁻¹ *
            coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) := by
  classical
  have hexists := coupled_circle_composition_term_local_bound hT hsample hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hterm : ∀ (k : ℕ) (t : CoupledCircleCompositionTerm k) (c s : ℕ),
      t.order + c ≤ s → ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : M.Space), M.grading base ψ ≤ R →
      ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
        |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
          C * (T.M (T.sample m))⁻¹ *
            coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) :=
    hexists.choose_spec.choose_spec
  refine ⟨base, loss, fun r k b c s hs R hR => ?_⟩
  have hlist (L : List (CoupledCircleCompositionTerm k))
      (hL : ∀ t ∈ L, t.order + c ≤ s) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
          |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
              CoupledCircleCompositionTerm.evaluateTerms L
                (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
            C * (T.M (T.sample m))⁻¹ *
              coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) := by
    induction L with
    | nil =>
      exact ⟨0, le_rfl, fun _ _ _ _ _ _ => by
        simp only [CoupledCircleCompositionTerm.evaluateTerms_nil, mul_zero, abs_zero,
          zero_mul, le_refl]⟩
    | cons t L ih =>
      have hAexists := hterm k t c s (hL t (List.mem_cons_self)) R hR
      let A : ℝ := hAexists.choose
      have hA : 0 ≤ A := hAexists.choose_spec.1
      have ha : ∀ ψ : M.Space, M.grading base ψ ≤ R →
          ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
            |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
              t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
              A * (T.M (T.sample m))⁻¹ *
                coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) :=
        hAexists.choose_spec.2
      have hBexists := ih (fun τ hτ => hL τ (List.mem_cons_of_mem _ hτ))
      let B : ℝ := hBexists.choose
      have hB : 0 ≤ B := hBexists.choose_spec.1
      have hb : ∀ ψ : M.Space, M.grading base ψ ≤ R →
          ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
            |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
                CoupledCircleCompositionTerm.evaluateTerms L
                  (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
              B * (T.M (T.sample m))⁻¹ *
                coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) :=
        hBexists.choose_spec.2
      refine ⟨A + B, add_nonneg hA hB, fun ψ hψ v w m θ => ?_⟩
      rw [CoupledCircleCompositionTerm.evaluateTerms_cons, mul_add]
      calc
        _ ≤ |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            t.evaluate (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| +
          |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            CoupledCircleCompositionTerm.evaluateTerms L
              (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| := abs_add_le _ _
        _ ≤ A * (T.M (T.sample m))⁻¹ *
            coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) +
          B * (T.M (T.sample m))⁻¹ *
            coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) :=
          add_le_add (ha ψ hψ v w m θ) (hb ψ hψ v w m θ)
        _ = _ := by rw [add_mul, add_mul]
  have hCexists := hlist (CoupledCircleCompositionTerm.expansion r k b)
    (fun t ht => (Nat.add_le_add_right
      (CoupledCircleCompositionTerm.expansion_order r k b t ht) c).trans hs)
  let C : ℝ := hCexists.choose
  have hC : 0 ≤ C := hCexists.choose_spec.1
  have hbound : ∀ ψ : M.Space, M.grading base ψ ≤ R →
      ∀ (v : M.Space) (w : Fin k → M.Space) (m : ℕ) (θ : ℝ),
        |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
            CoupledCircleCompositionTerm.evaluateTerms (CoupledCircleCompositionTerm.expansion r k b)
              (M.decode v m) (M.decode ψ m) (fun i => M.decode (w i) m) θ| ≤
          C * (T.M (T.sample m))⁻¹ *
            coupledCircleKernelMajorant M base (s + loss) ψ (Fin.cons v w) :=
    hCexists.choose_spec.2
  refine ⟨C, hC, fun ψ hψ v w m θ => ?_⟩
  have he := CoupledCircleCompositionTerm.evaluate_expansion r k b
    ((hM.2.2.2.1 v).1 m).1 ((hM.2.2.2.1 ψ).1 m).1
    (fun i => ((hM.2.2.2.1 (w i)).1 m).1)
  exact (congrArg (fun x : ℝ =>
    |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) * x|)
      (congrFun he θ).symm).trans_le (hbound ψ hψ v w m θ)

end ContinuousFlexibility.Statements
