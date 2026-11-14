module

public import ContinuousFlexibility.Analysis.SpacesNemytskiiExpansion
public import ContinuousFlexibility.Analysis.SpacesNemytskiiTermZero
public import ContinuousFlexibility.Analysis.SpacesNemytskiiLowFactors

/-!
# Tame bounds for every normalized composition jet

The finite spatial expansion and the repeated-base estimate retain one
fixed low seminorm and one fixed derivative loss for all spatial orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesNemytskiiMajorant (base high : ℕ) {k : ℕ}
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) : ℝ :=
  (1 + spacesPhysicalGrading hT high u) * (∏ i, spacesPhysicalGrading hT base (v i)) +
    ∑ i, spacesPhysicalGrading hT high (v i) *
      ∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT base (v j)

theorem spacesNemytskiiMajorant_nonneg (base high : ℕ) {k : ℕ}
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    0 ≤ spacesNemytskiiMajorant hT base high u v := by
  unfold spacesNemytskiiMajorant
  positivity

theorem spaces_nemytskii_term_tame (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base loss : ℕ, ∀ (γ : ℝ), 0 < γ → ∀ (F : ℝ → ℝ), ContDiff ℝ ∞ F → F 0 = 0 →
      (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C) →
      ∀ (k : ℕ) (t : SpacesNemytskiiTerm T γ k) (c s : ℕ), t.order + c ≤ s →
      ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalJetProjectiveLimit hT), spacesPhysicalGrading hT base u ≤ R →
      ∀ v : Fin k → PhysicalJetProjectiveLimit hT,
        MemLp (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure ∧
        lpNorm (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure ≤
          C * spacesNemytskiiMajorant hT base (s + loss) u v := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_term_one_high hT hI
  refine ⟨base, loss, fun γ hγ F hF hF0 hFb k t c s hs R hR => ?_⟩
  by_cases hn : 0 < k + t.baseFactors
  · obtain ⟨C, hC, hbound⟩ := hb γ hγ F hF hFb k t hn c s hs
    refine ⟨C * (((t.baseFactors : ℝ) + 1) * R ^ t.baseFactors), by positivity,
      fun u hu v => ⟨(hbound u v).1, ?_⟩⟩
    have hlow := spaces_repeated_low_factors_bound t.baseFactors k
      (spacesPhysicalGrading hT base u) (spacesPhysicalGrading hT (s + loss) u) R
      (fun i => spacesPhysicalGrading hT base (v i))
      (fun i => spacesPhysicalGrading hT (s + loss) (v i)) hR
      (apply_nonneg _ _) hu (apply_nonneg _ _)
      (fun i => apply_nonneg _ _) (fun i => apply_nonneg _ _)
    have he (n : ℕ) : (fun i => spacesPhysicalGrading hT n (t.factorFamily u v i)) =
        Sum.elim (fun _ : Fin t.baseFactors => spacesPhysicalGrading hT n u)
          (fun i : Fin k => spacesPhysicalGrading hT n (v i)) := by
      funext i
      cases i <;> rfl
    have hbound' := (hbound u v).2
    have he_apply (n : ℕ) (i : Fin t.baseFactors ⊕ Fin k) := congrFun (he n) i
    simp only [he_apply] at hbound'
    exact hbound'.trans (by
      simpa only [spacesNemytskiiMajorant, mul_assoc] using mul_le_mul_of_nonneg_left hlow hC)
  · have hk : k = 0 := by omega
    subst k
    have hq : t.baseFactors = 0 := by omega
    have hderiv : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |deriv F x| ≤ B := by
      simpa only [iteratedDeriv_one] using hFb 1
    obtain ⟨C, hC, hbound⟩ := spaces_nemytskii_zero_factor_bound hT t hq hF hF0 hderiv
    refine ⟨C, hC, fun u _ v => ⟨(hbound c u v).1, ?_⟩⟩
    apply (hbound c u v).2.trans
    apply mul_le_mul_of_nonneg_left _ hC
    simp only [spacesNemytskiiMajorant, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    exact (gradedSeminorm_monotone _ _ (by omega : c ≤ s + loss) u).trans
      (le_add_of_nonneg_left zero_le_one)

namespace SpacesNemytskiiTerm

def weightedEvaluateTerms {γ : ℝ} {k : ℕ} (L : List (SpacesNemytskiiTerm T γ k))
    (F : ℝ → ℝ) (c : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ c *
    evaluateTerms L F (spacesPhysicalRepresentative hT u)
      (fun i => spacesPhysicalRepresentative hT (v i)) p

theorem weightedEvaluateTerms_nil {γ : ℝ} {k : ℕ} (F : ℝ → ℝ) (c : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    weightedEvaluateTerms hT ([] : List (SpacesNemytskiiTerm T γ k)) F c u v = 0 := by
  funext p
  simp only [weightedEvaluateTerms, evaluateTerms_nil, mul_zero, Pi.zero_apply]

theorem weightedEvaluateTerms_cons {γ : ℝ} {k : ℕ} (t : SpacesNemytskiiTerm T γ k)
    (L : List (SpacesNemytskiiTerm T γ k)) (F : ℝ → ℝ) (c : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    weightedEvaluateTerms hT (t :: L) F c u v =
      t.weightedEvaluate hT F c u v + weightedEvaluateTerms hT L F c u v := by
  funext p
  simp only [weightedEvaluateTerms, evaluateTerms_cons, weightedEvaluate, mul_add, Pi.add_apply]

end SpacesNemytskiiTerm

theorem spaces_nemytskii_expansion_tame (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base loss : ℕ, ∀ (γ : ℝ), 0 < γ → ∀ (F : ℝ → ℝ), ContDiff ℝ ∞ F → F 0 = 0 →
      (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C) →
      ∀ (k : ℕ) (L : List (SpacesNemytskiiTerm T γ k)) (c s : ℕ),
      (∀ t ∈ L, t.order + c ≤ s) →
      ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalJetProjectiveLimit hT), spacesPhysicalGrading hT base u ≤ R →
      ∀ v : Fin k → PhysicalJetProjectiveLimit hT,
        MemLp (SpacesNemytskiiTerm.weightedEvaluateTerms hT L F c u v) 2 materialCylinderMeasure ∧
        lpNorm (SpacesNemytskiiTerm.weightedEvaluateTerms hT L F c u v) 2 materialCylinderMeasure ≤
          C * spacesNemytskiiMajorant hT base (s + loss) u v := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_term_tame hT hI
  refine ⟨base, loss, fun γ hγ F hF hF0 hFb k L c s hL R hR => ?_⟩
  induction L with
  | nil =>
    refine ⟨0, le_rfl, fun u _ v => ?_⟩
    rw [SpacesNemytskiiTerm.weightedEvaluateTerms_nil]
    exact ⟨MemLp.zero, by simp only [lpNorm_zero, zero_mul, le_refl]⟩
  | cons t L ih =>
    obtain ⟨C₁, hC₁, hb₁⟩ := hb γ hγ F hF hF0 hFb k t c s
      (hL t (List.mem_cons_self)) R hR
    obtain ⟨C₂, hC₂, hb₂⟩ := ih (fun τ hτ => hL τ (List.mem_cons_of_mem _ hτ))
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun u hu v => ?_⟩
    rw [SpacesNemytskiiTerm.weightedEvaluateTerms_cons]
    refine ⟨(hb₁ u hu v).1.add (hb₂ u hu v).1, ?_⟩
    calc
      lpNorm _ 2 materialCylinderMeasure ≤
          lpNorm (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure +
            lpNorm (SpacesNemytskiiTerm.weightedEvaluateTerms hT L F c u v) 2 materialCylinderMeasure :=
        lpNorm_add_le (hb₁ u hu v).1 (by norm_num)
      _ ≤ C₁ * spacesNemytskiiMajorant hT base (s + loss) u v +
          C₂ * spacesNemytskiiMajorant hT base (s + loss) u v :=
        add_le_add (hb₁ u hu v).2 (hb₂ u hu v).2
      _ = _ := (add_mul _ _ _).symm

end ContinuousFlexibility.Statements
