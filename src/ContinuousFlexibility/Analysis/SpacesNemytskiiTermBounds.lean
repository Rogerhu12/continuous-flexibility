module

public import ContinuousFlexibility.Analysis.SpacesNemytskiiTerms
public import ContinuousFlexibility.Analysis.SpacesNemytskiiProducts

/-!
# Fixed-loss bounds for composition terms

Every term with at least one height factor has a bounded radial coefficient
when the height exponent is positive. Its weighted L² norm is therefore
controlled by the finite-product interpolation estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SpacesNemytskiiTerm

variable {T : MaterialData} {γ : ℝ} {k : ℕ}

def factorOrder (t : SpacesNemytskiiTerm T γ k) : Fin t.baseFactors ⊕ Fin k → ℕ × ℕ :=
  Sum.elim t.baseOrder t.directionOrder

def factorFamily {E : Type*} (t : SpacesNemytskiiTerm T γ k) (u : E) (v : Fin k → E) :
    Fin t.baseFactors ⊕ Fin k → E := Sum.elim (fun _ => u) v

theorem factorOrder_sum (t : SpacesNemytskiiTerm T γ k) :
    (∑ i, ((t.factorOrder i).1 + (t.factorOrder i).2)) = t.order := by
  simp only [factorOrder, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, order]

def weightedEvaluate {D : ReferenceData} (hT : IsMaterialData D T)
    (t : SpacesNemytskiiTerm T γ k) (F : ℝ → ℝ) (c : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ c *
    t.evaluate F (spacesPhysicalRepresentative hT u) (fun i => spacesPhysicalRepresentative hT (v i)) p

end SpacesNemytskiiTerm

/-- One base and one loss work for every term and every number of direction
factors. Only the estimate's constant depends on the individual term. -/
theorem spaces_nemytskii_term_one_high {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base loss : ℕ, ∀ (γ : ℝ), 0 < γ → ∀ (F : ℝ → ℝ), ContDiff ℝ ∞ F →
      (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C) →
      ∀ (k : ℕ) (t : SpacesNemytskiiTerm T γ k), 0 < k + t.baseFactors →
      ∀ c s : ℕ, t.order + c ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT),
        MemLp (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure ∧
        lpNorm (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure ≤
          C * ∑ i, spacesPhysicalGrading hT (s + loss) (t.factorFamily u v i) *
            ∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT base (t.factorFamily u v j) := by
  obtain ⟨base, loss, hprod⟩ := spaces_weighted_jet_product_one_high hT hI
  refine ⟨base, loss, fun γ hγ F hF hFb k t hcount c s horder => ?_⟩
  have hα : 0 ≤ (((k + t.baseFactors : ℕ) : ℝ) - 1) * γ := by
    have hn : (1 : ℝ) ≤ ((k + t.baseFactors : ℕ) : ℝ) := by exact_mod_cast hcount
    exact mul_nonneg (sub_nonneg.mpr hn) hγ.le
  obtain ⟨A, hA, hAbound⟩ := t.coefficient_mem.bounded_of_nonneg hT hα
  obtain ⟨B, hB, hBbound⟩ := hFb (k + t.baseFactors)
  let : Nonempty (Fin t.baseFactors ⊕ Fin k) := by
    by_cases hq : 0 < t.baseFactors
    · exact ⟨Sum.inl ⟨0, hq⟩⟩
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  let a (i : Fin t.baseFactors ⊕ Fin k) := (t.factorOrder i).1
  let b (i : Fin t.baseFactors ⊕ Fin k) := (t.factorOrder i).2
  have hbudget : (∑ i, (a i + b i)) + c ≤ s := by
    simpa only [a, b, t.factorOrder_sum] using horder
  obtain ⟨C, hC, hbound⟩ := hprod a b c s hbudget
  refine ⟨(A * B) * C, mul_nonneg (mul_nonneg hA hB) hC, fun u v => ?_⟩
  let x := t.factorFamily u v
  let g (p : PolarPoint) := t.coefficient p.1 *
    iteratedDeriv (k + t.baseFactors) F (T.H (T.radius p.1) ^ γ * spacesPhysicalRepresentative hT u p)
  have hg : Continuous g :=
    (t.coefficient_mem.contDiff.continuous.comp continuous_fst).mul
      ((spaces_scalar_contDiff_iteratedDeriv hF _).continuous.comp
        (((spacesRadialMultiplier_materialH hT γ).contDiff.continuous.comp continuous_fst).mul
          (spacesPhysicalRepresentative_contDiff hT u).continuous))
  have hgb (p : PolarPoint) : |g p| ≤ A * B := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hAbound p.1) (hBbound _) (abs_nonneg _) hA)
  have he : t.weightedEvaluate hT F c u v =
      fun p => spacesWeightedJetProduct hT a b c x p * g p := by
    funext p
    simp only [SpacesNemytskiiTerm.weightedEvaluate, SpacesNemytskiiTerm.evaluate,
      spacesWeightedJetProduct, a, b, x, SpacesNemytskiiTerm.factorOrder,
      SpacesNemytskiiTerm.factorFamily, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, g]
    ring
  rw [he]
  have hp := hbound x
  refine ⟨spaces_memLp_mul_bounded hp.1 hg.aestronglyMeasurable hgb, ?_⟩
  calc
    lpNorm (fun p => spacesWeightedJetProduct hT a b c x p * g p) 2 materialCylinderMeasure ≤
        (A * B) * lpNorm (spacesWeightedJetProduct hT a b c x) 2 materialCylinderMeasure :=
      spaces_lpNorm_mul_bounded hp.1 hg.aestronglyMeasurable (mul_nonneg hA hB) hgb
    _ ≤ (A * B) * (C * ∑ i, spacesPhysicalGrading hT (s + loss) (x i) *
        ∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT base (x j)) :=
      mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hB)
    _ = _ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Statements
