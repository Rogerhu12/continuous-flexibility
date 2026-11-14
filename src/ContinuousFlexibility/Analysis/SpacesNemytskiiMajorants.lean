module

public import ContinuousFlexibility.Analysis.SpacesNemytskiiKernels

/-!
# Integrable bounds on affine parameter intervals

A positive-order kernel always has a direction factor. Keep one such
factor in L² and bound every remaining factor pointwise. This gives an
actual common L² majorant for every weighted spatial jet along a bounded
affine parameter interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

theorem spaces_nemytskii_affine_jet_pointwise (a b : ℕ)
    (u w : PhysicalJetProjectiveLimit hT) {R : ℝ} (_hR : 0 ≤ R) {t : ℝ} (ht : |t| ≤ R)
    (p : PolarPoint) :
    |mixedDerivative a b (spacesPhysicalRepresentative hT (u + t • w)) p| ≤
      (4 * Real.sqrt Real.pi) * (spacesPhysicalGrading hT (a + b + 2) u +
        R * spacesPhysicalGrading hT (a + b + 2) w) := by
  apply (spacesNormalizedMixed_pointwise hT a b (u + t • w) p).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (map_add_le_add _ _ _).trans
  rw [map_smul_eq_mul, Real.norm_eq_abs]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht
    (apply_nonneg (spacesPhysicalGrading hT (a + b + 2)) w))

theorem spaces_nemytskii_term_affine_majorant {γ : ℝ} (hγ : 0 < γ)
    {F : ℝ → ℝ} (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (τ : SpacesNemytskiiTerm T γ (k + 1)) (c : ℕ)
    (u w : PhysicalJetProjectiveLimit hT) (v : Fin (k + 1) → PhysicalJetProjectiveLimit hT)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ g : PolarPoint → ℝ, MemLp g 2 materialCylinderMeasure ∧
      ∀ t : ℝ, |t| ≤ R → ∀ p,
        |τ.weightedEvaluate hT F c (u + t • w) v p| ≤ g p := by
  have hα : 0 ≤ ((((k + 1 + τ.baseFactors : ℕ) : ℝ) - 1) * γ) := by
    have hn : (1 : ℝ) ≤ ((k + 1 + τ.baseFactors : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1 + τ.baseFactors)
    exact mul_nonneg (sub_nonneg.mpr hn) hγ.le
  obtain ⟨A, hA, hAb⟩ := τ.coefficient_mem.bounded_of_nonneg hT hα
  obtain ⟨B, hB, hBb⟩ := hFb (k + 1 + τ.baseFactors)
  let U (i : Fin τ.baseFactors) := (4 * Real.sqrt Real.pi) *
    (spacesPhysicalGrading hT ((τ.baseOrder i).1 + (τ.baseOrder i).2 + 2) u +
      R * spacesPhysicalGrading hT ((τ.baseOrder i).1 + (τ.baseOrder i).2 + 2) w)
  let V (i : Fin k) := (4 * Real.sqrt Real.pi) *
    spacesPhysicalGrading hT ((τ.directionOrder i.succ).1 + (τ.directionOrder i.succ).2 + 2) (v i.succ)
  let C := (A * B) * (∏ i, U i) * ∏ i, V i
  have hU (i : Fin τ.baseFactors) : 0 ≤ U i := by dsimp only [U]; positivity
  have hV (i : Fin k) : 0 ≤ V i := by dsimp only [V]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let f := spacesNormalizedJet hT (τ.directionOrder 0).1 (τ.directionOrder 0).2 c (v 0)
  have hf : MemLp f 2 materialCylinderMeasure := spacesNormalizedJet_memLp hT _ _ c (v 0)
  refine ⟨fun p => C * |f p|, ?_, fun t ht p => ?_⟩
  · have hm := hf.norm.const_smul C
    change MemLp (fun p => C * ‖f p‖) 2 materialCylinderMeasure at hm
    simpa only [Real.norm_eq_abs] using hm
  · have hbase : (∏ i, |mixedDerivative (τ.baseOrder i).1 (τ.baseOrder i).2
          (spacesPhysicalRepresentative hT (u + t • w)) p|) ≤ ∏ i, U i := by
      apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      intro i _
      exact spaces_nemytskii_affine_jet_pointwise hT _ _ u w hR ht p
    have hdir : (∏ i : Fin k, |mixedDerivative (τ.directionOrder i.succ).1
          (τ.directionOrder i.succ).2 (spacesPhysicalRepresentative hT (v i.succ)) p|) ≤ ∏ i, V i := by
      apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      intro i _
      exact spacesNormalizedMixed_pointwise hT _ _ (v i.succ) p
    have hM : 0 ≤ T.M (T.radius p.1) ^ c :=
      pow_nonneg (zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2) c
    have he : |τ.weightedEvaluate hT F c (u + t • w) v p| =
        (|τ.coefficient p.1| * |iteratedDeriv (k + 1 + τ.baseFactors) F
          (T.H (T.radius p.1) ^ γ * spacesPhysicalRepresentative hT (u + t • w) p)|) *
        (∏ i, |mixedDerivative (τ.baseOrder i).1 (τ.baseOrder i).2
          (spacesPhysicalRepresentative hT (u + t • w)) p|) *
        (∏ i : Fin k, |mixedDerivative (τ.directionOrder i.succ).1
          (τ.directionOrder i.succ).2 (spacesPhysicalRepresentative hT (v i.succ)) p|) * |f p| := by
      simp only [SpacesNemytskiiTerm.weightedEvaluate, SpacesNemytskiiTerm.evaluate,
        abs_mul, Finset.abs_prod, Fin.prod_univ_succ, f, spacesNormalizedJet, abs_of_nonneg hM]
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply mul_le_mul _ hdir (Finset.prod_nonneg (fun i _ => abs_nonneg _))
      (mul_nonneg (mul_nonneg hA hB) (Finset.prod_nonneg (fun i _ => hU i)))
    exact mul_le_mul
      (mul_le_mul (hAb p.1) (hBb _) (abs_nonneg _) hA)
      hbase (Finset.prod_nonneg (fun i _ => abs_nonneg _)) (mul_nonneg hA hB)

theorem spaces_nemytskii_expansion_affine_majorant {γ : ℝ} (hγ : 0 < γ)
    {F : ℝ → ℝ} (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (L : List (SpacesNemytskiiTerm T γ (k + 1))) (c : ℕ)
    (u w : PhysicalJetProjectiveLimit hT) (v : Fin (k + 1) → PhysicalJetProjectiveLimit hT)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ g : PolarPoint → ℝ, MemLp g 2 materialCylinderMeasure ∧
      ∀ t : ℝ, |t| ≤ R → ∀ p,
        |SpacesNemytskiiTerm.weightedEvaluateTerms hT L F c (u + t • w) v p| ≤ g p := by
  induction L with
  | nil =>
    refine ⟨0, MemLp.zero, fun t _ p => ?_⟩
    rw [SpacesNemytskiiTerm.weightedEvaluateTerms_nil]
    exact (abs_zero).le
  | cons τ L ih =>
    obtain ⟨g₁, hg₁, hb₁⟩ := spaces_nemytskii_term_affine_majorant hT hγ hFb k τ c u w v hR
    obtain ⟨g₂, hg₂, hb₂⟩ := ih
    refine ⟨g₁ + g₂, hg₁.add hg₂, fun t ht p => ?_⟩
    rw [SpacesNemytskiiTerm.weightedEvaluateTerms_cons]
    exact (abs_add_le _ _).trans (add_le_add (hb₁ t ht p) (hb₂ t ht p))

theorem spaces_nemytskii_material_jet_affine_majorant {γ : ℝ} (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k a b c : ℕ) (u w : PhysicalJetProjectiveLimit hT)
    (v : Fin (k + 1) → PhysicalJetProjectiveLimit hT) {R : ℝ} (hR : 0 ≤ R) :
    ∃ g : PolarPoint → ℝ, MemLp g 2 materialCylinderMeasure ∧
      ∀ t : ℝ, |t| ≤ R → ∀ p,
        |T.M (T.radius p.1) ^ c * mixedDerivative a b
          (spacesNemytskiiMaterial hT γ F (k + 1) (u + t • w) v) p| ≤ g p := by
  obtain ⟨g, hg, hb⟩ := spaces_nemytskii_expansion_affine_majorant hT hγ hFb k
    (SpacesNemytskiiTerm.jetExpansion hT γ (k + 1) a b) c u w v hR
  refine ⟨g, hg, fun t ht p => ?_⟩
  have he := congrFun (spacesNemytskiiMaterial_weightedJet hT γ hF (k + 1) a b c (u + t • w) v) p
  rw [he]
  exact hb t ht p

end ContinuousFlexibility.Statements
