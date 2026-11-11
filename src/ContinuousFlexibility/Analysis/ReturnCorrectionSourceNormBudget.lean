import ContinuousFlexibility.Analysis.ReturnCorrectionSourceJets
import ContinuousFlexibility.Analysis.ReturnDivergenceMembership

/-!
# The exact spatial-order budget of each source parameter jet

The source fiber formula is a finite sum of actual divergences. Applying
the physical multiplier estimate to each summand keeps coefficient order
k paired with height order s+4-k+d. All constants are chosen before the
coefficient fields, parameter point, directions, and height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem exists_symmetricSourceScalarJets_norm_budget
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : (∀ k : ℕ, E → MultilinearMap ℝ (fun _ : Fin k => E)
        (annularSmoothCoefficientSpace D)),
      ∀ z : E × HeightPair S, ∀ v : Fin (n + 1) → E × HeightPair S,
      ∀ K : ℕ → ℝ, ∀ K' : Fin (n + 1) → ℕ → ℝ,
      (∀ k, 0 ≤ K k) → (∀ i k, 0 ≤ K' i k) →
      (∀ a b p,
        |mixedDerivative a b (fun q =>
          ((A (n + 1) z.1 (fun i => (v i).1)).val (T.radius q.1, q.2)).1) p| ≤
            K (a + b) * T.M (T.radius p.1) ^ d ∧
        |mixedDerivative a b (fun q =>
          ((A (n + 1) z.1 (fun i => (v i).1)).val (T.radius q.1, q.2)).2) p| ≤
            K (a + b) * T.M (T.radius p.1) ^ d) →
      (∀ i a b p,
        |mixedDerivative a b (fun q =>
          ((A n z.1 (fun j => (v (i.succAbove j)).1)).val (T.radius q.1, q.2)).1) p| ≤
            K' i (a + b) * T.M (T.radius p.1) ^ d ∧
        |mixedDerivative a b (fun q =>
          ((A n z.1 (fun j => (v (i.succAbove j)).1)).val (T.radius q.1, q.2)).2) p| ≤
            K' i (a + b) * T.M (T.radius p.1) ^ d) →
      physicalNorm T (3 / 4 : ℝ) s (symmetricSourceScalarJets hS hT A (n + 1) z v) ≤
        C * ((∑ k ∈ Finset.range (s + 3), K k *
            physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d)
              ((S.height (3 / 4 : ℝ)).decode z.2.1)) +
          ∑ i : Fin (n + 1), ∑ k ∈ Finset.range (s + 3), K' i k *
            physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d)
              ((S.height (3 / 4 : ℝ)).decode (v i).2.1)) := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_physicalNorm_symmetricDivergenceBilinear_bound hS hT s d
  let H : ℝ := Real.sqrt (Fintype.card (JetIndex s) : ℝ)
  refine ⟨H * C, mul_nonneg (Real.sqrt_nonneg _) hC, ?_⟩
  intro A z v K K' hK hK' htop hlower
  let F : PolarPoint → ℝ := symmetricDivergenceBilinear hS hT
    (A (n + 1) z.1 (fun i => (v i).1)) z.2
  let G (i : Fin (n + 1)) : PolarPoint → ℝ := symmetricDivergenceBilinear hS hT
    (A n z.1 (fun j => (v (i.succAbove j)).1)) (v i).2
  let terms : Fin (n + 2) → PolarPoint → ℝ := Fin.cons F G
  let N : ℝ := ∑ k ∈ Finset.range (s + 3), K k *
    physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d) ((S.height (3 / 4 : ℝ)).decode z.2.1)
  let N' (i : Fin (n + 1)) : ℝ := ∑ k ∈ Finset.range (s + 3), K' i k *
    physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d) ((S.height (3 / 4 : ℝ)).decode (v i).2.1)
  have hF : ContDiffOn ℝ ∞ F (annularOpen D) :=
    symmetricDivergenceBilinear_contDiffOn hS hT _ _
  have hG (i : Fin (n + 1)) : ContDiffOn ℝ ∞ (G i) (annularOpen D) :=
    symmetricDivergenceBilinear_contDiffOn hS hT _ _
  have hFLp (a b c : ℕ) : MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c F)
      2 materialCylinderMeasure :=
    symmetricDivergenceBilinear_memLp hS hT _ d
      (fun a b => ⟨K (a + b), hK _, htop a b⟩) z.2 a b c
  have hGLp (i : Fin (n + 1)) (a b c : ℕ) :
      MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c (G i)) 2 materialCylinderMeasure :=
    symmetricDivergenceBilinear_memLp hS hT _ d
      (fun a b => ⟨K' i (a + b), hK' i _, hlower i a b⟩) (v i).2 a b c
  have hterms (i : Fin (n + 2)) : ContDiffOn ℝ ∞ (terms i) (annularOpen D) := by
    cases i using Fin.cases with
    | zero => exact hF
    | succ i => exact hG i
  have htermsLp (i : Fin (n + 2)) (a b c : ℕ) :
      MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c (terms i)) 2 materialCylinderMeasure := by
    cases i using Fin.cases with
    | zero => exact hFLp a b c
    | succ i => exact hGLp i a b c
  have hFn : physicalNorm T (3 / 4 : ℝ) s F ≤ C * N :=
    hb _ K hK htop z.2
  have hGn (i : Fin (n + 1)) : physicalNorm T (3 / 4 : ℝ) s (G i) ≤ C * N' i :=
    hb _ (K' i) (hK' i) (hlower i) (v i).2
  have heq : symmetricSourceScalarJets hS hT A (n + 1) z v =
      fun p => ∑ i : Fin (n + 2), terms i p := by
    funext p
    have h := congrFun (symmetricSourceScalarJets_eq_sum hS hT A n z v) p
    simpa only [Fin.sum_univ_succ, terms, Fin.cons_zero, Fin.cons_succ,
      Pi.add_apply, Finset.sum_apply, F, G] using h
  have hn := physicalNorm_finset_sum_le hT Finset.univ terms
    (fun i _ => hterms i) (fun i _ => htermsLp i) s
  have hs : (∑ i : Fin (n + 2), physicalNorm T (3 / 4 : ℝ) s (terms i)) ≤
      C * (N + ∑ i : Fin (n + 1), N' i) := by
    rw [Fin.sum_univ_succ]
    change physicalNorm T (3 / 4 : ℝ) s F +
      ∑ i : Fin (n + 1), physicalNorm T (3 / 4 : ℝ) s (G i) ≤ _
    exact (add_le_add hFn (Finset.sum_le_sum (fun i _ => hGn i))).trans_eq
      ((congrArg (fun y : ℝ => C * N + y)
        (Finset.mul_sum Finset.univ N' C).symm).trans (mul_add C N _).symm)
  rw [heq]
  exact hn.trans ((mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)).trans_eq
    (mul_assoc H C _).symm)

end ContinuousFlexibility.Statements
