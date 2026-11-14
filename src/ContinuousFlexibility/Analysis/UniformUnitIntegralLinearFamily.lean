module

public import ContinuousFlexibility.Analysis.TameUnitIntegralLinearFamily

/-!
# Uniform jet bounds under unit-interval averaging

If every genuine parameter jet has one fixed low order and loss on
arbitrary bounded low-seminorm sets, a contracting family of linear
pullbacks and its integral preserve those very same orders. The
constants are chosen before the point and all directional arguments.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
  {bond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ E} {f : E → ProjectiveLimit F bond}

theorem uniformOneHigh_unitIntegralLinearFamily
    (J : SmoothDirections univ f)
    (hJ : ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ K → ∀ v : Fin n → E,
        gradedSeminorm F bond s (J.D n x v) ≤ C * tameJetSize p n s loss base x v)
    (L : ℝ → E →L[ℝ] E)
    (hL : Continuous (fun z : ℝ × E => L z.1 z.2))
    (hcontract : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s x, p s (L a x) ≤ p s x) :
    ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ K → ∀ v : Fin n → E,
        gradedSeminorm F bond s
            ((smoothDirectionsUnitIntegralLinearFamily J L hL).D n x v) ≤
          C * tameJetSize p n s loss base x v := by
  intro n
  obtain ⟨base, loss, hb⟩ := hJ n
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb K hK s
  refine ⟨C, hC, fun x hx v => ?_⟩
  rw [smoothDirectionsUnitIntegralLinearFamily_jet]
  apply projectiveUnitIntegral_grading_le _ s
    (mul_nonneg hC (tameJetSize_nonneg p n s loss base x v))
  intro a ha
  have hbase : p base (L a x) ≤ K := (hcontract a ha base x).trans hx
  have hsize := tameJetSize_linear_contraction p (L a).toLinearMap
    (hcontract a ha) n s loss base x v
  exact (hc (L a x) hbase (fun i => L a (v i))).trans
    (mul_le_mul_of_nonneg_left hsize hC)

end ContinuousFlexibility.Analysis
