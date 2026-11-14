module

public import ContinuousFlexibility.Analysis.TameForwardJetSourceBounds

/-!
# Uniform fixed-base bounds for an abstract forward family

All existential constants and universal jet binders are handled before
instantiating a concrete realized family. The same low base and source
normalization are retained at every parameter order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

theorem inverseForwardJets_fixedBase_bound_of_kernel
    (p : ℕ → Seminorm ℝ E) (L : P → E → E →L[ℝ] E)
    (τ : P → E →L[ℝ] E)
    (K : (r k : ℕ) → E → E → (Fin k → E) → E)
    (hident : ∀ (travel : P) (U : Set E) (hU : IsOpen U)
      (J : Statements.SmoothDirections (U ×ˢ univ)
        (fun z : E × E => L travel z.1 z.2)) (n : ℕ),
      ∀ x ∈ U, ∀ (v : Fin n → E) (y : E),
        inverseForwardJet J n x v y = K n n x (τ travel y) v)
    (htranslation : ∀ travel s u, p s (τ travel u) ≤ p s u)
    (hkernel : ∃ base loss : ℕ, ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, p base x ≤ R →
        ∀ (u : E) (v : Fin k → E),
          p s (K r k x u v) ≤ C * multilinearTameSize
            (p base) (p (r + s + loss)) (k + 1)
            (1 + p (r + s + loss) x) (Fin.cons u v)) :
    ∃ base loss : ℕ, ∀ (n : ℕ) (R : ℝ), 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (travel : P) (U : Set E) (hU : IsOpen U)
          (J : Statements.SmoothDirections (U ×ˢ univ)
            (fun z : E × E => L travel z.1 z.2)),
          ∀ x ∈ U, p base x ≤ R → ∀ v : Fin n → E,
            (∀ i, p base (v i) ≤ R) → ∀ y : E,
              p s (inverseForwardJet J n x v y) ≤ C *
                ((1 + p (s + (n + loss)) x +
                    ∑ i, p (s + (n + loss)) (v i)) * p base y +
                  p (s + (n + loss)) y) := by
  classical
  obtain ⟨base, loss, hbound⟩ := hkernel
  refine ⟨base, loss, fun n R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hbound n n s R hR
  have horder : n + s + loss = s + (n + loss) := by omega
  rw [horder] at hc
  let H : ℕ := s + (n + loss)
  have hP : 0 ≤ R ^ (n + 1) := pow_nonneg (zero_le_one.trans hR) _
  refine ⟨C * R ^ (n + 1), mul_nonneg hC hP,
    fun travel U hU J x hx hxR v hv y => ?_⟩
  let A : E →L[ℝ] E := inverseForwardJetLinear J n x v
  have hA (u : E) : A u = inverseForwardJet J n x v u :=
    inverseForwardJetLinear_apply J n x v u
  have hsource (u : E) :
      p s (A u) ≤ C * multilinearTameSize
        (p base) (p H) (n + 1) (1 + p H x)
          (Fin.cons (τ travel u) v) := by
    rw [hA u, hident travel U hU J n x hx v u]
    exact hc x hxR (τ travel u) v
  have h := linearMap_oneHigh_of_shiftedSourceKernel A (p s)
    (p base) (p H) x v (τ travel) hC hR hv
    (htranslation travel base) (htranslation travel H) hsource y
  simpa only [hA] using h

end ContinuousFlexibility.Analysis
