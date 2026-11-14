module

public import ContinuousFlexibility.Radial.DeepTailJacobiData
public import ContinuousFlexibility.Radial.DeepTailPoissonFamilies
public import ContinuousFlexibility.Radial.TailNaturalNodeContinuity

/-!
# Continuous actual Jacobi coefficients

The flux coefficients involve only the fixed physical edges and the
density.  No continuity of the auxiliary mass-interval split is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

theorem continuous_tailPoissonJacobiDiagonal {P : Type*} [TopologicalSpace P]
    {p : P → ℝ → ℝ} {node : ℕ → ℝ} {Λ η : P → ℝ}
    {hn : ∀ n, node n ≤ node (n + 1)}
    (B : ∀ σ n, TailPhysicalPoissonData (p σ) (node n) (node (n + 1)) (Λ σ) (η σ) (hn n))
    (b₀ : P → ℝ) (hb₀ : Continuous b₀)
    (hl : ∀ n, Continuous (fun σ => (B σ n).leftDiagonal))
    (hr : ∀ n, Continuous (fun σ => (B σ n).rightDiagonal)) (n : ℕ) :
    Continuous (fun σ => tailPoissonJacobiDiagonal (B σ) (b₀ σ) n) := by
  cases n with
  | zero => exact hb₀
  | succ n => exact (hr n).neg.sub (hl (n + 1))

/-- Replace the common geometric fields by their values at one fixed
parameter. The resulting family has definitionally fixed edge spaces. -/
def deepTailFixedGeometryFamily {P : Type*} (family : P → DeepTailData) (σ₀ σ : P) :
    DeepTailData where
  entrance := (family σ₀).entrance
  endpoint := (family σ₀).endpoint
  p := (family σ).p
  node := (family σ₀).node
  massEnd := (family σ).massEnd
  Λ := (family σ₀).Λ
  η := (family σ₀).η
  K := (family σ₀).K

theorem deepTailFixedGeometryFamily_eq {P : Type*} (family : P → DeepTailData) (σ₀ : P)
    (hgeom : ∀ σ, (family σ).entrance = (family σ₀).entrance ∧
      (family σ).endpoint = (family σ₀).endpoint ∧
      (family σ).node = (family σ₀).node ∧ (family σ).Λ = (family σ₀).Λ ∧
      (family σ).η = (family σ₀).η ∧ (family σ).K = (family σ₀).K) (σ : P) :
    deepTailFixedGeometryFamily family σ₀ σ = family σ := by
  have h := hgeom σ
  rcases h with ⟨ha, he, hn, hΛ, hη, hK⟩
  unfold deepTailFixedGeometryFamily
  rw [← ha, ← he, ← hn, ← hΛ, ← hη, ← hK]

end ContinuousFlexibility.Radial
