module

public import ContinuousFlexibility.Analysis.SymmetricMultilinearDiagonalBounds
public import ContinuousFlexibility.Analysis.MixedParameterSymmetry
public import ContinuousFlexibility.Analysis.JointMixedDiagonalCalculus
public import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# From actual diagonal mixed estimates to unrestricted one-high bounds

The genuine mixed spatial derivative is multilinear and symmetric in
its parameter slots. Polarization gives its estimate on the low unit
polydisc. Homogeneous normalization then restores arbitrary directions,
including directions in the kernel of the low seminorm. The one
constant is chosen before the spatial orders and all evaluation data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem exists_jointMixedDiagonal_oneHigh_constant (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}
        (J : SmoothDirections (U ×ˢ V) f), IsOpen V → Convex ℝ (U ×ˢ V) →
      ∀ (p : ℕ → Seminorm ℝ E) (base high : ℕ)
        (x : E), x ∈ U → ∀ y ∈ V, ∀ a b : ℕ, ∀ C : ℝ, 0 ≤ C →
        (∀ w : E, p base w ≤ 1 →
          |jointMixedDiagonal J n a b x w y| ≤ C * (1 + p high x + p high w)) →
      ∀ v : Fin n → E,
        |mixedDerivative a b (fun q => J.D n (x, q) (fun i => (v i, (0 : PolarPoint)))) y| ≤
          K * C * oneHighVariationWeight p base high x v := by
  obtain ⟨K, hK, hpolar⟩ := exists_symmetric_multilinear_diagonal_affine_bound n
  refine ⟨K, hK, ?_⟩
  intro U V f J hV hc p base high x hx y hy a b C hC hdiag v
  let A := J.mixedParameterMultilinearMap hV n a b x hx y hy
  have hsym (u : Fin n → E) (σ : Equiv.Perm (Fin n)) : A (u ∘ σ) = A u :=
    J.mixedParameterMultilinearMap_comp_perm hV hc n a b x hx y hy u σ
  have hAdiag (w : E) (hw : p base w ≤ 1) :
      |A (fun _ => w)| ≤ C * (1 + p high x + p high w) := hdiag w hw
  have hunit (u : Fin n → E) (hu : ∀ i, p base (u i) < 1) :
      (normSeminorm ℝ ℝ) (A u) ≤
        (K * C) * ((1 + p high x) + ∑ i, p high (u i)) := by
    simpa only [coe_normSeminorm, Real.norm_eq_abs] using
      hpolar E (p base) (p high) A hsym x C hC hAdiag u (fun i => (hu i).le)
  have hb := multilinearMap_bound_of_unitBall A (normSeminorm ℝ ℝ)
    (p base) (p high) (mul_nonneg hK hC) hunit v
  simpa only [A, SmoothDirections.mixedParameterMultilinearMap_apply,
    coe_normSeminorm, Real.norm_eq_abs, multilinearTameSize,
    oneHighVariationWeight] using hb

end ContinuousFlexibility.Analysis
