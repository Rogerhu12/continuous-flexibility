import ContinuousFlexibility.Analysis.SmoothDirectionsBoundedLimit
import ContinuousFlexibility.Analysis.SmoothDirectionsConstantShift

/-!
# Uniform parameter towers after restoring the reference value

A uniformly bounded reference family contributes only at parameter order
zero. Every positive jet is the jet of the actual increment, so one
continuous seminorm still controls the full family at each fixed order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04Realization_uniformSeminormBounds_of_constantShift
    {ι : Type*} {U : Set E} {f g : ι → E → ℝ}
    (J : ∀ i, SmoothDirections U (f i))
    (K : ∀ i, SmoothDirections U (g i)) (c : ι → ℝ)
    (heq : ∀ i x, x ∈ U → f i x = g i x + c i)
    (hK : UniformScalarJetSeminormBounds K)
    {B : ℝ} (hB : 0 ≤ B) (hc : ∀ i, |c i| ≤ B) :
    UniformScalarJetSeminormBounds J := by
  intro n
  cases n with
  | zero =>
      obtain ⟨p, A, hp, hA, hb⟩ := hK 0
      refine ⟨p, A + B, hp, add_nonneg hA hB, ?_⟩
      intro i x hx v
      have hv : v = (Fin.elim0 : Fin 0 → E) := Subsingleton.elim _ _
      have hj : (J i).D 0 x v = f i x :=
        (congrArg (fun w => (J i).D 0 x w) hv).trans ((J i).zero x hx)
      have hk : (K i).D 0 x v = g i x :=
        (congrArg (fun w => (K i).D 0 x w) hv).trans ((K i).zero x hx)
      have hg : |g i x| ≤ A * (1 + p x) := by
        simpa only [hk, Fin.prod_univ_zero, mul_one] using hb i x hx v
      have hw : 1 ≤ 1 + p x := le_add_of_nonneg_right (apply_nonneg p x)
      calc
        |(J i).D 0 x v| = |g i x + c i| := congrArg abs (hj.trans (heq i x hx))
        _ ≤ |g i x| + |c i| := abs_add_le _ _
        _ ≤ A * (1 + p x) + B * (1 + p x) :=
          add_le_add hg ((hc i).trans (le_mul_of_one_le_right hB hw))
        _ = (A + B) * (1 + p x) * ∏ j : Fin 0, p (v j) := by
          simp only [Fin.prod_univ_zero, mul_one, add_mul]
  | succ n =>
      obtain ⟨p, A, hp, hA, hb⟩ := hK (n + 1)
      refine ⟨p, A, hp, hA, ?_⟩
      intro i x hx v
      exact (congrArg abs ((J i).positive_jet_eq_of_constant_shift
        (K i) (c i) (heq i) n x hx v)).trans_le (hb i x hx v)

end ContinuousFlexibility.Analysis
