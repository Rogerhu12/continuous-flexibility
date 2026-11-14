module

public import ContinuousFlexibility.Analysis.PeriodicFieldLipschitz
public import ContinuousFlexibility.Analysis.ScalarFlowParameterContinuity

/-!
# Joint continuity of actual periodic scalar flows

The field's actual derivative is bounded on a compact parameter set and
one angular period.  This derives the joint Lipschitz input for Gronwall.
The initial angle is then treated as an additional, constant parameter;
the field ignores this coordinate and the initial-value map is its
second projection.  Thus the selected solutions are jointly continuous
for every initial angle, with no continuity assumption on their choice.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped NNReal Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Compact parameter geometry and actual C1 periodic field data imply
joint continuity of any actual family of solutions with the prescribed
initial angle.  The domain coordinates are (parameter, initial angle)
followed by time. -/
theorem continuousOn_periodicScalarFlow_parameters
    {S : Set P} {F : ℝ → P × ℝ → ℝ} {Θ : P → ℝ → ℝ → ℝ}
    {a b T : ℝ}
    (hS : IsCompact S) (hconv : Convex ℝ S) (hT : T ≠ 0)
    (hF : ∀ t ∈ Icc a b, ∀ x ∈ S ×ˢ univ, DifferentiableAt ℝ (F t) x)
    (hD : ContinuousOn
      (fun x : (ℝ × P) × ℝ => fderiv ℝ (F x.1.1) (x.1.2, x.2))
      ((Icc a b ×ˢ S) ×ˢ univ))
    (hperiod : ∀ t ∈ Icc a b, ∀ p : P,
      Function.Periodic (fun θ => F t (p, θ)) T)
    (hinit : ∀ p ∈ S, ∀ θ : ℝ, Θ p a θ = θ)
    (hflow : ∀ p ∈ S, ∀ θ : ℝ, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun r => Θ p r θ)
        (F t (p, Θ p t θ)) (Icc a b) t) :
    ContinuousOn (fun x : (P × ℝ) × ℝ => Θ x.1.1 x.2 x.1.2)
      ((S ×ˢ univ) ×ˢ Icc a b) := by
  obtain ⟨K, hK⟩ := exists_uniform_lipschitzOnWith_periodic_fderiv
    isCompact_Icc hS hconv hT hF hD
    (fun t ht p _ => fderiv_periodic_snd (hperiod t ht) p)
  have hLift : ∀ t ∈ Ico a b,
      LipschitzOnWith K
        (fun x : (P × ℝ) × ℝ => F t (x.1.1, x.2))
        ((S ×ˢ univ) ×ˢ univ) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hproject : dist (x.1.1, x.2) (y.1.1, y.2) ≤ dist x y := by
      simp only [Prod.dist_eq]
      exact max_le_max (le_max_left _ _) le_rfl
    exact ((hK t ⟨ht.1, ht.2.le⟩).dist_le_mul
      (x.1.1, x.2) ⟨hx.1.1, mem_univ _⟩
      (y.1.1, y.2) ⟨hy.1.1, mem_univ _⟩).trans
        (mul_le_mul_of_nonneg_left hproject K.2)
  have hInitial : LipschitzOnWith 1 (fun q : P × ℝ => q.2) (S ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    simpa only [NNReal.coe_one, one_mul, Prod.dist_eq] using
      (le_max_right (dist x.1 y.1) (dist x.2 y.2))
  exact continuousOn_scalarFlow_parameters_time
    (F := fun (q : P × ℝ) t θ => F t (q.1, θ))
    (u := fun (q : P × ℝ) t => Θ q.1 t q.2)
    (v := fun q : P × ℝ => q.2)
    hLift (fun q hq t ht => hflow q.1 hq.1 q.2 t ht)
    (fun q hq => hinit q.1 hq.1 q.2) hInitial

end ContinuousFlexibility.Analysis
