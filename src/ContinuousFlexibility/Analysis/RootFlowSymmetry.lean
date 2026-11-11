import ContinuousFlexibility.Analysis.RootRegularizedFlow
import Mathlib.Tactic.Ring

/-!
# Reflection of the actual root-regularized flow

Oddness of d and evenness of c₀ in the angular variable give the exact
simultaneous reflection (ζ, θ) ↦ (-ζ, -θ) of the displayed root field.
Uniqueness transfers this symmetry to every actual solution family.
The angular Lipschitz bound needed for uniqueness is derived from the
actual derivative of the smooth periodic field on one compact period.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff NNReal Topology

private theorem exists_uniform_angle_lipschitz
    {F : ℝ × ℝ → ℝ} {a b T : ℝ}
    (hF : ContDiff ℝ ∞ F) (hT : T ≠ 0)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => F (t, θ)) T) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b,
      LipschitzWith K (fun θ => F (t, θ)) := by
  have hD : Continuous (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).continuous
  obtain ⟨M, hM0, hM⟩ := exists_norm_bound_periodic_compact
    isCompact_Icc hT hD.continuousOn
    (fun t _ => fderiv_periodic_snd hperiod t)
  refine ⟨NNReal.mk M hM0, ?_⟩
  intro t ht
  apply LipschitzWith.of_dist_le_mul
  intro θ φ
  have hh : dist (F (t, θ)) (F (t, φ)) ≤ M * dist (t, θ) (t, φ) := by
    simpa only [dist_eq_norm] using
      ((convex_Icc a b).prod (convex_univ : Convex ℝ (univ : Set ℝ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z _ => ((hF.differentiable (by simp)) z).hasFDerivAt.hasFDerivWithinAt)
        (fun z hz => hM z.1 hz.1 z.2)
        (show (t, φ) ∈ Icc a b ×ˢ univ from ⟨ht, mem_univ _⟩)
        (show (t, θ) ∈ Icc a b ×ˢ univ from ⟨ht, mem_univ _⟩)
  simpa only [NNReal.coe_mk, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hh

/-- The actual root field changes sign under simultaneous reflection of
the independent root parameter and current angle. -/
theorem rootRegularizedField_reflect
    {d c₀ : ℝ × ℝ → ℝ}
    (hdodd : ∀ r θ : ℝ, d (r, -θ) = -d (r, θ))
    (hc₀even : ∀ r θ : ℝ, c₀ (r, -θ) = c₀ (r, θ))
    (t x ζ θ : ℝ) :
    rootRegularizedField d c₀ (t, ((x, -ζ), -θ)) =
      -rootRegularizedField d c₀ (t, ((x, ζ), θ)) := by
  simp only [rootRegularizedField, hdodd, hc₀even]
  ring

/-- At zero radial and root parameters the actual field vanishes, so
every trajectory is its prescribed initial angle throughout [0,1]. -/
theorem rootRegularizedFlow_zero_parameters
    {d c₀ : ℝ × ℝ → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ p r θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t)
    (θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Θ (0, 0) t θ = θ := by
  apply eqOn_scalarFlow_of_same_initial
    (F := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
    (u := fun r => Θ (0, 0) r θ) (v := fun _ => θ)
    (fun _ _ => LipschitzWith.const (0 : ℝ)) _ _
    (hinit (0, 0) θ) ht
  · intro r hr
    simpa only [mul_zero, zero_mul, zero_add] using hflow (0, 0) θ r hr
  · intro r _
    exact (hasDerivAt_const r θ).hasDerivWithinAt

/-- Every actual root-flow family has the field's reflection symmetry.
The initial condition and time ODE are the only assumptions on the
family itself. -/
theorem rootRegularizedFlow_reflect
    {d c₀ : ℝ × ℝ → ℝ} {T : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r : ℝ, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r : ℝ, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hdodd : ∀ r θ : ℝ, d (r, -θ) = -d (r, θ))
    (hc₀even : ∀ r θ : ℝ, c₀ (r, -θ) = c₀ (r, θ))
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ p r θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t)
    (x ζ θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Θ (x, -ζ) t (-θ) = -Θ (x, ζ) t θ := by
  have hpmap : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => (q.1, ((x, -ζ), q.2))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hminus : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => rootRegularizedField d c₀ (q.1, ((x, -ζ), q.2))) :=
    (contDiff_rootRegularizedField hd hc₀).comp hpmap
  obtain ⟨K, hK⟩ := exists_uniform_angle_lipschitz
    (a := 0) (b := 1) hminus hT
    (fun r => rootRegularizedField_periodic hdperiod hc₀period r (x, -ζ))
  apply eqOn_scalarFlow_of_same_initial
    (u := fun r => Θ (x, -ζ) r (-θ)) (v := fun r => -Θ (x, ζ) r θ)
    hK (fun r hr => hflow (x, -ζ) (-θ) r hr) _ _ ht
  · intro r hr
    have hu : HasDerivWithinAt (fun s => Θ (x, ζ) s θ)
        (rootRegularizedField d c₀ (r, ((x, ζ), Θ (x, ζ) r θ)))
        (Icc (0 : ℝ) 1) r :=
      hflow (x, ζ) θ r hr
    simpa only [rootRegularizedField_reflect hdodd hc₀even] using hu.fun_neg
  · rw [hinit, hinit]

end ContinuousFlexibility.Analysis
