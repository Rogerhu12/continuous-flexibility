import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04RealizationMixedSlotBudget
import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization

/-!
# Normalize the actual joint bound only after the spatial budget is closed

The parameter arity is kept equal to the requested order while radial
and angular basis vectors are appended. Thus every term retains the
same positive-parameter height factor. The resulting actual mixed
multilinear map is normalized once, using its proved sublinear power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}

/-- A finite joint prefix, on the same domain and at the actual point,
gives the complete one-high bound for the true mixed parameter jet. -/
theorem n04PositiveGeometry_mixed_oneHigh_of_jointUnitPower
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (center : E)
    (k a b : ℕ) (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    {M exponent : ℝ} (hM : 0 ≤ M) (hexponent : exponent ≤ 1)
    (hraw : ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
      ∀ n : ℕ, n ≤ k + a + b → ∀ w : StateAngleWord n, w.stateArity = k →
      ∀ u : Fin n → E × PolarPoint,
      (∀ i, p base (u i).1 ≤ 1) → (∀ i, p high (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
      |J.D n (x, q) u| ≤ M * R ^ exponent)
    (Q : SmoothDirections U (fun z => mixedDerivative a b (fun y => f (z, y)) q)) :
    ∀ v : Fin k → E,
      |Q.D k x v| ≤ M * oneHighVariationWeight p base high (x - center) v := by
  have hb : ∀ v : Fin k → E, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
      (∀ i, p high (v i) ≤ R) → |Q.D k x v| ≤ M * R ^ exponent := by
    intro v hv R hR hxR hvR
    let P : ∀ n : ℕ, (Fin n → E × PolarPoint) → Prop := fun n u =>
      ∃ w : StateAngleWord n, w.stateArity = k ∧
        (∀ i, p base (u i).1 ≤ 1) ∧ (∀ i, p high (u i).1 ≤ R) ∧
        (∀ i, ‖(u i).2‖ ≤ 1) ∧
        (∀ i, w.isState i = false → (u i).1 = 0) ∧
        (∀ i, w.isState i = true → (u i).2 = 0)
    have hpos : 0 ≤ R := zero_le_one.trans hR
    have hrad : ∀ n u, P n u → P (n + 1) (Fin.snoc u (0, (1, 0))) := by
      intro n u hu
      exact n04Realization_mixedSlots_snoc_with_arity (p base) (p high)
        (fun j => j = k) hpos hu (1, 0) (by
          simp only [Prod.norm_def, norm_one, norm_zero,
            max_eq_left zero_le_one, le_refl])
    have hang : ∀ n u, P n u → P (n + 1) (Fin.snoc u (0, (0, 1))) := by
      intro n u hu
      exact n04Realization_mixedSlots_snoc_with_arity (p base) (p high)
        (fun j => j = k) hpos hu (0, 1) (by
          simp only [Prod.norm_def, norm_one, norm_zero,
            max_eq_right zero_le_one, le_refl])
    have hprefix : ∀ n, n ≤ k + a + b → ∀ u, P n u →
        |J.D n (x, q) u| ≤ M * R ^ exponent := by
      intro n hn u hu
      obtain ⟨w, hw, hl, hh, hp, hs, ht⟩ := hu
      exact hraw R hR hxR n hn w hw u hl hh hp hs ht
    rw [n04Realization_mixedParameter_eq_joint J hU hV hc a b k x hx q hq Q v]
    exact n04Realization_jointMixed_bound_of_stableSlots P hrad hang hV hc
      x hx q hq J k a b (M * R ^ exponent) hprefix (fun i => (v i, 0))
      (n04Realization_mixedSlots_parameters_with_arity (p base) (p high)
        (fun j => j = k) rfl v hv hvR)
  have h := weightedMultilinear_oneHigh_of_unitPower p base high (x - center)
    (Q.D k x) (δ := 1) zero_le_one hM hexponent
    (fun v hv R hR hxR hvR => by simpa only [one_mul] using hb v hv R hR hxR hvR)
  simpa only [one_mul] using h

end ContinuousFlexibility.Analysis
