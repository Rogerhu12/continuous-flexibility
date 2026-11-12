import ContinuousFlexibility.Analysis.JointJetSpatialRegularity

/-!
# Spatial differentiation with the original parameter-slot budget

Appending a pure physical basis vector does not add a parameter slot.
The bound is transferred through the actual mixed-derivative identities,
while the original joint tower and its open product domain are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

/-- A predicate closed under the two physical basis directions controls
mixed spatial derivatives without enlarging its parameter budget. -/
theorem n04Realization_jointMixed_bound_of_stableSlots
    (P : ∀ n : ℕ, (Fin n → E × PolarPoint) → Prop)
    (hrad : ∀ n v, P n v → P (n + 1) (Fin.snoc v (0, (1, 0))))
    (hang : ∀ n v, P n v → P (n + 1) (Fin.snoc v (0, (0, 1))))
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (n a b : ℕ) (B : ℝ)
    (hbound : ∀ m : ℕ, m ≤ n + a + b →
      ∀ u : Fin m → E × PolarPoint, P m u → |J.D m (x, q) u| ≤ B)
    (v : Fin n → E × PolarPoint) (hv : P n v) :
    |mixedDerivative a b (fun p => J.D n (x, p) v) q| ≤ B := by
  have haux : ∀ r : ℕ, ∀ g : E × PolarPoint → ℝ,
      ∀ Jg : SmoothDirections (U ×ˢ V) g,
      ∀ a b : ℕ, a + b ≤ r → ∀ n : ℕ, ∀ B : ℝ,
      (∀ m : ℕ, m ≤ n + a + b →
        ∀ u : Fin m → E × PolarPoint, P m u → |Jg.D m (x, q) u| ≤ B) →
      ∀ v : Fin n → E × PolarPoint, P n v →
        |mixedDerivative a b (fun p => Jg.D n (x, p) v) q| ≤ B := by
    intro r
    induction r with
    | zero =>
        intro g Jg a b hab n B hb v hv
        have ha : a = 0 := by omega
        have hb0 : b = 0 := by omega
        subst a
        subst b
        simpa only [spaces_mixedDerivative_zero] using hb n (by omega) v hv
    | succ r ih =>
        intro g Jg a b hab n B hb v hv
        cases a with
        | succ a =>
            rw [Jg.jointJet_mixed_radial_step hV hc a b n x hx v hq]
            refine ih _ (Jg.fixedLast (0, (1, 0))) a b (by omega) n B ?_ v hv
            intro m hm u hu
            rw [SmoothDirections.fixedLast_apply]
            exact hb (m + 1) (by omega) (Fin.snoc u (0, (1, 0))) (hrad m u hu)
        | zero =>
            cases b with
            | zero =>
                simpa only [spaces_mixedDerivative_zero] using hb n (by omega) v hv
            | succ b =>
                rw [Jg.jointJet_mixed_angular_step hV hc 0 b n x hx v hq]
                refine ih _ (Jg.fixedLast (0, (0, 1))) 0 b (by omega) n B ?_ v hv
                intro m hm u hu
                rw [SmoothDirections.fixedLast_apply]
                exact hb (m + 1) (by omega) (Fin.snoc u (0, (0, 1))) (hang m u hu)
  exact haux (a + b) f J a b le_rfl n B hbound v hv

end ContinuousFlexibility.Analysis
