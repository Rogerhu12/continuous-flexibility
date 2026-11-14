module

public import ContinuousFlexibility.Analysis.OneHighCylinderPureJets
public import ContinuousFlexibility.Analysis.OneHighCompositionJets

/-!
# Actual derivative formulas for smooth composition on the cylinder

Both pure derivative towers come from the composed function itself. Their
pointwise Faà di Bruno bounds involve only the genuine input jets. Local
smoothness of the outer function at the actual input values suffices here;
the convex region through zero is used separately for the zeroth derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : ℝ} [Fact (0 < P)]

theorem composition_sub_base_iteratedDeriv_norm_le
    {v : ℝ → E} {Φ : E → ℝ} {x : ℝ}
    (hv : ContDiffAt ℝ ∞ v x) (hΦ : ContDiffAt ℝ ∞ Φ (v x))
    {s : ℕ} (hs : 0 < s) {B : ℕ → ℝ}
    (hB : ∀ n, 1 ≤ n → n ≤ s → ‖iteratedFDeriv ℝ n Φ (v x)‖ ≤ B n) :
    ‖iteratedDeriv s (fun y => Φ (v y) - Φ 0) x‖ ≤
      ∑ c : OrderedFinpartition s, B c.length *
        ∏ j, ‖iteratedDeriv (c.partSize j) v x‖ := by
  have hsub : iteratedDeriv s (fun y => Φ (v y) - Φ 0) x =
      iteratedDeriv s (Φ ∘ v) x := by
    simpa only [sub_eq_add_neg, add_comm, Function.comp_apply] using
      (iteratedDeriv_const_add (f := Φ ∘ v) (x := x) hs (-Φ 0))
  rw [hsub]
  have h := norm_iteratedFDeriv_comp_le_bounded_partition_sum hΦ hv hs hB
  simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  exact h

def cylinderComposition (u : CylinderSmoothJet P E) (Φ : E → ℝ)
    (p : ℝ × AddCircle P) : ℝ :=
  Φ (u.jet 0 0 p) - Φ 0

theorem cylinderComposition_contDiff_lift (u : CylinderSmoothJet P E) (Φ : E → ℝ)
    (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p)) :
    ContDiff ℝ ∞
      (fun p : ℝ × ℝ => cylinderComposition u Φ (p.1, (p.2 : AddCircle P))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact ((hΦ (p.1, (p.2 : AddCircle P))).comp p
    (u.contDiff_lift 0 0).contDiffAt).sub contDiffAt_const

theorem continuous_cylinderComposition (u : CylinderSmoothJet P E) (Φ : E → ℝ)
    (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p)) :
    Continuous (cylinderComposition u Φ) :=
  continuous_cylinder_of_lift (cylinderComposition_contDiff_lift u Φ hΦ).continuous

theorem cylinder_composition_radial_pointwise
    (u : CylinderSmoothJet P E) (Φ : E → ℝ)
    (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p))
    {s : ℕ} (hs : 0 < s) {B : ℕ → ℝ}
    (hB : ∀ p n, 1 ≤ n → n ≤ s →
      ‖iteratedFDeriv ℝ n Φ (u.jet 0 0 p)‖ ≤ B n)
    (p : ℝ × AddCircle P) :
    ‖cylinderRadialJet (cylinderComposition u Φ) s p‖ ≤
      ∑ c : OrderedFinpartition s, B c.length *
        ∏ j, ‖u.jet (c.partSize j) 0 p‖ := by
  let v : ℝ → E := fun r => u.jet 0 0 (r, p.2)
  have hv : ContDiff ℝ ∞ v :=
    cylinder_radial_slice_contDiff (u.contDiff_lift 0 0) p.2
  have hj (n : ℕ) : iteratedDeriv n v p.1 = u.jet n 0 p := by
    simpa only [v, Nat.zero_add] using
      congrFun (u.iteratedDeriv_radial 0 0 n p.2) p.1
  have h := composition_sub_base_iteratedDeriv_norm_le
    (v := v) hv.contDiffAt (hΦ p) hs (hB p)
  simp_rw [hj] at h
  simpa only [cylinderRadialJet, cylinderComposition, v] using h

theorem cylinder_composition_angular_pointwise
    (u : CylinderSmoothJet P E) (Φ : E → ℝ)
    (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p))
    {s : ℕ} (hs : 0 < s) {B : ℕ → ℝ}
    (hB : ∀ p n, 1 ≤ n → n ≤ s →
      ‖iteratedFDeriv ℝ n Φ (u.jet 0 0 p)‖ ≤ B n)
    (p : ℝ × AddCircle P) :
    ‖cylinderAngularJet (cylinderComposition u Φ) s p‖ ≤
      ∑ c : OrderedFinpartition s, B c.length *
        ∏ j, ‖u.jet 0 (c.partSize j) p‖ := by
  obtain ⟨r, θ⟩ := p
  refine QuotientAddGroup.induction_on θ ?_
  intro x
  let v : ℝ → E := fun y => u.jet 0 0 (r, (y : AddCircle P))
  have hv : ContDiff ℝ ∞ v :=
    cylinder_angular_slice_contDiff (u.contDiff_lift 0 0) r
  have hj (n : ℕ) : iteratedDeriv n v x = u.jet 0 n (r, (x : AddCircle P)) := by
    simpa only [v, Nat.zero_add] using
      congrFun (u.iteratedDeriv_angular 0 0 n r) x
  have h := composition_sub_base_iteratedDeriv_norm_le
    (v := v) hv.contDiffAt (hΦ (r, (x : AddCircle P))) hs
    (hB (r, (x : AddCircle P)))
  simp_rw [hj] at h
  simpa only [cylinderAngularJet_coe_apply, cylinderComposition, v] using h

end ContinuousFlexibility.Analysis
