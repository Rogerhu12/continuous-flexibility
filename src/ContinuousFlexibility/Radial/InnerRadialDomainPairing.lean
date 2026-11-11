import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# First-order integration by parts on the actual physical domain

The actual zero-endpoint domain is a closure of physical smooth fields.
Continuity extends its integration-by-parts identity to that closure.
Adding the fixed affine lift then recovers the canonical endpoint trace.
For a matched finite chain, these endpoint terms cancel exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

section Piece

variable (D : ReferenceData) (hw : Continuous D.w)
  {a b : ℝ} (hab : a < b) (ha : 0 < a)
  (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
  {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)

include hab in
/-- The first-order Green identity holds on the actual physical closure,
with no classical derivative assumed for its field coordinate. -/
theorem innerRadialH1Zero_firstOrder_pairing {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Zero D a b) :
    ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
      hp.continuous.continuousOn⟫_ℝ +
    ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
      (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ = 0 := by
  have hclosed : IsClosed {q : InnerRadialH1Pair D |
      ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
        hp.continuous.continuousOn⟫_ℝ +
      ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
        (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ = 0} :=
    isClosed_eq ((continuous_snd.inner continuous_const).add
      (continuous_fst.inner continuous_const)) continuous_const
  apply closure_minimal (t := {q : InnerRadialH1Pair D |
      ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
        hp.continuous.continuousOn⟫_ℝ +
      ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
        (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ = 0})
    ?_ hclosed ((mem_innerRadialH1Zero D a b q).mp hq)
  rintro r ⟨φ, hφ, _, hs, hu, hd⟩
  have hφa : φ a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
  have hφb : φ b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hs h).2)
  have h := innerRadialH1_smooth_trace_pairing D hw hab ha hcore hpos
    (fun _ _ => hφ.contDiffAt) (fun _ _ => hp.contDiffAt) hu hd
  change ⟪r.2, innerRadialTraceGradientTest D hw ha hcore hpos p
      hp.continuous.continuousOn⟫_ℝ +
    ⟪r.1, innerRadialTraceValueTest D hw ha hcore hpos p
      (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ = 0
  simpa only [hφa, hφb, mul_zero, sub_self] using h

include hab in
theorem innerRadialAffineLift_firstOrder_pairing (z : Fin 2 → ℝ) :
    ⟪(innerRadialAffineLift D hw ha hcore hpos z).2,
      innerRadialTraceGradientTest D hw ha hcore hpos p
        hp.continuous.continuousOn⟫_ℝ +
    ⟪(innerRadialAffineLift D hw ha hcore hpos z).1,
      innerRadialTraceValueTest D hw ha hcore hpos p
        (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ =
      p b * z 1 - p a * z 0 := by
  have hunit (i : Fin 2) := innerRadialH1_smooth_trace_pairing D hw hab ha hcore hpos
    (fun _ _ => (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).contDiffAt)
    (fun _ _ => hp.contDiffAt)
    (innerRadialAffineUnitPair_value_ae D hw ha hcore hpos i)
    (innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos i)
  have h0 := hunit 0
  have h1 := hunit 1
  have he0 := innerIntervalAffineLift_endpoints hab (innerEndpointValues 0)
  have he1 := innerIntervalAffineLift_endpoints hab (innerEndpointValues 1)
  rw [he0.1, he0.2] at h0
  rw [he1.1, he1.2] at h1
  norm_num [innerEndpointValues] at h0 h1
  simp only [innerRadialAffineLift_apply, Prod.snd_add, Prod.fst_add,
    Prod.smul_snd, Prod.smul_fst, inner_add_left, real_inner_smul_left]
  linear_combination z 0 * h0 + z 1 * h1

include hab in
/-- The full actual domain determines the boundary term for every
smooth multiplier, not just the two affine trace multipliers. -/
theorem innerRadialH1Domain_firstOrder_pairing {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha hcore hpos) :
    ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
      hp.continuous.continuousOn⟫_ℝ +
    ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
      (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ =
      p b * innerRadialH1Trace D hw ha hcore hpos q 1 -
        p a * innerRadialH1Trace D hw ha hcore hpos q 0 := by
  have hzero := innerRadialH1Zero_firstOrder_pairing D hw hab ha hcore hpos hp
    ((mem_innerRadialH1Domain D hw ha hcore hpos q).mp hq)
  have hlift := innerRadialAffineLift_firstOrder_pairing D hw hab ha hcore hpos hp
    (innerRadialH1Trace D hw ha hcore hpos q)
  simp only [Prod.snd_sub, Prod.fst_sub, inner_sub_left] at hzero
  linarith

end Piece

/-- Internal cut values cancel once, and only the two exterior values
remain; those are zero in the genuine matched-chain domain. -/
theorem innerRadialChainBoundary_pairing_sum {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (ξ : EuclideanSpace ℝ (Fin n)) (p : ℝ → ℝ) :
    (∑ k : Fin (n + 1),
      (p (G.right k) * innerChainBoundaryRestriction n k ξ 1 -
        p (G.left k) * innerChainBoundaryRestriction n k ξ 0)) = 0 := by
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun k : Fin (n + 1) =>
      p (G.right k) * innerChainBoundaryRestriction n k ξ 1),
    Fin.sum_univ_succ (fun k : Fin (n + 1) =>
      p (G.left k) * innerChainBoundaryRestriction n k ξ 0)]
  rw [(innerChainBoundaryRestriction_outer n ξ).1,
    (innerChainBoundaryRestriction_outer n ξ).2, mul_zero, mul_zero, add_zero, zero_add]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro k _
  rw [(innerChainBoundaryRestriction_match n k ξ).1,
    (innerChainBoundaryRestriction_match n k ξ).2]
  rfl

/-- No assumed gluing equation is used here: cancellation follows from
the actual canonical H¹ traces in the finite matched domain. -/
theorem innerRadialChainDomain_firstOrder_pairing
    (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
    (G : InnerRadialChainGeometry D n)
    {q : Fin (n + 1) → InnerRadialH1Pair D}
    (hq : q ∈ innerRadialChainDomain D hw G)
    {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) :
    (∑ k : Fin (n + 1),
      (⟪(q k).2, innerRadialTraceGradientTest D hw (G.left_pos k) (G.in_core k)
        (G.weight_pos k) p hp.continuous.continuousOn⟫_ℝ +
      ⟪(q k).1, innerRadialTraceValueTest D hw (G.left_pos k) (G.in_core k)
        (G.weight_pos k) p
        (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ)) = 0 := by
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G q).mp hq
  calc
    _ = ∑ k : Fin (n + 1),
        (p (G.right k) * innerChainBoundaryRestriction n k ξ 1 -
          p (G.left k) * innerChainBoundaryRestriction n k ξ 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [innerRadialH1Domain_firstOrder_pairing D hw (G.left_lt_right k)
        (G.left_pos k) (G.in_core k) (G.weight_pos k) hp (hξ k).1, (hξ k).2]
    _ = 0 := innerRadialChainBoundary_pairing_sum G ξ p

end ContinuousFlexibility.Radial
