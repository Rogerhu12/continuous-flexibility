module

public import ContinuousFlexibility.Radial.InnerRadialH1Density
public import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-!
# Smooth tests in the actual matched physical domain

These statements construct domain membership from the actual field and
normalized derivative. Arbitrary endpoint values are obtained by the
fixed affine lift; only the residual is sent to the proved H¹ closure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section Piece

variable (D : ReferenceData) (hw : Continuous D.w) {a b : ℝ}
  (hab : a < b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

/-- The physical affine lift realizes the ordinary affine function,
including its actual normalized derivative. -/
theorem innerRadialAffineLift_representatives (z : Fin 2 → ℝ) :
    ((innerRadialAffineLift D hw ha hcore hpos z).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator (innerIntervalAffineLift a b z) ∧
    ((innerRadialAffineLift D hw ha hcore hpos z).2 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D]
        (Ioo a b).indicator (innerGapGradientField (innerIntervalAffineLift a b z)) := by
  let Q := innerRadialAffineUnitPair D hw ha hcore hpos
  let φ : Fin 2 → ℝ → ℝ := fun i => innerIntervalAffineLift a b (innerEndpointValues i)
  have hφ (i : Fin 2) : ContDiff ℝ ∞ (φ i) :=
    innerIntervalAffineLift_contDiff a b (innerEndpointValues i)
  have hf : innerIntervalAffineLift a b z =
      fun r => z 0 * φ 0 r + z 1 * φ 1 r := by
    funext r
    norm_num [φ, innerIntervalAffineLift, innerEndpointValues] <;> ring
  have hd (r : ℝ) : deriv (innerIntervalAffineLift a b z) r =
      z 0 * deriv (φ 0) r + z 1 * deriv (φ 1) r := by
    rw [hf]
    exact ((((hφ 0).differentiable (by simp) r).hasDerivAt.const_mul (z 0)).add
      (((hφ 1).differentiable (by simp) r).hasDerivAt.const_mul (z 1))).deriv
  constructor
  · simp only [innerRadialAffineLift_apply, Prod.fst_add, Prod.smul_fst]
    filter_upwards [Lp.coeFn_add (z 0 • (Q 0).1) (z 1 • (Q 1).1),
      Lp.coeFn_smul (z 0) (Q 0).1, Lp.coeFn_smul (z 1) (Q 1).1,
      innerRadialAffineUnitPair_value_ae D hw ha hcore hpos 0,
      innerRadialAffineUnitPair_value_ae D hw ha hcore hpos 1]
      with r hadd hzero hone hqzero hqone
    rw [hadd, Pi.add_apply, hzero, hone, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hqzero, hqone]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, hf, φ]
    · simp only [indicator_of_notMem hr, mul_zero, zero_add]
  · simp only [innerRadialAffineLift_apply, Prod.snd_add, Prod.smul_snd]
    filter_upwards [Lp.coeFn_add (z 0 • (Q 0).2) (z 1 • (Q 1).2),
      Lp.coeFn_smul (z 0) (Q 0).2, Lp.coeFn_smul (z 1) (Q 1).2,
      innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos 0,
      innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos 1]
      with r hadd hzero hone hqzero hqone
    rw [hadd, Pi.add_apply, hzero, hone, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hqzero, hqone]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, innerGapGradientField, hd]
      dsimp only [φ]
      ring
    · simp only [indicator_of_notMem hr, mul_zero, zero_add]

include hab in
/-- A smooth field belongs to the genuine physical domain with exactly
its ordinary endpoint values. No domain membership is an input. -/
theorem innerRadialH1Pair_smooth_domain_trace {u : ℝ → ℝ}
    (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r) {Q : InnerRadialH1Pair D}
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u)) :
    Q ∈ innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos Q = fun i => if i = 0 then u a else u b := by
  let z : Fin 2 → ℝ := fun i => if i = 0 then u a else u b
  let φ := innerIntervalAffineLift a b z
  have hφ : ContDiff ℝ ∞ φ := innerIntervalAffineLift_contDiff a b z
  have he := innerIntervalAffineLift_endpoints hab z
  have hA := innerRadialAffineLift_representatives D hw ha hcore hpos z
  apply (innerRadialH1Domain_trace_iff D hw hab ha hcore hpos Q z).mpr
  apply innerRadialH1Zero_of_smooth_zero_endpoints D hw hab ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (fun r hr => (hu r hr).sub hφ.contDiffAt)
    (by simp only [Pi.sub_apply, φ, he.1, z, ite_true, sub_self])
    (by simp only [Pi.sub_apply, φ, he.2, z,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, sub_self])
  · filter_upwards [Lp.coeFn_sub Q.1 (innerRadialAffineLift D hw ha hcore hpos z).1,
      hQu, hA.1] with r hsub hQ hA
    rw [hsub, Pi.sub_apply, hQ, hA]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, Pi.sub_apply, φ]
    · simp only [indicator_of_notMem hr, sub_self]
  · filter_upwards [Lp.coeFn_sub Q.2 (innerRadialAffineLift D hw ha hcore hpos z).2,
      hQd, hA.2] with r hsub hQ hA
    rw [hsub, Pi.sub_apply, hQ, hA]
    by_cases hr : r ∈ Ioo a b
    · have hd : deriv (fun x => u x - φ x) r = deriv u r - deriv φ r :=
        (((hu r (Ioo_subset_Icc_self hr)).differentiableAt (by simp)).hasDerivAt.sub
          (hφ.differentiable (by simp) r).hasDerivAt).deriv
      simp only [indicator_of_mem hr, innerGapGradientField]
      change (r / sqrt 12) * deriv u r - (r / sqrt 12) * deriv φ r =
        (r / sqrt 12) * deriv (fun x => u x - φ x) r
      rw [hd]
      ring
    · simp only [indicator_of_notMem hr, sub_self]

end Piece

/-- Restricting a single smooth test to every piece produces a genuine
matched test, provided its two exterior values vanish. -/
theorem innerRadialChain_smooth_test_mem (D : ReferenceData) (hw : Continuous D.w)
    {n : ℕ} (G : InnerRadialChainGeometry D n) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hleft : ψ (G.left 0) = 0)
    (hright : ψ (G.right (Fin.last n)) = 0)
    {Q : Fin (n + 1) → InnerRadialH1Pair D}
    (hQu : ∀ p, ((Q p).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo (G.left p) (G.right p)).indicator ψ)
    (hQd : ∀ p, ((Q p).2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo (G.left p) (G.right p)).indicator (innerGapGradientField ψ)) :
    Q ∈ innerRadialChainDomain D hw G := by
  let ξ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2
    (fun i : Fin n => ψ (G.cuts i.succ.castSucc))
  apply (innerRadialChainDomain_trace_iff D hw G Q).mpr
  refine ⟨ξ, ?_⟩
  intro p
  obtain ⟨hp, ht⟩ := innerRadialH1Pair_smooth_domain_trace D hw (G.left_lt_right p)
    (G.left_pos p) (G.in_core p) (G.weight_pos p)
    (fun _ _ => hψ.contDiffAt) (hQu p) (hQd p)
  refine ⟨hp, ht.trans ?_⟩
  funext i
  rw [innerChainBoundaryRestriction_apply]
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]
    by_cases hp : 0 < p.val
    · rw [dif_pos hp]
      change ψ (G.cuts p.castSucc) = ξ ⟨p.val - 1, by omega⟩
      rw [show ξ ⟨p.val - 1, by omega⟩ =
        ψ (G.cuts (⟨p.val - 1, by omega⟩ : Fin n).succ.castSucc) from PiLp.toLp_apply _ _ _ _]
      congr 2
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    · rw [dif_neg hp]
      have hp0 : p = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      simpa only [hp0] using hleft
  · rw [if_neg hi, if_neg hi]
    by_cases hp : p.val < n
    · rw [dif_pos hp]
      change ψ (G.cuts p.succ) = ξ ⟨p.val, hp⟩
      rw [show ξ ⟨p.val, hp⟩ =
        ψ (G.cuts (⟨p.val, hp⟩ : Fin n).succ.castSucc) from PiLp.toLp_apply _ _ _ _]
      congr 2
    · rw [dif_neg hp]
      have hplast : p = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
      simpa only [hplast] using hright

end ContinuousFlexibility.Radial
