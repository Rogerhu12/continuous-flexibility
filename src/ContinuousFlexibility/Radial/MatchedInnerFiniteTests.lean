import ContinuousFlexibility.Radial.MatchedInnerSmoothTests
import ContinuousFlexibility.Radial.MatchedInnerSmoothGreen
import ContinuousFlexibility.Radial.InnerRadialH1Support
import ContinuousFlexibility.Radial.InnerRadialPotentialGraph
import ContinuousFlexibility.Radial.ModeCoreSource

/-!
# Actual smooth tests and cancellation on the finite physical chain

The test field and gradient are restrictions in the existing radial
Hilbert space. Their true endpoint values put them in the finite weak
domain. Smooth Green identities against arbitrary domain elements then
cancel at every internal cut, with the actual endpoint normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace BigOperators
open ContinuousFlexibility.Statements

def matchedInnerSmoothTest (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) : InnerRadialH1Pair D :=
  (innerRadialIntervalToLp D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) ψ hψ.continuous.continuousOn,
    innerRadialIntervalToLp D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapGradientField ψ)
      (innerGapGradientField_continuous hψ).continuousOn)

theorem matchedInnerSmoothTest_value_ae (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ((matchedInnerSmoothTest D hw ha hcore hpos ψ hψ).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator ψ :=
  innerRadialIntervalToLp_ae D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) ψ hψ.continuous.continuousOn

theorem matchedInnerSmoothTest_gradient_ae (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ((matchedInnerSmoothTest D hw ha hcore hpos ψ hψ).2 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator (innerGapGradientField ψ) :=
  innerRadialIntervalToLp_ae D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapGradientField ψ)
    (innerGapGradientField_continuous hψ).continuousOn

theorem matchedInnerSmoothTest_domain_trace (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    matchedInnerSmoothTest D hw ha hcore hpos ψ hψ ∈
        innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos
        (matchedInnerSmoothTest D hw ha hcore hpos ψ hψ) =
          (fun i => if i = 0 then ψ a else ψ b) :=
  matchedInnerH1Pair_smooth_domain_trace D hw ha hcore hpos hab
    (fun _ _ => hψ.contDiffAt)
    (matchedInnerSmoothTest_value_ae D hw ha hcore hpos ψ hψ)
    (matchedInnerSmoothTest_gradient_ae D hw ha hcore hpos ψ hψ)

theorem matchedInnerSmoothTest_value_projection {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    (matchedInnerSmoothTest D hw ha hcore hpos ψ hψ).1 =
      innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b)
        (matchingSmoothVector D hD ψ hψ) := by
  apply Lp.ext
  filter_upwards [matchedInnerSmoothTest_value_ae D hw ha hcore hpos ψ hψ,
    innerL2PieceProjection_ae (radialHilbertMeasure D) (Ioo a b)
      measurableSet_Ioo (matchingSmoothVector D hD ψ hψ),
    matchingTestInput_coe hD ψ hψ 0] with r hT hP hψr
  rw [hT, hP]
  by_cases hr : r ∈ Ioo a b
  · rw [indicator_of_mem hr, indicator_of_mem hr]
    exact hψr.symm
  · rw [indicator_of_notMem hr, indicator_of_notMem hr]

/-- Local Green reciprocity uses the genuine Hilbert Jacobi test.
The potential coordinate is constrained by the existing signed
multiplication relation. -/
theorem matchedInnerSmoothTest_green {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℕ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {q : InnerRadialH1Pair D} {v : RadialModeL2 D}
    (hq : q ∈ innerRadialH1Domain D hw.continuous ha hcore hpos)
    (hv : InnerRadialPotentialClass D (j : ℝ) a b q.1 v) :
    ⟪q.2, (matchedInnerSmoothTest D hw.continuous ha hcore hpos ψ hψ).2⟫_ℝ +
        ⟪v, (matchedInnerSmoothTest D hw.continuous ha hcore hpos ψ hψ).1⟫_ℝ +
        ⟪q.1, matchingJacobiVector D hD j ψ hψ⟫_ℝ =
      innerRadialH1Trace D hw.continuous ha hcore hpos q 1 * (D.w b * deriv ψ b) -
        innerRadialH1Trace D hw.continuous ha hcore hpos q 0 * (D.w a * deriv ψ a) := by
  let T := matchedInnerSmoothTest D hw.continuous ha hcore hpos ψ hψ
  let J := matchingJacobiVector D hD j ψ hψ
  let P := innerL2PieceProjection (radialHilbertMeasure D) (Ioo a b)
  let V := innerRadialPotentialMultiplier D hw (j : ℝ) hpos T.1
  have hV : InnerRadialPotentialClass D (j : ℝ) a b T.1 V :=
    innerRadialPotentialMultiplier_class D hw (j : ℝ) hpos T.1
  have hF : (((-P J - (0 : ℝ) • (0 : RadialModeL2 D)) : RadialModeL2 D) : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator
        (fun r => -radialJacobi ((j : ℝ) ^ 2) D.w ψ r / (12 * D.w r / r ^ 2)) := by
    simp only [zero_smul, sub_zero]
    filter_upwards [Lp.coeFn_neg (P J),
      innerL2PieceProjection_ae (radialHilbertMeasure D) (Ioo a b) measurableSet_Ioo J,
      (matchingJacobiTest_memLp hD hψ j).coeFn_toLp] with r hn hP hJ
    rw [hn, Pi.neg_apply, hP]
    by_cases hr : r ∈ Ioo a b
    · rw [indicator_of_mem hr, indicator_of_mem hr, hJ]
      simp only [matchingJacobiTest, matchingDensity]
      ring
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, neg_zero]
  have h := matchedInner_smoothResidual_domain D hw hab ha hcore hpos
    (fun _ _ => hψ.contDiffAt) 0
    (matchedInnerSmoothTest_value_ae D hw.continuous ha hcore hpos ψ hψ)
    (matchedInnerSmoothTest_gradient_ae D hw.continuous ha hcore hpos ψ hψ) hV hF hq
  simp only [innerRadialWeakResidual_apply, zero_mul, add_zero, inner_neg_left,
    sub_neg_eq_add] at h
  have hpot : ⟪v, T.1⟫_ℝ = ⟪V, q.1⟫_ℝ := hv.inner_symm hV
  have hproj : ⟪P J, q.1⟫_ℝ = ⟪J, q.1⟫_ℝ :=
    innerL2PieceProjection_inner_fixed (radialHilbertMeasure D) (Ioo a b) J q.1
      (innerRadialH1Domain_piece_projection D hw.continuous ha hcore hpos hq)
  rw [real_inner_comm T.2 q.2, ← hpot, hproj, real_inner_comm J q.1] at h
  exact h

def matchedInnerChainSmoothTest (D : ReferenceData) (hw : Continuous D.w)
    {n : ℕ} (G : InnerRadialChainGeometry D n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (p : Fin (n + 1)) : InnerRadialH1Pair D :=
  matchedInnerSmoothTest D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) ψ hψ

/-- Every smooth test vanishing at the two outer cuts belongs to the
actual matched finite domain, even if it crosses internal cuts. -/
theorem matchedInnerChainSmoothTest_mem (D : ReferenceData) (hw : Continuous D.w)
    {n : ℕ} (G : InnerRadialChainGeometry D n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hl : ψ (G.left 0) = 0) (hr : ψ (G.right (Fin.last n)) = 0) :
    matchedInnerChainSmoothTest D hw G ψ hψ ∈ innerRadialChainDomain D hw G := by
  let ξ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2
    (fun i => ψ (G.right i.castSucc))
  apply (innerRadialChainDomain_trace_iff D hw G _).mpr
  refine ⟨ξ, ?_⟩
  intro p
  have hp := matchedInnerSmoothTest_domain_trace D hw (G.left_lt_right p)
    (G.left_pos p) (G.in_core p) (G.weight_pos p) ψ hψ
  refine ⟨hp.1, ?_⟩
  rw [hp.2]
  funext i
  fin_cases i
  · simp only [innerChainBoundaryRestriction_apply, if_pos rfl]
    by_cases hp₀ : 0 < p.val
    · rw [dif_pos hp₀]
      change ψ (G.left p) = ψ (G.right (⟨p.val - 1, by omega⟩ : Fin n).castSucc)
      congr 1
      unfold InnerRadialChainGeometry.left InnerRadialChainGeometry.right
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    · rw [dif_neg hp₀]
      have hpz : p = 0 := Fin.ext (by omega)
      simpa only [hpz] using hl
  · simp only [innerChainBoundaryRestriction_apply,
      show (1 : Fin 2) ≠ 0 by decide, if_false]
    by_cases hpn : p.val < n
    · rw [dif_pos hpn]
      change ψ (G.right p) = ψ (G.right (⟨p.val, hpn⟩ : Fin n).castSucc)
      congr 2
      exact Fin.ext rfl
    · rw [dif_neg hpn]
      have hplast : p = Fin.last n := Fin.ext (by omega)
      simpa only [hplast] using hr

/-- The finite common trace vector cancels all internal boundary terms;
the two external boundary restrictions are zero by construction. -/
theorem matchedInnerChain_boundary_cancel {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (ξ : EuclideanSpace ℝ (Fin n)) (f : ℝ → ℝ) :
    (∑ p : Fin (n + 1),
      innerChainBoundaryRestriction n p ξ 1 * f (G.right p) -
        innerChainBoundaryRestriction n p ξ 0 * f (G.left p)) = 0 := by
  have hR : (∑ p : Fin (n + 1),
      innerChainBoundaryRestriction n p ξ 1 * f (G.right p)) =
        ∑ i : Fin n, ξ i * f (G.right i.castSucc) := by
    rw [Fin.sum_univ_castSucc, (innerChainBoundaryRestriction_outer n ξ).2,
      zero_mul, add_zero]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [(innerChainBoundaryRestriction_match n i ξ).1])
  have hL : (∑ p : Fin (n + 1),
      innerChainBoundaryRestriction n p ξ 0 * f (G.left p)) =
        ∑ i : Fin n, ξ i * f (G.left i.succ) := by
    rw [Fin.sum_univ_succ, (innerChainBoundaryRestriction_outer n ξ).1,
      zero_mul, zero_add]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [(innerChainBoundaryRestriction_match n i ξ).2])
  rw [Finset.sum_sub_distrib, hR, hL]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  rfl

end ContinuousFlexibility.Radial
