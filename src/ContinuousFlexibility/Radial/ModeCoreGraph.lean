import ContinuousFlexibility.Radial.ModeCoreSource
import ContinuousFlexibility.Radial.RadialGreenBoundary

/-!
# The extended modal graph and its actual smooth core

At frequency two this is the bordered maximal weak graph. At other
frequencies only the inactive scalar is extended by the identity. The
differential component and every original smooth weak test are unchanged.
The graph is exactly the adjoint relation of the concrete smooth test
pairs, and those pairs satisfy the graph by the global Green identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

def ModeExtendedGraph (D : ReferenceData) (j : ℕ)
    (U F : RadialModePair D) : Prop :=
  ModeLocalEquation D j (radialCore D) (U.1, if j = 2 then U.2 else 0) F ∧
    if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
    else U.2 = F.2

@[simp]
theorem matchingSmoothVector_zero (D : ReferenceData) (hD : IsAccumulatingProfile D) :
    matchingSmoothVector D hD (0 : ℝ → ℝ) contDiff_const = 0 :=
  MemLp.toLp_zero _

@[simp]
theorem matchingJacobiVector_zero (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (j : ℕ) :
    matchingJacobiVector D hD j (0 : ℝ → ℝ) contDiff_const = 0 := by
  apply Lp.ext
  filter_upwards [(matchingJacobiTest_memLp hD
    (show ContDiff ℝ ∞ (0 : ℝ → ℝ) from contDiff_const) j).coeFn_toLp,
      (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D) : ⇑(0 : RadialModeL2 D) =ᵐ[radialHilbertMeasure D] 0)]
    with r h₁ h₂
  change ((matchingJacobiTest_memLp hD contDiff_const j).toLp
    (matchingJacobiTest D j (0 : ℝ → ℝ)) : ℝ → ℝ) r = _
  rw [h₁, h₂]
  simp only [matchingJacobiTest, radialJacobi, Pi.zero_apply, deriv_const,
    mul_zero, sub_zero, zero_div]

theorem modeExtendedGraph_iff_core_pairings {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (j : ℕ) (U F : RadialModePair D) :
    ModeExtendedGraph D j U F ↔
      ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ), HasCompactSupport ψ →
        Function.support ψ ⊆ radialCore D → ∀ s : ℝ,
          modePairing D U (matchingTestSource D hD hB j ψ hψ s) =
            modePairing D F (matchingTestInput D hD ψ hψ s) := by
  constructor
  · intro h ψ hψ hc hs s
    have he := (modeLocalEquation_iff_inner hD j (radialCore D) _ _).mp h.1
      ψ hψ hc hs
    rw [matchingTestSource_pairing]
    change -⟪U.1, matchingJacobiVector D hD j ψ hψ⟫_ℝ +
      (if j = 2 then U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) +
        s * ⟪U.1, matchingBorderVector D hD hB⟫_ℝ else U.2 * s) =
      ⟪F.1, matchingSmoothVector D hD ψ hψ⟫_ℝ + F.2 * s
    by_cases hj : j = 2
    · have hr : ⟪U.1, matchingBorderVector D hD hB⟫_ℝ = F.2 := by
        rw [← matchingColumn_integral_eq_inner hD hB]
        simpa only [hj, if_pos, ite_true] using h.2
      simp only [hj, if_pos, ite_true] at he ⊢
      rw [hr]
      nlinarith only [he]
    · have hr : U.2 = F.2 := by simpa only [hj, if_neg, ite_false] using h.2
      simp only [hj, if_neg, ite_false, zero_mul, sub_zero] at he ⊢
      rw [hr]
      nlinarith only [he]
  · intro h
    constructor
    · apply (modeLocalEquation_iff_inner hD j (radialCore D) _ _).mpr
      intro ψ hψ hc hs
      have he := h ψ hψ hc hs 0
      rw [matchingTestSource_pairing] at he
      change -⟪U.1, matchingJacobiVector D hD j ψ hψ⟫_ℝ +
        (if j = 2 then U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) +
          0 * ⟪U.1, matchingBorderVector D hD hB⟫_ℝ else U.2 * 0) =
        ⟪F.1, matchingSmoothVector D hD ψ hψ⟫_ℝ + F.2 * 0 at he
      by_cases hj : j = 2
      · simp only [hj, if_pos, ite_true, zero_mul, mul_zero, add_zero] at he ⊢
        linarith only [he]
      · simp only [hj, if_neg, ite_false, zero_mul, mul_zero, add_zero, sub_zero] at he ⊢
        linarith only [he]
    · have hz := h 0 contDiff_const hasCompactSupport_zero (by simp) 1
      rw [matchingTestSource_pairing] at hz
      simp only [matchingTestInput, modePairing, matchingJacobiVector_zero,
        matchingSmoothVector_zero, inner_zero_right, neg_zero, zero_add,
        Pi.zero_apply, mul_zero, intervalIntegral.integral_zero, one_mul, mul_one,
        add_zero] at hz
      by_cases hj : j = 2
      · simp only [hj, if_pos, ite_true] at hz ⊢
        rw [matchingColumn_integral_eq_inner hD hB]
        exact hz
      · simpa only [hj, if_neg, ite_false] using hz

theorem modeFullGraph_iff_extended {D : ReferenceData} (j : ℕ)
    (U F : RadialModePair D) :
    ModeFullGraph D j U F ↔
      ModeExtendedGraph D j U F ∧ (j ≠ 2 → F.2 = 0) := by
  by_cases hj : j = 2
  · simp [ModeFullGraph, ModeExtendedGraph, hj]
  · constructor
    · intro h
      have hzero : U.2 = 0 ∧ F.2 = 0 := by simpa only [hj, if_neg, ite_false] using h.2
      have hu : U.2 = 0 := hzero.1
      have hf : F.2 = 0 := hzero.2
      have hpair : (U.1, (0 : ℝ)) = U := by
        apply Prod.ext
        · rfl
        · exact hu.symm
      refine ⟨⟨?_, ?_⟩, fun _ => hf⟩
      · simpa only [hj, if_neg, ite_false, hpair] using h.1
      · simp only [hj, if_neg, ite_false]
        exact hu.trans hf.symm
    · rintro ⟨h, hf⟩
      have hF : F.2 = 0 := hf hj
      have hrow : U.2 = F.2 := by simpa only [hj, if_neg, ite_false] using h.2
      have hU : U.2 = 0 := hrow.trans hF
      have hpair : (U.1, (0 : ℝ)) = U := by
        apply Prod.ext
        · rfl
        · exact hU.symm
      refine ⟨?_, ?_⟩
      · simpa only [hj, if_neg, ite_false, hpair] using h.1
      · simpa only [hj, if_neg, ite_false] using And.intro hU hF

theorem matchingJacobi_continuousOn {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    ContinuousOn (radialJacobi ((j : ℝ) ^ 2) D.w ψ) (Icc D.a D.b) := by
  have hw : ContDiff ℝ ∞ D.w := (matchingProfileGeometry hD).2.2.1.1
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hp : ContDiff ℝ ∞ (deriv (fun r => D.w r * deriv ψ r)) :=
    (contDiff_infty_iff_deriv.mp (hw.mul hdψ)).2
  exact hp.continuous.continuousOn.sub
    ((matchingPotential_continuousOn hD j).mul hψ.continuous.continuousOn)

theorem matchingSmoothVector_jacobi_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (j : ℕ) {ψ η : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hη : ContDiff ℝ ∞ η) :
    ⟪matchingSmoothVector D hD ψ hψ, matchingJacobiVector D hD j η hη⟫_ℝ =
      ∫ r in D.a..D.b, ψ r * radialJacobi ((j : ℝ) ^ 2) D.w η r := by
  calc
    _ = ∫ r in D.a..D.b, matchingSmoothVector D hD ψ hψ r *
        radialJacobi ((j : ℝ) ^ 2) D.w η r :=
      (matchingJacobi_integral_eq_inner hD (matchingSmoothVector D hD ψ hψ) hη j).symm
    _ = _ := by
      apply matchingInterval_congr_ae hD
      filter_upwards [matchingTestInput_coe hD ψ hψ 0] with r hr
      change matchingSmoothVector D hD ψ hψ r = ψ r at hr
      rw [hr]

theorem matchingSmoothVector_border_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ⟪matchingSmoothVector D hD ψ hψ, matchingBorderVector D hD hB⟫_ℝ =
      ∫ r in D.a..D.b, referenceColumn D r * ψ r := by
  rw [← matchingColumn_integral_eq_inner hD hB]
  apply matchingInterval_congr_ae hD
  filter_upwards [matchingTestInput_coe hD ψ hψ 0] with r hr
  change matchingSmoothVector D hD ψ hψ r = ψ r at hr
  rw [hr]

theorem matchingSmoothVector_jacobi_symm {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (j : ℕ) {ψ η : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hη : ContDiff ℝ ∞ η) :
    ⟪matchingSmoothVector D hD ψ hψ, matchingJacobiVector D hD j η hη⟫_ℝ =
      ⟪matchingSmoothVector D hD η hη, matchingJacobiVector D hD j ψ hψ⟫_ℝ := by
  rw [matchingSmoothVector_jacobi_pairing hD j hψ hη,
    matchingSmoothVector_jacobi_pairing hD j hη hψ]
  have hg := matchingProfileGeometry hD
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hdη : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hi₁ : IntervalIntegrable
      (fun r => ψ r * radialJacobi ((j : ℝ) ^ 2) D.w η r) volume D.a D.b :=
    (hψ.continuous.continuousOn.mul
      (matchingJacobi_continuousOn hD hη j)).intervalIntegrable_of_Icc hg.2.1.le
  have hi₂ : IntervalIntegrable
      (fun r => η r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) volume D.a D.b :=
    (hη.continuous.continuousOn.mul
      (matchingJacobi_continuousOn hD hψ j)).intervalIntegrable_of_Icc hg.2.1.le
  have hgreen := integral_radialJacobi_green
    (J := (j : ℝ) ^ 2) (w := D.w) (u := ψ) (v := η)
    (fun r _ => ⟨hw.differentiable (by simp) r,
      hψ.differentiable (by simp) r, hdψ.differentiable (by simp) r,
      hη.differentiable (by simp) r, hdη.differentiable (by simp) r⟩)
    (hi₁.sub hi₂)
  have hwa : D.w D.a = 0 := hg.2.2.1.2 D.a (Or.inl le_rfl)
  have hwb : D.w D.b = 0 := hg.2.2.1.2 D.b (Or.inr le_rfl)
  rw [intervalIntegral.integral_sub hi₁ hi₂] at hgreen
  simpa only [radialWronskian, hwa, hwb, zero_mul, sub_self, sub_eq_zero] using hgreen

theorem matchingTestPairs_symmetric {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (j : ℕ) {ψ η : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hη : ContDiff ℝ ∞ η)
    (s t : ℝ) :
    modePairing D (matchingTestInput D hD ψ hψ s)
      (matchingTestSource D hD hB j η hη t) =
    modePairing D (matchingTestSource D hD hB j ψ hψ s)
      (matchingTestInput D hD η hη t) := by
  have hpair (U F : RadialModePair D) : modePairing D U F = modePairing D F U := by
    unfold modePairing
    rw [real_inner_comm U.1 F.1, mul_comm U.2 F.2]
  rw [hpair (matchingTestSource D hD hB j ψ hψ s),
    matchingTestSource_pairing, matchingTestSource_pairing]
  dsimp only [matchingTestInput]
  rw [matchingSmoothVector_jacobi_symm hD j hψ hη]
  by_cases hj : j = 2
  · simp only [hj, if_pos, ite_true, matchingSmoothVector_border_pairing hD hB hψ,
      matchingSmoothVector_border_pairing hD hB hη]
    ring
  · simp only [hj, if_neg, ite_false]
    ring

/-- The concrete source of every smooth core input satisfies the actual
extended weak graph. No limit at a singular endpoint is needed: the smooth
profile vanishes at both endpoints of the finite Green identity. -/
theorem matchingTestPair_mem_extendedGraph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (j : ℕ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    ModeExtendedGraph D j (matchingTestInput D hD ψ hψ s)
      (matchingTestSource D hD hB j ψ hψ s) := by
  apply (modeExtendedGraph_iff_core_pairings hD hB j _ _).mpr
  intro η hη hc hs t
  exact matchingTestPairs_symmetric hD hB j hψ hη s t

end ContinuousFlexibility.Radial
