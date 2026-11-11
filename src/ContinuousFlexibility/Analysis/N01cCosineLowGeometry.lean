import ContinuousFlexibility.Analysis.N01cCosineAngularJets
import ContinuousFlexibility.Analysis.N01cSpeedLowBounds
import ContinuousFlexibility.Analysis.OneHighCircleFlowReferenceNorms

/-!
# Uniform low geometry of the actual compact component speeds

The physical speed difference contributes one bounded cosine velocity
factor. The circle norms below are the actual canonical angular jets.
The mean reference speed disappears before estimating any norm, so it
does not enter the constants that control the flow geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

theorem circleFlowSubtractJet_coe_apply
    {P : ℝ} [Fact (0 < P)] (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (c : ℝ → ℝ) (t : ℝ) (n : ℕ) (θ : ℝ) :
    circleSubtractConstantJet (circleFlowSpeedJet G hG hperiod t) (c t) n
      (θ : AddCircle P) = iteratedDeriv n (fun η => G (t, η) - c t) θ := by
  change circleSubtractConstantJet
    (periodicCircleJet (fun η => G (t, η)) (hperiod t)
      (hG.comp (contDiff_const.prodMk contDiff_id))) (c t) n (θ : AddCircle P) = _
  rw [periodicCircleJet_sub_const, periodicCircleJet_coe_apply]

/-- A pointwise bound on the genuine endpoint angular jets gives the
integrated reference norm, with no dependence on the mean velocity. -/
theorem circleFlowReferenceSize_le_of_uniformJetBounds
    {P : ℝ} [Fact (0 < P)] (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    {c : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hc : IntervalIntegrable c volume a b) (s : ℕ) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc a b, ∀ n, n ≤ s → ∀ θ : ℝ,
      |iteratedDeriv n (fun η => G (t, η) - c t) θ| ≤ M) :
    circleFlowReferenceSize G hG hperiod c s a b ≤
      (b - a) * (2 : ℝ) ^ s * (M + M) := by
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      circleFlowReferenceNorm G hG hperiod c s t ≤ (2 : ℝ) ^ s * (M + M) := by
    apply circle_sobolevNorm_le_pointwiseJetBounds
      (circleSubtractConstantJet (circleFlowSpeedJet G hG hperiod t) (c t))
      (circleSubtractConstantJet_hasDerivAt (circleFlowSpeedJet G hG hperiod t)
        (circleFlowSpeedJet_hasDerivAt G hG hperiod t) (c t)) s hM hM
    · intro θ
      rw [circleFlowSubtractJet_coe_apply]
      exact hb t ht 0 (Nat.zero_le _) θ
    · intro θ
      rw [circleFlowSubtractJet_coe_apply]
      exact hb t ht s le_rfl θ
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_circleFlowReferenceNorm G hG hperiod hab hc s)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (2 : ℝ) ^ s * (M + M)) volume a b) hpoint
  simpa only [circleFlowReferenceSize, intervalIntegral.integral_const,
    smul_eq_mul, mul_assoc] using hi

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem componentCosineSpeed_difference_eq_zero_of_sin_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (z : AnnularState S × ℝ) (m : ℕ) {t : ℝ} (ht : Real.sin t = 0) :
    (fun η : ℝ => componentCosineSpeed D S C m (z, (t, η)) -
      componentCosineSpeed D S C m ((C.referenceState, 0), (t, η))) = 0 := by
  funext η
  simp only [componentCosineSpeed, cosineRegularizedSpeed, ht, mul_zero,
    neg_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.zero_apply]

/-- One uniform fixed-order physical bound controls every component's
reference-subtracted cosine speed, including both actual root values. -/
theorem componentCosineSpeedDifference_jet_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base s : ℕ} {ε M : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hM : 0 ≤ M)
    (hbound : ∀ m n p, n ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      |characteristicSpeedFamily D S C 0 n p z| ≤ M)
    (m n : ℕ) (hn : n ≤ s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) (θ : ℝ) :
    |iteratedDeriv n (fun η => componentCosineSpeed D S C m (z, (t, η)) -
      componentCosineSpeed D S C m ((C.referenceState, 0), (t, η))) θ| ≤
        (D.b - D.a) / 2 * M := by
  have hC := hA.2.2.1
  have hwidth : 0 < D.b - D.a := sub_pos.mpr
    ((hC.1 m).1.trans ((hC.1 m).2.1.trans (hC.1 m).2.2))
  have hright : 0 ≤ (D.b - D.a) / 2 * M := mul_nonneg (by positivity) hM
  by_cases hzero : t = 0
  · subst t
    rw [componentCosineSpeed_difference_eq_zero_of_sin_zero z m Real.sin_zero,
      iteratedDeriv_const_zero, abs_zero]
    exact hright
  by_cases hpi : t = Real.pi
  · subst t
    rw [componentCosineSpeed_difference_eq_zero_of_sin_zero z m Real.sin_pi,
      iteratedDeriv_const_zero, abs_zero]
    exact hright
  have hti : t ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hpi⟩
  rw [iteratedDeriv_componentCosineSpeed_difference hS hT hA hε hB hz m n hti θ,
    abs_mul]
  have hlength : 0 ≤ (C.right m - C.left m) / 2 := by
    exact div_nonneg (sub_nonneg.mpr (hC.1 m).2.1.le) (by norm_num)
  have hvelocity : |(C.right m - C.left m) / 2 * Real.sin t| ≤ (D.b - D.a) / 2 := by
    rw [abs_mul, abs_of_nonneg hlength]
    calc
      _ ≤ ((C.right m - C.left m) / 2) * 1 :=
        mul_le_mul_of_nonneg_left (abs_le.mpr ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩)
          hlength
      _ ≤ (D.b - D.a) / 2 := by
        have hl := (hC.1 m).1
        have hh := (hC.1 m).2.2
        nlinarith
  exact mul_le_mul hvelocity
    (hbound m n (rootCosinePath (C.left m) (C.right m) t, θ) hn
      (rootCosinePath_mem_Ioo (hC.1 m).2.1 hti))
    (abs_nonneg _) (div_nonneg hwidth.le (by norm_num))

/-- The fixed physical order controls the actual integrated circle norm
for every component. Its constant only uses the full radial width. -/
theorem componentCosineSpeed_referenceSize_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base s : ℕ} {ε M : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hM : 0 ≤ M)
    (hbound : ∀ m n p, n ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      |characteristicSpeedFamily D S C 0 n p z| ≤ M)
    (m : ℕ)
    (hG : ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)))
    (hG₀ : Continuous (fun t => componentCosineSpeed D S C m
      ((C.referenceState, 0), (t, 0)))) :
    circleFlowReferenceSize
      (fun p => componentCosineSpeed D S C m (z, p)) hG
      (componentCosineSpeed_periodic hS z m)
      (fun t => componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0)))
      s 0 Real.pi ≤ Real.pi * (2 : ℝ) ^ s * ((D.b - D.a) * M) := by
  have hwidth : 0 < D.b - D.a := sub_pos.mpr
    ((hA.2.2.1.1 m).1.trans ((hA.2.2.1.1 m).2.1.trans (hA.2.2.1.1 m).2.2))
  have hi := circleFlowReferenceSize_le_of_uniformJetBounds
    (M := (D.b - D.a) / 2 * M)
    (fun p => componentCosineSpeed D S C m (z, p)) hG
    (componentCosineSpeed_periodic hS z m) Real.pi_pos.le
    (hG₀.intervalIntegrable 0 Real.pi) s
    (mul_nonneg (div_nonneg hwidth.le (by norm_num)) hM)
    (fun t ht n hn θ => by
      have he : (fun η => componentCosineSpeed D S C m (z, (t, η)) -
          componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0))) =
          fun η => componentCosineSpeed D S C m (z, (t, η)) -
            componentCosineSpeed D S C m ((C.referenceState, 0), (t, η)) := by
        funext η
        rw [componentCosineSpeed_reference_angle hS hT hA hε hB m t η]
      rw [he]
      exact componentCosineSpeedDifference_jet_le hS hT hA hε hB hz hM hbound m n hn ht θ)
  convert hi using 1 <;> ring

end ContinuousFlexibility.Statements
