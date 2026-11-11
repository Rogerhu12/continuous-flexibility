import ContinuousFlexibility.Radial.ReferenceCosineBoundedSynthesis
import ContinuousFlexibility.Radial.ReferenceCosineSynthesisGraph
import ContinuousFlexibility.Radial.ReferenceSourceEnergy

/-!
# Assembling the actual zero and positive radial solutions

The zero mode supplies the left height. Every positive mode supplies a
radial L² vector; only the first carries the scalar border. Their genuine
weak equations and a common energy estimate produce an actual field in
the full frozen weak graph, with the exact frozen output norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

theorem referenceSolution_of_radial_modes {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ K aL ν : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M₀ F) (hK : 0 ≤ K)
    (z : ℝ → ℝ)
    (hz : MemLp (fun r => z r - aL * D.chiLeft r) 2
      (referenceRadialWeightedMeasure D γ (-M₁)))
    (u : ℕ → Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁)))
    (hzbound : aL ^ 2 +
      (∫ r, (z r - aL * D.chiLeft r) ^ 2
        ∂referenceRadialWeightedMeasure D γ (-M₁)) ≤
      K * ‖referenceSourceCosineAnalysis
        (Radial.matchingProfileGeometry hD).2.1.le hD.choose_spec.2.1 hF 0‖ ^ 2)
    (hubound : ∀ n : ℕ, ‖u n‖ ^ 2 + (if n = 0 then ν ^ 2 else 0) ≤
      K * (‖referenceSourceCosineAnalysis
        (Radial.matchingProfileGeometry hD).2.1.le hD.choose_spec.2.1 hF (n + 1)‖ ^ 2 +
        if n = 0 then F.2 ^ 2 else 0))
    (hrow : (∫ r in D.a..D.b, referenceColumn D r * u 0 r) = F.2)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
      (∫ r in D.a..D.b, z r * Radial.radialJacobi 0 D.w φ r) =
        ∫ r in D.a..D.b, referenceCosineCoefficient F.1 0 r * φ r)
    (hpositive : ∀ (n : ℕ) (φ : ℝ → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ radialCore D →
      (∫ r in D.a..D.b, u n r *
        Radial.radialJacobi (((2 * (n + 1) : ℕ) : ℝ) ^ 2) D.w φ r) +
        (if n = 0 then ν else 0) *
          (∫ r in D.a..D.b, referenceColumn D r * φ r) =
      ∫ r in D.a..D.b, referenceCosineCoefficient F.1 (n + 1) r * φ r) :
    ∃ U : RadialUnknown,
      ReferenceGraph D γ M₀ M₁ U F ∧ OutputRealization D γ M₁ aL U ∧
        outputNormSquare D γ M₁ aL U ≤ (3 * K) * sourceNormSquare D γ M₀ F := by
  have hab : D.a ≤ D.b := (Radial.matchingProfileGeometry hD).2.1.le
  have hP : RadialPartition D := hD.choose_spec.2.1
  let v : ℕ → Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁))
    | 0 => hz.toLp (fun r => z r - aL * D.chiLeft r)
    | n + 1 => u n
  have hIz : 0 ≤ ∫ r, (z r - aL * D.chiLeft r) ^ 2
      ∂referenceRadialWeightedMeasure D γ (-M₁) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have haL : aL ^ 2 ≤ K * sourceNormSquare D γ M₀ F := by
    have hi := mul_le_mul_of_nonneg_left
      (referenceSourceCosineAnalysis_coordinate_le hab hP hF 0) hK
    linarith only [hzbound, hIz, hi]
  have hν : ν ^ 2 ≤ K * sourceNormSquare D γ M₀ F := by
    have hb := hubound 0
    simp only [if_pos rfl, ite_true, Nat.zero_add] at hb
    have hi := mul_le_mul_of_nonneg_left
      (referenceSourceCosineAnalysis_coordinate_scalar_le hab hP hF 1) hK
    linarith only [hb, hi, sq_nonneg ‖u 0‖]
  have hv (n : ℕ) : ‖v n‖ ^ 2 ≤
      K * (‖referenceSourceCosineAnalysis hab hP hF n‖ ^ 2 +
        if n = 1 then F.2 ^ 2 else 0) := by
    cases n with
    | zero =>
        change ‖hz.toLp (fun r => z r - aL * D.chiLeft r)‖ ^ 2 ≤ _
        rw [referenceL2_toLp_norm_sq]
        simp only [if_neg (by decide : (0 : ℕ) ≠ 1), add_zero]
        linarith only [hzbound, sq_nonneg aL]
    | succ n =>
        have hb := hubound n
        have he : (if n + 1 = 1 then F.2 ^ 2 else 0) =
            (if n = 0 then F.2 ^ 2 else 0) := by
          by_cases hn : n = 0
          · subst n; rfl
          · rw [if_neg (by omega), if_neg hn]
        change ‖u n‖ ^ 2 ≤
          K * (‖referenceSourceCosineAnalysis hab hP hF (n + 1)‖ ^ 2 +
            if n + 1 = 1 then F.2 ^ 2 else 0)
        rw [he]
        have hs : 0 ≤ if n = 0 then ν ^ 2 else 0 := by
          split_ifs <;> positivity
        linarith only [hb, hs]
  obtain ⟨a, ha, hreal, hnorm⟩ :=
    referenceCosine_bounded_synthesis hab hP hF v hK haL hν hv
  have ha0 : a 0 = hz.toLp (fun r => z r - aL * D.chiLeft r) := ha 0
  have has (n : ℕ) : a (n + 1) = u n := ha (n + 1)
  refine ⟨referenceOutputCosine D γ M₁ aL ν a, ?_, hreal, hnorm⟩
  apply referenceOutputCosine_graph hD hB hF a
  · change (∫ r in D.a..D.b, referenceColumn D r * a (0 + 1) r) = F.2
    rw [has 0]
    exact hrow
  · intro n φ hφ hcφ hsφ
    cases n with
    | zero =>
        simp only [if_pos rfl, ite_true, if_neg (by decide : (0 : ℕ) ≠ 1), ite_false,
          Nat.mul_zero, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
          zero_mul, add_zero]
        calc
          _ = ∫ r in D.a..D.b, z r * Radial.radialJacobi 0 D.w φ r := by
            apply Radial.matchingInterval_congr_ae hD
            have hae : (a 0 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
                fun r => z r - aL * D.chiLeft r := by
              rw [ha0]
              exact (Radial.radialHilbertMeasure_ae_iff hD).mpr
                ((referenceRadialWeightedMeasure_ae_iff hP γ (-M₁)).mp hz.coeFn_toLp)
            filter_upwards [hae] with r hr
            rw [hr]
            ring
          _ = _ := hzero φ hφ hcφ hsφ
    | succ n =>
        simp only [if_neg (show n + 1 ≠ 0 by omega), ite_false, zero_add, has n]
        have he : (if n + 1 = 1 then ν else 0) = (if n = 0 then ν else 0) := by
          by_cases hn : n = 0
          · subst n; rfl
          · rw [if_neg (by omega), if_neg hn]
        rw [he]
        exact hpositive n φ hφ hcφ hsφ

end ContinuousFlexibility.Statements
