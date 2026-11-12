import ContinuousFlexibility.Radial.ReferenceCosineLocalPairing

/-!
# Sufficiency of the actual modal weak equations

The mode equations are tested with the genuine smooth angular
coefficients of an arbitrary two-dimensional test. Their convergent
paired series sum to the frozen distributional equation. The border
contributes precisely the single physical frequency-two coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem referenceColumn_test_eq_first_coefficient (D : ReferenceData)
    (ψ : PolarPoint → ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceColumn D r * Radial.cosineMode 2 θ * ψ (r, θ))) =
      ∫ r in D.a..D.b, referenceColumn D r * referenceCosineCoefficient ψ 1 r := by
  apply intervalIntegral.integral_congr
  intro r _
  change radialAngularMean (fun θ =>
    referenceColumn D r * Radial.cosineMode 2 θ * ψ (r, θ)) =
      referenceColumn D r * referenceCosineCoefficient ψ 1 r
  rw [referenceCosineCoefficient_eq_angularMean]
  have hk (θ : ℝ) :
      referenceCircleCosine 1 (θ : AddCircle Real.pi) = Radial.cosineMode 2 θ := by
    simpa using referenceCircleCosine_succ_coe 0 θ
  simp only [hk]
  have heq : (fun θ : ℝ =>
      referenceColumn D r * Radial.cosineMode 2 θ * ψ (r, θ)) =
      (fun θ => referenceColumn D r * (ψ (r, θ) * Radial.cosineMode 2 θ)) := by
    funext θ
    ring
  rw [heq, radialAngularMean_const_mul]

/-- The actual zero and positive even mode equations imply the complete frozen weak graph. -/
theorem referenceGraph_of_cosine_weak_equations {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hU : OutputMember D γ M₁ U) (hF : SourceMember D γ M₀ F)
    (hrow : referenceRow D U.1 = F.2)
    (hmode : ∀ (n : ℕ) (φ : ℝ → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ radialCore D →
      (∫ r in D.a..D.b, referenceCosineCoefficient U.1 n r *
        Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r) +
          (if n = 1 then U.2 else 0) *
            (∫ r in D.a..D.b, referenceColumn D r * φ r) =
      ∫ r in D.a..D.b, referenceCosineCoefficient F.1 n r * φ r) :
    ReferenceGraph D γ M₀ M₁ U F := by
  refine ⟨hU, hF, hrow, ?_⟩
  intro ψ hψ
  obtain ⟨aL, hUa⟩ := hU
  have hUl : RadialCellIntegrable D U.1 :=
    (show OutputMember D γ M₁ U from ⟨aL, hUa⟩).radialCellIntegrable hD hB
  have hsU := hUl.cosine_testOperator_pairing_hasSum hD hUa.2.2.1 hUa.2.2.2 hψ
  have hsF := hF.1.cosine_test_pairing_hasSum hD hF.2.2.1 hF.2.2.2.1 hψ
  let B : ℝ := U.2 *
    (∫ r in D.a..D.b, referenceColumn D r * referenceCosineCoefficient ψ 1 r)
  have hsB : HasSum (fun n : ℕ => if n = 1 then B else 0) B :=
    hasSum_ite_eq 1 B
  have hterm (n : ℕ) :
      (∫ r in D.a..D.b, referenceCosineCoefficient U.1 n r *
        Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w
          (referenceCosineCoefficient ψ n) r) +
        (if n = 1 then B else 0) =
      ∫ r in D.a..D.b,
        referenceCosineCoefficient F.1 n r * referenceCosineCoefficient ψ n r := by
    obtain ⟨hφ, hcφ, hsφ⟩ := hψ.cosineCoefficient_test n
    have hm := hmode n (referenceCosineCoefficient ψ n) hφ hcφ hsφ
    by_cases hn : n = 1
    · subst n
      simpa only [ite_true, B] using hm
    · simpa only [ite_eq_right hn, zero_mul, add_zero] using hm
  have hs := hsU.add hsB
  change HasSum (fun n : ℕ =>
    (∫ r in D.a..D.b, referenceCosineCoefficient U.1 n r *
      Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w
        (referenceCosineCoefficient ψ n) r) +
      (if n = 1 then B else 0)) (radialWeakPairing D U.1 ψ + B) at hs
  have hs' : HasSum (fun n : ℕ => ∫ r in D.a..D.b,
      referenceCosineCoefficient F.1 n r * referenceCosineCoefficient ψ n r)
      (radialWeakPairing D U.1 ψ + B) := by
    simpa only [hterm] using hs
  rw [referenceColumn_test_eq_first_coefficient]
  exact hs'.unique hsF

end ContinuousFlexibility.Statements
