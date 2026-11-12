import ContinuousFlexibility.Radial.ReferenceOutputCosineCoordinates
import ContinuousFlexibility.Radial.ReferenceCosineGraphSufficiency
import ContinuousFlexibility.Radial.ReferenceRadialKernelPairing
import ContinuousFlexibility.Radial.ModeLocalMeasure

/-!
# The actual graph of cosine synthesis

The prescribed radial coefficients are compared with the true angular
coefficients in the actual weighted measure. Equivalence of null sets
then transfers their equations and the border row to ordinary interval
integrals. Thus the synthesized field satisfies every frozen radial test.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

theorem referenceOutputCosine_graph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ aL ν : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M₀ F)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁))) 2)
    (hrow : (∫ r in D.a..D.b, referenceColumn D r * a 1 r) = F.2)
    (hmode : ∀ (n : ℕ) (φ : ℝ → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ radialCore D →
      (∫ r in D.a..D.b,
        ((if n = 0 then aL * D.chiLeft r else 0) + a n r) *
          Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r) +
        (if n = 1 then ν else 0) *
          (∫ r in D.a..D.b, referenceColumn D r * φ r) =
      ∫ r in D.a..D.b, referenceCosineCoefficient F.1 n r * φ r) :
    ReferenceGraph D γ M₀ M₁ (referenceOutputCosine D γ M₁ aL ν a) F := by
  have hP : RadialPartition D := hD.choose_spec.2.1
  have hab : D.a ≤ D.b := (Radial.matchingProfileGeometry hD).2.1.le
  have hcoef (n : ℕ) :
      referenceCosineCoefficient (referenceOutputCosine D γ M₁ aL ν a).1 n
        =ᵐ[radialHilbertMeasure D]
          fun r => (if n = 0 then aL * D.chiLeft r else 0) + a n r :=
    (Radial.radialHilbertMeasure_ae_iff hD).mpr
      ((referenceRadialWeightedMeasure_ae_iff hP γ (-M₁)).mp
        (referenceOutputCosine_coefficient_ae D γ M₁ aL ν a n))
  apply referenceGraph_of_cosine_weak_equations hD hB
    ⟨aL, referenceOutputCosine_realization hab hP γ M₁ aL ν a⟩ hF
  · change (∫ r in D.a..D.b, referenceColumn D r *
      referenceMode (referenceOutputCosine D γ M₁ aL ν a).1 2 r) = F.2
    calc
      _ = ∫ r in D.a..D.b, referenceColumn D r * a 1 r := by
        apply Radial.matchingInterval_congr_ae hD
        have hc : referenceMode (referenceOutputCosine D γ M₁ aL ν a).1 2
            =ᵐ[radialHilbertMeasure D] a 1 :=
          (Radial.radialHilbertMeasure_ae_iff hD).mpr
            ((referenceRadialWeightedMeasure_ae_iff hP γ (-M₁)).mp
              (referenceOutputCosine_referenceMode_ae D γ M₁ aL ν a 0))
        filter_upwards [hc] with r hr
        rw [hr]
      _ = F.2 := hrow
  · intro n φ hφ hcφ hsφ
    have hi :
        (∫ r in D.a..D.b,
          referenceCosineCoefficient (referenceOutputCosine D γ M₁ aL ν a).1 n r *
            Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r) =
        ∫ r in D.a..D.b,
          ((if n = 0 then aL * D.chiLeft r else 0) + a n r) *
            Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r := by
      apply Radial.matchingInterval_congr_ae hD
      filter_upwards [hcoef n] with r hr
      rw [hr]
    change (∫ r in D.a..D.b,
        referenceCosineCoefficient (referenceOutputCosine D γ M₁ aL ν a).1 n r *
          Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w φ r) +
        (if n = 1 then ν else 0) *
          (∫ r in D.a..D.b, referenceColumn D r * φ r) = _
    rw [hi]
    exact hmode n φ hφ hcφ hsφ

end ContinuousFlexibility.Statements
