import ContinuousFlexibility.Analysis.N05ReferenceAuxiliary
import ContinuousFlexibility.Radial.ReferenceCommonInverse

/-!
# Physical graph uniqueness for equal source representatives

Actual positive-weight membership gives the integrability required to change
source representatives in the iterated weak pairing. The fixed physical
inverse then identifies the height and metric scalar. Normalization of the
auxiliary source column also identifies its scalar.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open ContinuousFlexibility.Radial

theorem n05_referenceGraph_source_congr_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M0 M1 : ℝ} (hγ : 0 < γ)
    {U : RadialUnknown} {F F' : RadialSource}
    (hUF : ReferenceGraph D γ M0 M1 U F)
    (hF' : SourceMember D γ M0 F')
    (hscalar : F.2 = F'.2) (hsource : F.1 =ᵐ[radialPhysicalMeasure D] F'.1) :
    ReferenceGraph D γ M0 M1 U F' := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hf := r11b_source_memLp hD hγ hUF.2.1
  have hf' := r11b_source_memLp hD hγ hF'
  refine ⟨hUF.1, hF', hUF.2.2.1.trans hscalar, fun φ hφ => ?_⟩
  have hφL := r11b_continuous_memLp (D := D) hφ.1.continuous
  have he : (fun p => F.1 p * φ p) =ᵐ[radialPhysicalMeasure D]
      (fun p => F'.1 p * φ p) := by
    filter_upwards [hsource] with p hp
    rw [hp]
  exact (hUF.2.2.2 φ hφ).trans
    (r11b_integral_angularMean_congr_ae hab
      (hf.integrable_mul hφL) (hf'.integrable_mul hφL) he)

/-- Equality of source representatives is enough for uniqueness; pointwise
parity and periodicity are retained from each actual source membership. -/
theorem n05_referenceGraph_unique_source_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M0 M1 : ℝ} (hγ : 0 < γ)
    {G : RadialSource → RadialUnknown} (hG : ReferenceInverseProperties D γ M0 M1 G)
    {U V : RadialUnknown} {F F' : RadialSource}
    (hUF : ReferenceGraph D γ M0 M1 U F)
    (hVF : ReferenceGraph D γ M0 M1 V F')
    (hscalar : F.2 = F'.2) (hsource : F.1 =ᵐ[radialPhysicalMeasure D] F'.1) :
    RadialRepresentativeEq D U V := by
  have hVF' := n05_referenceGraph_source_congr_ae hD hγ hVF hUF.2.1
    hscalar.symm hsource.symm
  exact (hG.2.1 U F hUF).symm.trans (hG.2.1 V F hVF')

/-- The physical equation and the normalized auxiliary column determine
both the auxiliary scalar and the original physical inverse output. -/
theorem n05_augmentedReferenceGraph_unique_source_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M0 M1 : ℝ} (hγ : 0 < γ)
    {G : RadialSource → RadialUnknown} (hG : ReferenceInverseProperties D γ M0 M1 G)
    {ψ f g : PolarPoint → ℝ} {a b : ℝ} {U V : RadialUnknown}
    (hψ : (∫ r in D.a..D.b, radialAngularMean (fun θ => ψ (r, θ))) = 1)
    (hfg : f =ᵐ[radialPhysicalMeasure D] g)
    (hU : ReferenceGraph D γ M0 M1 U ((fun p => f p - a * ψ p), 0))
    (hV : ReferenceGraph D γ M0 M1 V ((fun p => g p - b * ψ p), 0)) :
    a = b ∧ RadialRepresentativeEq D U V := by
  have hab := n05_referenceAuxiliaryScalar_unique hD hγ hγ hψ hfg hU.2.1 hV.2.1
  refine ⟨hab, n05_referenceGraph_unique_source_ae hD hγ hG hU hV rfl ?_⟩
  filter_upwards [hfg] with p hp
  change f p - a * ψ p = g p - b * ψ p
  rw [hp, hab]

end ContinuousFlexibility.Statements
