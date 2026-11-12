import ContinuousFlexibility.Analysis.N05ReferenceNormalization
import ContinuousFlexibility.Radial.R11bAngularL2Bridge
import ContinuousFlexibility.Radial.R11bCompactSources

/-!
# Compatibility of the actual physical source after its auxiliary correction

The prescribed normalizer has compact radial support and hence every
reference source weight. Positive-weight membership of an arbitrary even
periodic source supplies actual physical integrability. Subtracting its
normalized integral times that column then gives the literal compatible
source class required by the physical inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Radial

theorem n05_compact_annular_continuous {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    (hsupp : HasCompactRadialSupport D f) : Continuous f := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := hsupp
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ annularOpen D
  · exact hf.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  · have hpJ : p.1 ∉ J := fun h => hp ⟨hJcore h, mem_univ _⟩
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ J :=
      (hJ.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpJ
    have heq : f =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnear] with q hq
      exact hzero q.1 hq q.2
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- The actual auxiliary source column lies in every reference source
weight, independently of the endpoint and material exponents. -/
theorem n05_physicalNormalizer_sourceDerivativeMember
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S) (γ M : ℝ) :
    SourceDerivativeMember D γ M ((S.height (3 / 4 : ℝ)).decode S.psi) := by
  have hψ := (hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi
  have hsupp : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode S.psi) := by
    rcases hS with ⟨_, _, _, _, _, _, _, _, hsupp, _⟩
    exact hsupp
  have hc := n05_compact_annular_continuous hψ.1.continuousOn hsupp
  obtain ⟨J, hJ, hJcore, hzero⟩ := hsupp
  exact r11b_compact_sourceDerivativeMember hD hJ hJcore hc
    (fun r _ hr => hzero r hr) γ M

theorem n05_referenceMean_intervalIntegrable {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    IntervalIntegrable (fun r => radialAngularMean (fun θ => f (r, θ)))
      volume D.a D.b := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    dsimp only [radialCore]
    infer_instance
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
    ((r11b_radialAngularMean_L2_bound hf).1.integrable (by norm_num))

/-- The actual physical integral removes the source obstruction. The
input need not satisfy any compatibility condition. -/
theorem n05_referenceSource_normalized_member
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    {γ M : ℝ} (hγ : 0 < γ) {f : PolarPoint → ℝ}
    (hf : SourceDerivativeMember D γ M f)
    (hperiodic : Function.Periodic f (0, Real.pi))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ)) :
    SourceMember D γ M
      ((fun p => f p -
        (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) *
          (S.height (3 / 4 : ℝ)).decode S.psi p), 0) := by
  let ψ : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode S.psi
  let a : ℝ := ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))
  have hψ := n05_physicalNormalizer_sourceDerivativeMember hD hS γ M
  have hψheight := (hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi
  have hψnorm : (∫ r in D.a..D.b, radialAngularMean (fun θ => ψ (r, θ))) = 1 :=
    n05_physicalSpaces_normalizer_referenceIntegral hS
  have hab := hD.choose_spec.1.2.1.le
  have hcorrected : SourceDerivativeMember D γ M (fun p => f p - a * ψ p) := by
    have heq : (fun p => f p - a * ψ p) = (fun p => f p + (-a) * ψ p) := by
      funext p
      ring
    rw [heq]
    exact ⟨hf.1.add (hψ.1.const_mul (-a)),
      sourceCellSquare_summable_add hab hf.1 (hψ.1.const_mul (-a)) hf.2
        (sourceCellSquare_summable_const_mul hψ.2 (-a))⟩
  have hcorrectedLp := r11b_sourceDerivative_memLp hD hγ hcorrected
  change SourceMember D γ M ((fun p => f p - a * ψ p), 0)
  refine ⟨hcorrected.1, hcorrected.2, ?_, ?_,
    n05_referenceMean_intervalIntegrable hab hcorrectedLp, ?_⟩
  · intro p
    change f (p + (0, Real.pi)) - a * ψ (p + (0, Real.pi)) = f p - a * ψ p
    rw [hperiodic p, show ψ (p + (0, Real.pi)) = ψ p from hψheight.2.2.1 p]
  · intro r θ
    change f (r, -θ) - a * ψ (r, -θ) = f (r, θ) - a * ψ (r, θ)
    rw [heven r θ, show ψ (r, -θ) = ψ (r, θ) from hψheight.2.1 r θ]
  · letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
      ⟨r11b_radialPhysicalMeasure_finite D⟩
    have hi := (r11b_sourceDerivative_memLp hD hγ hf).integrable (by norm_num)
    have hψi : Integrable ψ (radialPhysicalMeasure D) :=
      (r11b_sourceDerivative_memLp hD hγ hψ).integrable (by norm_num)
    have ha : a = (2 * Real.pi)⁻¹ * ∫ p, f p ∂radialPhysicalMeasure D :=
      r11b_integral_angularMean_eq hab hi
    have hψiNorm : (2 * Real.pi)⁻¹ * ∫ p, ψ p ∂radialPhysicalMeasure D = 1 :=
      (r11b_integral_angularMean_eq hab hψi).symm.trans hψnorm
    calc
      _ = (2 * Real.pi)⁻¹ *
          ∫ p, (f p - a * ψ p) ∂radialPhysicalMeasure D :=
        r11b_integral_angularMean_eq hab (hi.sub (hψi.const_mul a))
      _ = (2 * Real.pi)⁻¹ *
          ((∫ p, f p ∂radialPhysicalMeasure D) -
            a * ∫ p, ψ p ∂radialPhysicalMeasure D) := by
        rw [integral_sub hi (hψi.const_mul a), integral_const_mul]
      _ = a - a * 1 := by
        rw [mul_sub, show (2 * Real.pi)⁻¹ *
            (a * ∫ p, ψ p ∂radialPhysicalMeasure D) =
            a * ((2 * Real.pi)⁻¹ * ∫ p, ψ p ∂radialPhysicalMeasure D) by ring,
          ← ha, hψiNorm]
      _ = 0 := by ring

end ContinuousFlexibility.Statements
