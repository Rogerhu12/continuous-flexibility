module

public import ContinuousFlexibility.Radial.ReferenceSourceCosine

/-!
# Actual coordinates and uniqueness of cosine reconstruction

Analysis recovers every radial input mode of the synthesized physical
representative. Conversely, equality of the actual angular coefficients
implies physical almost-everywhere equality. The last result uses only
the frozen local cell L² condition, so it also applies to output fields
whose left constant is not in the weighted remainder space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

section Product

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem referenceCosineAnalysis_representative
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    referenceCosineAnalysis (referenceCosineRepresentative_memLp a)
      (referenceCosineRepresentative_periodic a)
      (referenceCosineRepresentative_even a) = a := by
  apply (referencePhysicalCosineL2Synthesis (μ := μ)).injective
  rw [referencePhysicalCosineL2Synthesis_analysis, referenceCosineRepresentative_toLp]
  rfl

/-- The actual angular integral of a synthesized field is the prescribed radial mode. -/
theorem referenceCosineCoefficient_representative_ae
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) (n : ℕ) :
    referenceCosineCoefficient (referenceCosineRepresentative a) n =ᵐ[μ] a n := by
  have hh := referenceCosineAnalysisCoeff_ae (referenceCosineRepresentative_memLp a)
    (referenceCosineRepresentative_periodic a) (referenceCosineRepresentative_even a) n
  have hn := congrArg (fun b : lp (fun _ : ℕ => Lp ℝ 2 μ) 2 => b n)
    (referenceCosineAnalysis_representative a)
  change referenceCosineAnalysisCoeff (referenceCosineRepresentative_memLp a)
    (referenceCosineRepresentative_periodic a)
    (referenceCosineRepresentative_even a) n = a n at hn
  rw [hn] at hh
  exact hh.symm

theorem referenceCosineCoefficients_ae_injective {f g : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hg : MemLp g 2 (μ.prod referenceAngularMeasure))
    (hfp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (hgp : ∀ r, Function.Periodic (fun θ => g (r, θ)) Real.pi)
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hge : ∀ r θ, g (r, -θ) = g (r, θ))
    (hc : ∀ n : ℕ, referenceCosineCoefficient f n =ᵐ[μ] referenceCosineCoefficient g n) :
    f =ᵐ[μ.prod referenceAngularMeasure] g := by
  have ha : referenceCosineAnalysis hf hfp hfe = referenceCosineAnalysis hg hgp hge := by
    apply lp.ext
    funext n
    apply Lp.ext
    exact (referenceCosineAnalysisCoeff_ae hf hfp hfe n).trans
      ((hc n).trans (referenceCosineAnalysisCoeff_ae hg hgp hge n).symm)
  have hv := congrArg (referencePhysicalCosineL2Synthesis (μ := μ)) ha
  rw [referencePhysicalCosineL2Synthesis_analysis,
    referencePhysicalCosineL2Synthesis_analysis] at hv
  have hr := hf.coeFn_toLp
  rw [hv] at hr
  exact hr.symm.trans hg.coeFn_toLp

end Product

theorem referenceMode_cosineRepresentative_ae {μ : Measure ℝ} [SFinite μ]
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) (n : ℕ) :
    referenceMode (referenceCosineRepresentative a) (2 * (n + 1)) =ᵐ[μ] a (n + 1) := by
  rw [← referenceCosineCoefficient_succ_eq_referenceMode]
  exact referenceCosineCoefficient_representative_ae a (n + 1)

theorem OutputRealization.remainder_angular_periodic {D : ReferenceData}
    {γ M aL : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M aL U) (r : ℝ) :
    Function.Periodic (fun θ => outputRemainder D aL U (r, θ)) Real.pi := by
  intro θ
  have hp := hU.2.2.1 (r, θ)
  change U.1 (r + 0, θ + Real.pi) = U.1 (r, θ) at hp
  simp only [add_zero] at hp
  change U.1 (r, θ + Real.pi) - aL * D.chiLeft r =
    U.1 (r, θ) - aL * D.chiLeft r
  rw [hp]

theorem OutputRealization.remainder_even {D : ReferenceData}
    {γ M aL : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M aL U) (r θ : ℝ) :
    outputRemainder D aL U (r, -θ) = outputRemainder D aL U (r, θ) := by
  change U.1 (r, -θ) - aL * D.chiLeft r = U.1 (r, θ) - aL * D.chiLeft r
  rw [hU.2.2.2 r θ]

/-- In particular, index zero gives the actual mean of the output remainder in radial L². -/
theorem OutputRealization.remainder_cosineCoefficient_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (n : ℕ) :
    MemLp (referenceCosineCoefficient (outputRemainder D aL U) n) 2
      (referenceRadialWeightedMeasure D γ (-M)) := by
  have hm := hU.memLp_weighted hab hD
  rw [referenceWeightedMeasure_eq_prod hD γ (-M)] at hm
  exact referenceCosineCoefficient_memLp hm
    hU.remainder_angular_periodic hU.remainder_even n

/-- Coefficient uniqueness needs only the actual local cell L² domain. -/
theorem RadialCellIntegrable.cosineCoefficients_ae_injective {D : ReferenceData}
    (hD : RadialPartition D) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hfp : Function.Periodic f (0, Real.pi))
    (hgp : Function.Periodic g (0, Real.pi))
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hge : ∀ r θ, g (r, -θ) = g (r, θ))
    (hc : ∀ n : ℕ,
      referenceCosineCoefficient f n =ᵐ[volume.restrict (radialCore D)]
        referenceCosineCoefficient g n) :
    f =ᵐ[radialPhysicalMeasure D] g := by
  have hprod :
      (volume.restrict (radialCore D)).prod referenceAngularMeasure =
        ENNReal.ofReal ((2 * Real.pi)⁻¹) • radialPhysicalMeasure D := by
    rw [referenceAngularMeasure, Measure.prod_smul_right, ← radialPhysicalMeasure_eq_prod]
  have hfprod (m : ℕ) :
      MemLp (fun x : PolarPoint => D.localizer m x.1 * f x) 2
        ((volume.restrict (radialCore D)).prod referenceAngularMeasure) := by
    rw [hprod]
    exact (hf m).smul_measure ENNReal.ofReal_ne_top
  have hgprod (m : ℕ) :
      MemLp (fun x : PolarPoint => D.localizer m x.1 * g x) 2
        ((volume.restrict (radialCore D)).prod referenceAngularMeasure) := by
    rw [hprod]
    exact (hg m).smul_measure ENNReal.ofReal_ne_top
  have hlocal (m : ℕ) :
      (fun x : PolarPoint => D.localizer m x.1 * f x) =ᵐ[radialPhysicalMeasure D]
        (fun x => D.localizer m x.1 * g x) := by
    have hff (r : ℝ) :
        Function.Periodic (fun θ => D.localizer m r * f (r, θ)) Real.pi := by
      intro θ
      have hp := hfp (r, θ)
      change f (r + 0, θ + Real.pi) = f (r, θ) at hp
      simpa only [add_zero] using congrArg (fun t : ℝ => D.localizer m r * t) hp
    have hgg (r : ℝ) :
        Function.Periodic (fun θ => D.localizer m r * g (r, θ)) Real.pi := by
      intro θ
      have hp := hgp (r, θ)
      change g (r + 0, θ + Real.pi) = g (r, θ) at hp
      simpa only [add_zero] using congrArg (fun t : ℝ => D.localizer m r * t) hp
    have heq := referenceCosineCoefficients_ae_injective (hfprod m) (hgprod m) hff hgg
      (fun r θ => congrArg (fun t : ℝ => D.localizer m r * t) (hfe r θ))
      (fun r θ => congrArg (fun t : ℝ => D.localizer m r * t) (hge r θ)) (fun n => by
        filter_upwards [hc n] with r hr
        change referenceCosineCoefficient (fun x => D.localizer m x.1 * f x) n r =
          referenceCosineCoefficient (fun x => D.localizer m x.1 * g x) n r
        rw [referenceCosineCoefficient_radial_mul, referenceCosineCoefficient_radial_mul, hr])
    rw [hprod] at heq
    exact (Measure.ae_ennreal_smul_measure_iff
      (by positivity : ENNReal.ofReal ((2 * Real.pi)⁻¹) ≠ 0)).mp heq
  have hall :
      ∀ᵐ x ∂radialPhysicalMeasure D, ∀ m : ℕ,
        D.localizer m x.1 * f x = D.localizer m x.1 * g x :=
    ae_all_iff.2 hlocal
  have hmem : ∀ᵐ x ∂radialPhysicalMeasure D,
      x ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hall, hmem] with x hx hxmem
  obtain ⟨m, hm⟩ := hD.exists_localizer_ne_zero hxmem.1
  exact mul_left_cancel₀ hm (hx m)

end ContinuousFlexibility.Statements
