import ContinuousFlexibility.Radial.ReferenceTestRegularity
import ContinuousFlexibility.Radial.WeakDivergenceRegularity

/-!
# Genuine integrability of weak-test pairings

A field in the actual cell L² domain can be paired with every continuous
test of compact radial support. This applies both to an admissible test
and to the actual PDE applied to that test. Fubini then identifies the
frozen iterated angular integral with the physical two-dimensional integral.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace

theorem continuous_radialCellIntegrable {D : ReferenceData}
    (hP : RadialPartition D) {f : PolarPoint → ℝ} (hf : Continuous f) :
    RadialCellIntegrable D f := by
  intro m
  have hm : Continuous (fun x : PolarPoint => D.localizer m x.1 * f x) :=
    ((hP.1 m).continuous.comp continuous_fst).mul hf
  apply (continuous_memLp_reference_interval hm D.a D.b).mono_measure
  rw [radialPhysicalMeasure_eq_prod]
  exact Measure.prod_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl) le_rfl

theorem OutputMember.radialCellIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M : ℝ} {U : RadialUnknown} (hU : OutputMember D γ M U) :
    RadialCellIntegrable D U.1 := by
  obtain ⟨C, hC⟩ := hD
  obtain ⟨aL, hU⟩ := hU
  have hchi : Continuous (fun x : PolarPoint => aL * D.chiLeft x.1) :=
    continuous_const.mul (hB.2.2.2.2.1.continuous.comp continuous_fst)
  have hs := hU.1.add (continuous_radialCellIntegrable hC.2.1 hchi)
  apply hs.congr_ae
  filter_upwards with x
  change U.1 x - aL * D.chiLeft x.1 + aL * D.chiLeft x.1 = U.1 x
  ring

theorem RadialCellIntegrable.integrable_mul_radialSupport {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : Continuous g)
    {K : Set ℝ} (hK : IsCompact K) (hKcore : K ⊆ radialCore D)
    (hgs : ∀ r ∉ K, ∀ θ, g (r, θ) = 0) :
    Integrable (fun x => f x * g x) (radialPhysicalMeasure D) := by
  have hgeom : RadialProfileGeometry D := by
    obtain ⟨C, hC⟩ := hD
    exact hC.1
  obtain ⟨l, h, hal, hlh, hhb, hcover⟩ :=
    Radial.compact_subset_Ioo_enclosure hgeom.2.1 hK hKcore
  have hsub : Icc l h ⊆ radialCore D :=
    fun r hr => ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩
  have hfl := hf.memLp_on_interval hD hsub
  have hgl := continuous_memLp_reference_interval hg l h
  have hi : Integrable (fun x : PolarPoint => f x * g x)
      ((volume.restrict (Icc l h)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hfl.toLp f) (hgl.toLp g)).congr
    filter_upwards [hfl.coeFn_toLp, hgl.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply, hx, hy]
  have hsupport : Function.support (fun x : PolarPoint => f x * g x) ⊆
      Icc l h ×ˢ (univ : Set ℝ) := by
    intro x hx
    have hxK : x.1 ∈ K := by
      by_contra hn
      exact hx (by
        change f x * g (x.1, x.2) = 0
        rw [hgs x.1 hn x.2, mul_zero])
    exact ⟨mem_Icc_of_Ioo (hcover hxK), mem_univ _⟩
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  change Integrable (fun x : PolarPoint => f x * g x)
    ((radialPhysicalMeasure D).restrict (Icc l h ×ˢ (univ : Set ℝ)))
  have hrect : (Icc l h ×ˢ (univ : Set ℝ)) ∩
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) =
      Icc l h ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2.2⟩
    · intro hx
      exact ⟨⟨hx.1, mem_univ _⟩, hsub hx.1, hx.2⟩
  rw [radialPhysicalMeasure,
    Measure.restrict_restrict (measurableSet_Icc.prod MeasurableSet.univ), hrect]
  rw [Measure.prod_restrict] at hi
  exact hi

theorem RadialCellIntegrable.integrable_mul_test {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hψ : RadialTest D ψ) :
    Integrable (fun x => f x * ψ x) (radialPhysicalMeasure D) := by
  obtain ⟨K, hK, hKcore, hs⟩ := hψ.2.2
  exact hf.integrable_mul_radialSupport hD hψ.1.continuous hK hKcore hs

theorem RadialCellIntegrable.integrable_mul_testOperator {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hψ : RadialTest D ψ) :
    Integrable (fun x => f x *
      Radial.radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2)
      (radialPhysicalMeasure D) := by
  obtain ⟨K, hK, hKcore, hs⟩ := hψ.operator_radial_support
  exact hf.integrable_mul_radialSupport hD (hψ.operator_continuous hD) hK hKcore hs

theorem integral_angularMean_eq_physical {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : Integrable f (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      (2 * Real.pi)⁻¹ * ∫ x, f x ∂radialPhysicalMeasure D := by
  have hprod : Integrable f ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hf
  have hFub := integral_prod f hprod
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  simp_rw [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  simpa only [radialCore, radialPhysicalMeasure_eq_prod] using hFub.symm

theorem radialWeakPairing_eq_physical {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hψ : RadialTest D ψ) :
    radialWeakPairing D f ψ =
      (2 * Real.pi)⁻¹ * ∫ x, f x *
        Radial.radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2
        ∂radialPhysicalMeasure D := by
  obtain ⟨C, hC⟩ := hD
  exact integral_angularMean_eq_physical hC.1.2.1.le
    (hf.integrable_mul_testOperator ⟨C, hC⟩ hψ)

end ContinuousFlexibility.Statements
