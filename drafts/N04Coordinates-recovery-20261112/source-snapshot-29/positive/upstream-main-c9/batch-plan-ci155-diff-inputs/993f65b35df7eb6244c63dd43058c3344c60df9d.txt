import ContinuousFlexibility.Analysis.N05CanonicalPhysicalL2

/-!
# Integrals on two actual angular periods

Translation by pi carries the lower physical angular rectangle to the
upper rectangle. Every integrable pi-periodic field therefore has exactly
twice its half-period integral on the full reference period. In particular,
this identifies the square integral of an actual L² field.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

theorem n05_piPeriodic_integral_fullPeriod
    {J : Set ℝ} (hJ : MeasurableSet J) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (hfull : Integrable f (volume.restrict (J ×ˢ Ioc (0 : ℝ) (2 * Real.pi)))) :
    (∫ p, f p ∂volume.restrict (J ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) =
      2 * ∫ p, f p ∂volume.restrict (J ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hlowerSet : J ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      J ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans (by linarith [Real.pi_pos])⟩
  have hilower : IntegrableOn f (J ×ˢ Ioc (0 : ℝ) Real.pi) volume :=
    hfull.mono_measure (Measure.restrict_mono hlowerSet le_rfl)
  have hupperSet : J ×ˢ Ioc Real.pi (2 * Real.pi) ⊆
      J ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    fun p hp => ⟨hp.1, Real.pi_pos.trans hp.2.1, hp.2.2⟩
  have hiupper : IntegrableOn f
      (J ×ˢ Ioc Real.pi (2 * Real.pi)) volume :=
    hfull.mono_measure (Measure.restrict_mono hupperSet le_rfl)
  have hpre : (fun p : PolarPoint => p + (0, Real.pi)) ⁻¹'
      (J ×ˢ Ioc Real.pi (2 * Real.pi)) = J ×ˢ Ioc (0 : ℝ) Real.pi := by
    ext p
    simp only [mem_preimage, mem_prod, Prod.fst_add, Prod.snd_add, add_zero, mem_Ioc]
    constructor
    · rintro ⟨hr, hlo, hhi⟩
      exact ⟨hr, by linarith only [hlo], by linarith only [hhi]⟩
    · rintro ⟨hr, hlo, hhi⟩
      exact ⟨hr, by linarith only [hlo], by linarith only [hhi]⟩
  have hshift := (measurePreserving_add_right volume ((0, Real.pi) : PolarPoint)).restrict_preimage
    (s := J ×ˢ Ioc Real.pi (2 * Real.pi))
    (hJ.prod measurableSet_Ioc)
  rw [hpre] at hshift
  have hupperIntegral :
      (∫ p, f p ∂volume.restrict (J ×ˢ Ioc Real.pi (2 * Real.pi))) =
        ∫ p, f p ∂volume.restrict (J ×ˢ Ioc (0 : ℝ) Real.pi) := by
    rw [← hshift.integral_comp
      (MeasurableEquiv.addRight ((0, Real.pi) : PolarPoint)).measurableEmbedding
      f]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hf
  have hdisjoint : Disjoint (J ×ˢ Ioc (0 : ℝ) Real.pi)
      (J ×ˢ Ioc Real.pi (2 * Real.pi)) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.2.2) hq.2.1
  have hunion : (J ×ˢ Ioc (0 : ℝ) Real.pi) ∪
      (J ×ˢ Ioc Real.pi (2 * Real.pi)) = J ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [← prod_union, Ioc_union_Ioc_eq_Ioc Real.pi_pos.le
      (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos])]
  rw [← hunion, setIntegral_union hdisjoint (hJ.prod measurableSet_Ioc)
    hilower hiupper, hupperIntegral]
  ring

theorem n05_piPeriodic_integral_sq_fullPeriod
    {J : Set ℝ} (hJ : MeasurableSet J) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (hhalf : MemLp f 2 (volume.restrict (J ×ˢ Ioc (0 : ℝ) Real.pi))) :
    (∫ p, f p ^ 2 ∂volume.restrict (J ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) =
      2 * ∫ p, f p ^ 2 ∂volume.restrict (J ×ˢ Ioc (0 : ℝ) Real.pi) := by
  apply n05_piPeriodic_integral_fullPeriod hJ
    (fun p => congrArg (fun x : ℝ => x ^ 2) (hf p))
  exact (n05_piPeriodic_memLp_fullPeriod hJ hf hhalf).integrable_sq

end ContinuousFlexibility.Statements
