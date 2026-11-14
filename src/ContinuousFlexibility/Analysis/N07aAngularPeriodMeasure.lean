module

public import ContinuousFlexibility.Analysis.N07aAngularEven
public import ContinuousFlexibility.Radial.ReferenceCosineWeighted

/-!
# Actual periodic representatives on the half and full angular intervals

The physical graph uses a `2π` interval, whereas a canonical source uses
one `π` period.  Translation of the second half gives genuine `L²`
membership on the full interval, including a.e. strong measurability.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis

theorem n07aAngularHalfShift_preserving :
    MeasurePreserving (fun θ : ℝ => θ - Real.pi)
      (volume.restrict (Ioc Real.pi (2 * Real.pi))) angleMeasure := by
  have hpre : (fun θ : ℝ => θ + (-Real.pi)) ⁻¹' Ioc (0 : ℝ) Real.pi =
      Ioc Real.pi (2 * Real.pi) := by
    ext θ
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simpa only [hpre, sub_eq_add_neg, angleMeasure] using
    (measurePreserving_add_right (volume : Measure ℝ) (-Real.pi)).restrict_preimage
      (s := Ioc (0 : ℝ) Real.pi) measurableSet_Ioc

theorem n07a_memLp_fullPeriod_of_half {μ : Measure ℝ} [SFinite μ]
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (μ.prod angleMeasure))
    (hp : ∀ᵐ r ∂μ, Function.Periodic (fun θ => f (r, θ)) Real.pi) :
    MemLp f 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  have hpres : MeasurePreserving (fun p : PolarPoint => (p.1, p.2 - Real.pi))
      (μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))) (μ.prod angleMeasure) :=
    (MeasurePreserving.id μ).prod n07aAngularHalfShift_preserving
  have hshift := hf.comp_measurePreserving hpres
  have he : (f ∘ (fun p : PolarPoint => (p.1, p.2 - Real.pi))) =ᵐ[
      μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))] f := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := volume.restrict (Ioc Real.pi (2 * Real.pi)))).ae hp] with p hpr
    exact hpr.sub_eq p.2
  have hf₂ : MemLp f 2 (μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi)))) :=
    (memLp_congr_ae he).mp hshift
  have hsum : μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) =
      μ.prod angleMeasure + μ.prod (volume.restrict (Ioc Real.pi (2 * Real.pi))) := by
    rw [← Ioc_union_Ioc_eq_Ioc Real.pi_pos.le (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos]),
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.prod_add]
    rfl
  rw [hsum]
  exact (memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable.add_measure hf₂.aestronglyMeasurable)).mpr
      (hf.integrable_sq.add_measure hf₂.integrable_sq)

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07aCanonical_memLp_full_of_periodic {m : ℕ} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (canonicalMeasure S K m))
    (hp : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      Function.Periodic (fun θ => f (r, θ)) Real.pi) :
    MemLp f 2 ((volume.restrict (Ioo (K.left m) (K.right m))).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  rw [n07aCanonicalMeasure_eq_prod] at hf
  exact n07a_memLp_fullPeriod_of_half hf hp

end ContinuousFlexibility.Statements
