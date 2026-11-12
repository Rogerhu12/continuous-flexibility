import ContinuousFlexibility.Radial.ReferenceWeightedProduct
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Pullback from the period-π circle to the physical angular interval

The quotient map from the normalized interval (0,2π] to the circle of
period π preserves measure: the interval consists of two fundamental
domains. Its product with the radial identity therefore preserves the
actual weighted product L² norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem referenceCircle_measurePreserving :
    MeasurePreserving ((↑) : ℝ → AddCircle Real.pi)
      referenceAngularMeasure AddCircle.haarAddCircle := by
  have hdisj : Disjoint (Ioc (0 : ℝ) Real.pi) (Ioc Real.pi (2 * Real.pi)) := by
    apply Set.disjoint_left.2
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  have hunion : Ioc (0 : ℝ) Real.pi ∪ Ioc Real.pi (2 * Real.pi) =
      Ioc (0 : ℝ) (2 * Real.pi) := by
    ext x
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans (by linarith [Real.pi_pos])⟩
      · exact ⟨Real.pi_pos.trans hx.1, hx.2⟩
    · intro hx
      by_cases hp : x ≤ Real.pi
      · exact Or.inl ⟨hx.1, hp⟩
      · exact Or.inr ⟨lt_of_not_ge hp, hx.2⟩
  have hsum := (AddCircle.measurePreserving_mk Real.pi 0).add_measure
    (AddCircle.measurePreserving_mk Real.pi Real.pi)
  have hadd : Real.pi + Real.pi = 2 * Real.pi := by ring
  rw [zero_add, hadd, ← Measure.restrict_union hdisj measurableSet_Ioc, hunion] at hsum
  have hcoef : ENNReal.ofReal ((2 * Real.pi)⁻¹) *
      (ENNReal.ofReal Real.pi + ENNReal.ofReal Real.pi) = 1 := by
    rw [← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹), hadd,
      inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), ENNReal.ofReal_one]
  have hnorm : ENNReal.ofReal ((2 * Real.pi)⁻¹) •
      ((volume : Measure (AddCircle Real.pi)) + volume) =
      AddCircle.haarAddCircle := by
    simp only [AddCircle.volume_eq_smul_haarAddCircle]
    rw [← add_smul, smul_smul, hcoef, one_smul]
  simpa only [referenceAngularMeasure, hnorm] using
    hsum.smul_measure (ENNReal.ofReal ((2 * Real.pi)⁻¹))

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem referenceCircleProduct_measurePreserving :
    MeasurePreserving (fun x : α × ℝ => (x.1, (x.2 : AddCircle Real.pi)))
      (μ.prod referenceAngularMeasure)
      (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))) :=
  (MeasurePreserving.id μ).prod referenceCircle_measurePreserving

/-- Isometric pullback to the actual physical angular variable. -/
def referenceCirclePullback :
    Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))) →ₗᵢ[ℝ]
      Lp ℝ 2 (μ.prod referenceAngularMeasure) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (fun x : α × ℝ => (x.1, (x.2 : AddCircle Real.pi)))
    referenceCircleProduct_measurePreserving

theorem referenceCirclePullback_ae
    (v : Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)))) :
    referenceCirclePullback v =ᵐ[μ.prod referenceAngularMeasure]
      fun x : α × ℝ => v (x.1, (x.2 : AddCircle Real.pi)) :=
  Lp.coeFn_compMeasurePreserving v referenceCircleProduct_measurePreserving

theorem referenceCirclePullback_memLp
    {v : α × AddCircle Real.pi → ℝ}
    (hv : MemLp v 2 (μ.prod AddCircle.haarAddCircle)) :
    MemLp (fun x : α × ℝ => v (x.1, (x.2 : AddCircle Real.pi)))
      2 (μ.prod referenceAngularMeasure) :=
  hv.comp_measurePreserving referenceCircleProduct_measurePreserving

theorem referenceCirclePullback_norm
    (v : Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)))) :
    ‖referenceCirclePullback v‖ = ‖v‖ :=
  referenceCirclePullback.norm_map v

end ContinuousFlexibility.Statements
