import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Topology.Order.ProjIcc

/-!
# Actual restricted L² on a compact interval

The compact-subtype space used by the continuous Green kernel and the
restriction of the ambient measure are isometrically the same L² space.
The inverse map is composition with the interval projection; it is an
inverse only almost everywhere on the restricted ambient measure, which
is exactly what L² requires.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped Topology

variable (μ : Measure ℝ) {a b : ℝ}

/-- The ambient measure transferred to the compact interval subtype. -/
def compactIntervalMeasure (a b : ℝ) : Measure (Icc a b) :=
  μ.comap (Subtype.val : Icc a b → ℝ)

theorem measurePreserving_compactInterval_val (a b : ℝ) :
    MeasurePreserving (Subtype.val : Icc a b → ℝ)
      (compactIntervalMeasure μ a b) (μ.restrict (Icc a b)) :=
  measurePreserving_subtype_coe measurableSet_Icc

theorem measurePreserving_compactInterval_proj (hab : a ≤ b) :
    MeasurePreserving (projIcc a b hab) (μ.restrict (Icc a b))
      (compactIntervalMeasure μ a b) := by
  have hp : Measurable (projIcc a b hab) := continuous_projIcc.measurable
  have hv := measurePreserving_compactInterval_val μ a b
  refine ⟨hp, ?_⟩
  calc
    Measure.map (projIcc a b hab) (μ.restrict (Icc a b)) =
        Measure.map (projIcc a b hab)
          (Measure.map (Subtype.val : Icc a b → ℝ) (compactIntervalMeasure μ a b)) := by
      rw [hv.map_eq]
    _ = Measure.map ((projIcc a b hab) ∘ Subtype.val) (compactIntervalMeasure μ a b) :=
      Measure.map_map hp measurable_subtype_coe
    _ = Measure.map id (compactIntervalMeasure μ a b) := by
      congr 1
      funext x
      exact projIcc_val hab x
    _ = compactIntervalMeasure μ a b := Measure.map_id

/-- Finite core mass is preserved by the compact interval identification. -/
theorem isFiniteMeasure_compactIntervalMeasure (hab : a ≤ b)
    [IsFiniteMeasure (μ.restrict (Icc a b))] :
    IsFiniteMeasure (compactIntervalMeasure μ a b) := by
  rw [← (measurePreserving_compactInterval_proj μ hab).map_eq]
  infer_instance

theorem compactIntervalMeasure_univ (hab : a ≤ b) :
    compactIntervalMeasure μ a b Set.univ = μ (Icc a b) := by
  rw [← (measurePreserving_compactInterval_proj μ hab).map_eq,
    Measure.map_apply (continuous_projIcc.measurable) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- The actual L² isometry between an ambient restriction and its compact subtype. -/
def l2CompactIntervalEquiv (hab : a ≤ b) :
    Lp ℝ 2 (μ.restrict (Icc a b)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (compactIntervalMeasure μ a b) where
  toFun := Lp.compMeasurePreserving (Subtype.val : Icc a b → ℝ)
    (measurePreserving_compactInterval_val μ a b)
  invFun := Lp.compMeasurePreserving (projIcc a b hab)
    (measurePreserving_compactInterval_proj μ hab)
  left_inv f := by
    apply Lp.ext
    have hv := measurePreserving_compactInterval_val μ a b
    have hp := measurePreserving_compactInterval_proj μ hab
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (Subtype.val : Icc a b → ℝ) hv f) hp,
      hp.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hv),
      ae_restrict_mem measurableSet_Icc] with x hx hval hmem
    simp only [Function.comp_apply] at hx hval
    rw [hx, hval, projIcc_of_mem hab hmem]
  right_inv f := by
    apply Lp.ext
    have hv := measurePreserving_compactInterval_val μ a b
    have hp := measurePreserving_compactInterval_proj μ hab
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (projIcc a b hab) hp f) hv,
      hv.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hp)] with x hx hproj
    simp only [Function.comp_apply] at hx hproj
    rw [hx, hproj, projIcc_val]
  map_add' := map_add (Lp.compMeasurePreservingₗ ℝ (Subtype.val : Icc a b → ℝ)
    (measurePreserving_compactInterval_val μ a b))
  map_smul' := map_smul (Lp.compMeasurePreservingₗ ℝ (Subtype.val : Icc a b → ℝ)
    (measurePreserving_compactInterval_val μ a b))
  norm_map' f := Lp.norm_compMeasurePreserving f (measurePreserving_compactInterval_val μ a b)

theorem l2CompactIntervalEquiv_coeFn (hab : a ≤ b)
    (f : Lp ℝ 2 (μ.restrict (Icc a b))) :
    (l2CompactIntervalEquiv μ hab f : Icc a b → ℝ) =ᵐ[compactIntervalMeasure μ a b]
      fun x => f x :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_compactInterval_val μ a b)

theorem l2CompactIntervalEquiv_symm_coeFn (hab : a ≤ b)
    (f : Lp ℝ 2 (compactIntervalMeasure μ a b)) :
    ((l2CompactIntervalEquiv μ hab).symm f : ℝ → ℝ) =ᵐ[μ.restrict (Icc a b)]
      fun x => f (projIcc a b hab x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_compactInterval_proj μ hab)

end ContinuousFlexibility.Analysis
