module

public import ContinuousFlexibility.Analysis.PhysicalJetMollification
public import ContinuousFlexibility.Analysis.SpacesHeightBounds
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness and the unweighted physical jet tower

The compact planar test identity separates periodic cylinder `L²`
classes. Thus every weighted coordinate of a compatible physical jet
has the same unweighted derivative as the pure coordinate of its order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff

/-- The actual cylinder weak derivative is unique as an `L²` class. -/
theorem hasWeakMixedDerivative_unique {f d e : CylinderL2} {a b : ℕ}
    (hd : HasWeakMixedDerivative f d a b)
    (he : HasWeakMixedDerivative f e a b) : d = e := by
  have hp : cylinderPeriodicExtension d =ᵐ[volume] cylinderPeriodicExtension e := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_cylinderPeriodicExtension d)
      (locallyIntegrable_cylinderPeriodicExtension e)
    intro φ hφ hc
    simp only [smul_eq_mul, mul_comm (φ _)]
    rw [hd.periodicExtension_test hφ hc, he.periodicExtension_test hφ hc]
  have hr : cylinderPeriodicExtension d =ᵐ[materialCylinderMeasure]
      cylinderPeriodicExtension e := hp.filter_mono (ae_mono Measure.restrict_le_self)
  apply Lp.ext
  exact (cylinderPeriodicExtension_ae d).symm.trans (hr.trans (cylinderPeriodicExtension_ae e))

/-- The pure mixed index occurs already in the level `a + b`. -/
def physicalJetPureMixedIndex (a b : ℕ) : JetIndex (a + b) :=
  spacesMixedJetIndex a b (a + b) le_rfl

@[simp] theorem physicalJetPureMixedIndex_radial (a b : ℕ) :
    ((physicalJetPureMixedIndex a b).val 0).val = a := rfl

@[simp] theorem physicalJetPureMixedIndex_angular (a b : ℕ) :
    ((physicalJetPureMixedIndex a b).val 1).val = b := rfl

@[simp] theorem physicalJetPureMixedIndex_weight (a b : ℕ) :
    ((physicalJetPureMixedIndex a b).val 2).val = 0 := rfl

variable {D : ReferenceData} {T : MaterialData} {hT : IsMaterialData D T}

/-- A pure coordinate has no weight to remove. -/
theorem physicalJetNormalizedDerivative_pure {a b : ℕ} (z : PhysicalJetHilbert (a + b)) :
    physicalJetNormalizedDerivative hT (physicalJetPureMixedIndex a b) z =
      z (physicalJetPureMixedIndex a b) := by
  apply Lp.ext
  filter_upwards [physicalJetNormalizedDerivative_ae hT (physicalJetPureMixedIndex a b) z]
    with p hp
  simpa only [physicalJetWeight, physicalJetPureMixedIndex_weight, pow_zero, inv_one,
    one_mul] using hp

/-- The common unweighted mixed derivative of a compatible physical jet. -/
def physicalJetMixedDerivative (u : PhysicalJetProjectiveLimit hT) (a b : ℕ) : CylinderL2 :=
  (u.val (a + b)).val (physicalJetPureMixedIndex a b)

theorem physicalJetProjective_mem_graph (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    (u.val s).val ∈ physicalJetGraph T s := by
  rw [← physicalJetClosedSubmodule_carrier hT]
  exact (u.val s).property

theorem physicalJetMixedDerivative_spec (u : PhysicalJetProjectiveLimit hT) (a b : ℕ) :
    HasWeakMixedDerivative (physicalJetProjectiveZero hT u)
      (physicalJetMixedDerivative u a b) a b := by
  have hh := ((mem_physicalJetGraph_iff_normalized hT (u.val (a + b)).val).mp
    (physicalJetProjective_mem_graph u (a + b))).2 (physicalJetPureMixedIndex a b)
  rw [physicalJetNormalizedDerivative_pure,
    ← physicalJetProjectiveZero_apply hT u (a + b)] at hh
  exact hh

/-- Every level recovers precisely the pure mixed derivative. -/
theorem physicalJetNormalizedDerivative_eq_mixed (u : PhysicalJetProjectiveLimit hT)
    (s : ℕ) (j : JetIndex s) :
    physicalJetNormalizedDerivative hT j (u.val s).val =
      physicalJetMixedDerivative u (j.val 0).val (j.val 1).val := by
  have hh := ((mem_physicalJetGraph_iff_normalized hT (u.val s).val).mp
    (physicalJetProjective_mem_graph u s)).2 j
  rw [← physicalJetProjectiveZero_apply hT u s] at hh
  exact hasWeakMixedDerivative_unique hh (physicalJetMixedDerivative_spec u _ _)

/-- Exact weighted recovery, before choosing any smooth representative. -/
theorem physicalJetMixedDerivative_level_ae (u : PhysicalJetProjectiveLimit hT)
    (s : ℕ) (j : JetIndex s) :
    (((u.val s).val j) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      fun p => physicalJetWeight T j p * physicalJetMixedDerivative u (j.val 0).val (j.val 1).val p := by
  obtain ⟨d, hd, hw⟩ := (physicalJetProjective_mem_graph u s).2 j
  have he : d = physicalJetMixedDerivative u (j.val 0).val (j.val 1).val := by
    rw [← physicalJetProjectiveZero_apply hT u s] at hd
    exact hasWeakMixedDerivative_unique hd (physicalJetMixedDerivative_spec u _ _)
  rw [he] at hw
  exact hw

end ContinuousFlexibility.Statements
