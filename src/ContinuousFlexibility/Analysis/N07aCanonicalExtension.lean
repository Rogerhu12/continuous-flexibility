module

public import ContinuousFlexibility.Analysis.N07aAngularClassical
public import ContinuousFlexibility.Analysis.N07aWeakRegularityAlgebra

/-!
# Extension of actual canonical L² classes to the cylinder

Extension by zero is an exact linear isometry. Its integral pairing is
the original canonical pairing. Compact radial localization will use
this map to transfer true weak derivatives to the cylinder, where the
smooth reconstruction theorem applies.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonical_ae_imp {P : PolarPoint → Prop}
    (h : ∀ᵐ p ∂canonicalMeasure S K m, P p) :
    ∀ᵐ p ∂materialCylinderMeasure, p ∈ canonicalOpen S K m → P p := by
  apply (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).mp
  rwa [← n07a_canonicalMeasure_eq_cylinder_restrict S K m]

theorem n07aCanonicalZeroExtension_memLp (u : CanonicalL2 S K m) :
    MemLp ((canonicalOpen S K m).indicator (u : PolarPoint → ℝ))
      2 materialCylinderMeasure := by
  rw [canonicalOpen, memLp_indicator_iff_restrict (measurableSet_Ioo.prod MeasurableSet.univ),
    ← n07a_canonicalMeasure_eq_cylinder_restrict S K m]
  exact Lp.memLp u

def n07aCanonicalZeroExtension (u : CanonicalL2 S K m) : CylinderL2 :=
  (n07aCanonicalZeroExtension_memLp u).toLp
    ((canonicalOpen S K m).indicator (u : PolarPoint → ℝ))

theorem n07aCanonicalZeroExtension_ae (u : CanonicalL2 S K m) :
    (n07aCanonicalZeroExtension u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (canonicalOpen S K m).indicator (u : PolarPoint → ℝ) := MemLp.coeFn_toLp _

theorem n07aCanonicalZeroExtension_norm (u : CanonicalL2 S K m) :
    ‖n07aCanonicalZeroExtension u‖ = ‖u‖ := by
  rw [n07aCanonicalZeroExtension, Lp.norm_toLp, canonicalOpen,
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_Ioo.prod MeasurableSet.univ),
    ← n07a_canonicalMeasure_eq_cylinder_restrict S K m, Lp.norm_def]

theorem n07aCanonicalZeroExtension_add (u v : CanonicalL2 S K m) :
    n07aCanonicalZeroExtension (u + v) =
      n07aCanonicalZeroExtension u + n07aCanonicalZeroExtension v := by
  apply Lp.ext
  filter_upwards [n07aCanonicalZeroExtension_ae (u + v),
    n07aCanonicalZeroExtension_ae u, n07aCanonicalZeroExtension_ae v,
    Lp.coeFn_add (n07aCanonicalZeroExtension u) (n07aCanonicalZeroExtension v),
    n07aCanonical_ae_imp (Lp.coeFn_add u v)] with p hsum hu hv he hi
  rw [hsum, he]
  simp only [Pi.add_apply]
  rw [hu, hv]
  by_cases hp : p ∈ canonicalOpen S K m
  · simp only [Set.indicator_of_mem hp]
    exact hi hp
  · simp only [Set.indicator_of_notMem hp, zero_add]

theorem n07aCanonicalZeroExtension_smul (c : ℝ) (u : CanonicalL2 S K m) :
    n07aCanonicalZeroExtension (c • u) = c • n07aCanonicalZeroExtension u := by
  apply Lp.ext
  filter_upwards [n07aCanonicalZeroExtension_ae (c • u), n07aCanonicalZeroExtension_ae u,
    Lp.coeFn_smul c (n07aCanonicalZeroExtension u),
    n07aCanonical_ae_imp (Lp.coeFn_smul c u)] with p hmul hu he hi
  rw [hmul, he]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hu]
  by_cases hp : p ∈ canonicalOpen S K m
  · simp only [Set.indicator_of_mem hp]
    exact hi hp
  · simp only [Set.indicator_of_notMem hp, mul_zero]

/-- Extension by zero keeps exactly the prescribed physical L² norm. -/
def n07aCanonicalExtension : CanonicalL2 S K m →ₗᵢ[ℝ] CylinderL2 where
  toFun := n07aCanonicalZeroExtension
  map_add' := n07aCanonicalZeroExtension_add
  map_smul' := n07aCanonicalZeroExtension_smul
  norm_map' := n07aCanonicalZeroExtension_norm

theorem n07aCanonicalExtension_apply (u : CanonicalL2 S K m) :
    n07aCanonicalExtension u = n07aCanonicalZeroExtension u := rfl

theorem n07aCanonicalExtension_restrict_ae (u : CanonicalL2 S K m) :
    (n07aCanonicalExtension u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] u := by
  have he := (n07aCanonicalZeroExtension_ae u).filter_mono
    (ae_mono (show canonicalMeasure S K m ≤ materialCylinderMeasure from by
      rw [n07a_canonicalMeasure_eq_cylinder_restrict]
      exact Measure.restrict_le_self))
  have hm : ∀ᵐ p ∂canonicalMeasure S K m, p ∈ canonicalOpen S K m := by
    rw [n07a_canonicalMeasure_eq_cylinder_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)
  filter_upwards [he, hm] with p hp hpm
  simpa only [n07aCanonicalExtension_apply, Set.indicator_of_mem hpm] using hp

theorem n07aCanonicalExtension_pairing (u : CanonicalL2 S K m) (φ : PolarPoint → ℝ) :
    (∫ p, n07aCanonicalExtension u p * φ p ∂materialCylinderMeasure) =
      ∫ p, u p * φ p ∂canonicalMeasure S K m := by
  calc
    _ = ∫ p, (canonicalOpen S K m).indicator (fun p => u p * φ p) p
        ∂materialCylinderMeasure := by
      apply integral_congr_ae
      filter_upwards [n07aCanonicalZeroExtension_ae u] with p hp
      rw [n07aCanonicalExtension_apply, hp]
      by_cases hm : p ∈ canonicalOpen S K m
      · simp only [Set.indicator_of_mem hm]
      · simp only [Set.indicator_of_notMem hm, zero_mul]
    _ = _ := by
      rw [canonicalOpen, integral_indicator (measurableSet_Ioo.prod MeasurableSet.univ),
        ← n07a_canonicalMeasure_eq_cylinder_restrict S K m]

end ContinuousFlexibility.Analysis
