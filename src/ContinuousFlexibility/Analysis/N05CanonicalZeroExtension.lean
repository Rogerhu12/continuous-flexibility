import ContinuousFlexibility.Analysis.N05CanonicalRadialCutoff
import ContinuousFlexibility.Analysis.SpacesLpRestriction

/-!
# Actual zero extension from a canonical rectangle to the cylinder

The radial window restriction of the cylinder measure is exactly the
canonical measure. Identity pullback and zero extension consequently give
a linear isometry, with the literal indicator representative and exact
integral pairing formula.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def n05CanonicalRadialWindow (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    Set PolarPoint :=
  Ioo (K.left m) (K.right m) ×ˢ univ

theorem n05CanonicalRadialWindow_measurable (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) : MeasurableSet (n05CanonicalRadialWindow S K m) :=
  measurableSet_Ioo.prod MeasurableSet.univ

theorem n05CanonicalMeasure_eq_cylinder_restrict (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m) =
      canonicalMeasure S K m := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [materialCylinderMeasure_eq_prod, n05CanonicalRadialWindow,
    ← Measure.prod_restrict, Measure.restrict_univ]
  exact (n05CanonicalMeasure_eq_prod S K m).symm

theorem n05CanonicalRestrictionIdentity_measurePreserving (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    MeasurePreserving (id : PolarPoint → PolarPoint)
      (materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m))
      (canonicalMeasure S K m) := by
  rw [n05CanonicalMeasure_eq_cylinder_restrict]
  exact MeasurePreserving.id _

def n05CanonicalToCylinderRestriction (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    CanonicalL2 S K m →ₗᵢ[ℝ]
      Lp ℝ 2 (materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m)) :=
  Lp.compMeasurePreservingₗᵢ ℝ id (n05CanonicalRestrictionIdentity_measurePreserving S K m)

theorem n05CanonicalToCylinderRestriction_ae (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalToCylinderRestriction S K m u : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m)] u :=
  Lp.coeFn_compMeasurePreserving u (n05CanonicalRestrictionIdentity_measurePreserving S K m)

def n05CanonicalZeroExtension (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    CanonicalL2 S K m →ₗᵢ[ℝ] CylinderL2 :=
  (spacesLpZeroExtension materialCylinderMeasure (n05CanonicalRadialWindow S K m)
    (n05CanonicalRadialWindow_measurable S K m)).comp (n05CanonicalToCylinderRestriction S K m)

theorem n05CanonicalZeroExtension_norm (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    ‖n05CanonicalZeroExtension S K m u‖ = ‖u‖ :=
  (n05CanonicalZeroExtension S K m).norm_map u

theorem n05CanonicalZeroExtension_ae (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalZeroExtension S K m u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (n05CanonicalRadialWindow S K m).indicator u := by
  have ht := (ae_restrict_iff' (n05CanonicalRadialWindow_measurable S K m)).mp
    (n05CanonicalToCylinderRestriction_ae S K m u)
  change (spacesLpZeroExtension materialCylinderMeasure (n05CanonicalRadialWindow S K m)
    (n05CanonicalRadialWindow_measurable S K m) (n05CanonicalToCylinderRestriction S K m u) :
      PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] _
  filter_upwards [spacesLpZeroExtension_ae materialCylinderMeasure (n05CanonicalRadialWindow S K m)
    (n05CanonicalRadialWindow_measurable S K m) (n05CanonicalToCylinderRestriction S K m u),
    ht] with p hp ht
  rw [hp]
  by_cases hm : p ∈ n05CanonicalRadialWindow S K m
  · simp only [indicator_of_mem hm]
    exact ht hm
  · simp only [indicator_of_notMem hm]

theorem n05CanonicalZeroExtension_mul_integral (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) (φ : PolarPoint → ℝ) :
    (∫ p, n05CanonicalZeroExtension S K m u p * φ p ∂materialCylinderMeasure) =
      ∫ p, u p * φ p ∂canonicalMeasure S K m := by
  calc
    (∫ p, n05CanonicalZeroExtension S K m u p * φ p ∂materialCylinderMeasure) =
        ∫ p, (n05CanonicalRadialWindow S K m).indicator (fun q => u q * φ q) p
          ∂materialCylinderMeasure := by
      apply integral_congr_ae
      filter_upwards [n05CanonicalZeroExtension_ae S K m u] with p hp
      rw [hp]
      by_cases hm : p ∈ n05CanonicalRadialWindow S K m
      · simp only [indicator_of_mem hm]
      · simp only [indicator_of_notMem hm, zero_mul]
    _ = ∫ p, u p * φ p
        ∂materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m) := by
      rw [integral_indicator (n05CanonicalRadialWindow_measurable S K m)]
    _ = _ := by rw [n05CanonicalMeasure_eq_cylinder_restrict]

def n05CanonicalCutoffExtension (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C) :
    CanonicalL2 S K m →L[ℝ] CylinderL2 :=
  (n05CanonicalZeroExtension S K m).toContinuousLinearMap.comp
    (n05CanonicalRadialMultiply S K m χ hχ C hC)

theorem n05CanonicalCutoffExtension_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C)
    (u : CanonicalL2 S K m) :
    n05CanonicalCutoffExtension S K m χ hχ C hC u =
      n05CanonicalZeroExtension S K m (n05CanonicalRadialMultiply S K m χ hχ C hC u) := by
  simp only [n05CanonicalCutoffExtension, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]

theorem n05CanonicalCutoffExtension_norm_le (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (C : ℝ) (hC : ∀ r, |χ r| ≤ C) (u : CanonicalL2 S K m) :
    ‖n05CanonicalCutoffExtension S K m χ hχ C hC u‖ ≤ C * ‖u‖ := by
  rw [n05CanonicalCutoffExtension_apply, n05CanonicalZeroExtension_norm]
  exact n05CanonicalRadialMultiply_norm_le S K m χ hχ C hC u

theorem n05WeakCanonicalAngularDerivative_cutoffExtension {S : PhysicalSpacesData}
    {K : CanonicalData S} {m j : ℕ} {f g : CanonicalL2 S K m}
    (h : WeakCanonicalAngularDerivative S K m f g j)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo (K.left m) (K.right m))
    (C : ℝ) (hC : ∀ r, |χ r| ≤ C) :
    HasWeakMixedDerivative
      (n05CanonicalCutoffExtension S K m χ hχ.continuous C hC f)
      (n05CanonicalCutoffExtension S K m χ hχ.continuous C hC g) 0 j := by
  intro φ hφ
  simp only [Nat.zero_add, n05CanonicalCutoffExtension_apply,
    n05CanonicalZeroExtension_mul_integral]
  let ψ : PolarPoint → ℝ := fun p => χ p.1 * φ p
  have hψ : CanonicalTest S K m ψ := n05CanonicalTest_cutoff_cylinder hφ hχ hc hs
  calc
    (∫ p, n05CanonicalRadialMultiply S K m χ hχ.continuous C hC g p * φ p
      ∂canonicalMeasure S K m) =
        ∫ p, g p * ψ p ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [n05CanonicalRadialMultiply_ae S K m χ hχ.continuous C hC g] with p hp
      rw [hp]
      dsimp only [ψ]
      ring
    _ = (-1 : ℝ) ^ j * ∫ p, f p * mixedDerivative 0 j ψ p ∂canonicalMeasure S K m :=
      h ψ hψ
    _ = (-1 : ℝ) ^ j *
        ∫ p, n05CanonicalRadialMultiply S K m χ hχ.continuous C hC f p *
          mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
      congr 1
      apply integral_congr_ae
      filter_upwards [n05CanonicalRadialMultiply_ae S K m χ hχ.continuous C hC f] with p hp
      rw [hp, n05CanonicalAngularDerivative_radial_mul]
      ring


theorem n05CanonicalZeroExtension_even (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) (hu : n05CanonicalReflection S K m u = u) :
    cylinderReflectionL2 (n05CanonicalZeroExtension S K m u) =
      n05CanonicalZeroExtension S K m u := by
  apply (cylinderReflectionL2_fixed_iff _).mpr
  have he : (fun p : PolarPoint => u (p.1, Real.pi - p.2))
      =ᵐ[materialCylinderMeasure.restrict (n05CanonicalRadialWindow S K m)] u := by
    rw [n05CanonicalMeasure_eq_cylinder_restrict]
    exact (n05CanonicalReflection_fixed_iff S K m u).mp hu
  have he' := (ae_restrict_iff' (n05CanonicalRadialWindow_measurable S K m)).mp he
  have hz := n05CanonicalZeroExtension_ae S K m u
  have hr := measurePreserving_cylinderAngularReflection.quasiMeasurePreserving.ae_eq_comp hz
  filter_upwards [hr, hz, he'] with p hp hq he
  change n05CanonicalZeroExtension S K m u (p.1, Real.pi - p.2) =
    (n05CanonicalRadialWindow S K m).indicator u (p.1, Real.pi - p.2) at hp
  rw [hp, hq]
  have hwindow : (p.1, Real.pi - p.2) ∈ n05CanonicalRadialWindow S K m ↔
      p ∈ n05CanonicalRadialWindow S K m := Iff.rfl
  by_cases hw : p ∈ n05CanonicalRadialWindow S K m
  · simp only [indicator_of_mem hw, indicator_of_mem (hwindow.mpr hw)]
    exact he hw
  · simp only [indicator_of_notMem hw, indicator_of_notMem (fun h => hw (hwindow.mp h))]

theorem n05CanonicalCutoffExtension_even (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (χ : ℝ → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ r, |χ r| ≤ C)
    (u : CanonicalL2 S K m) (hu : n05CanonicalReflection S K m u = u) :
    cylinderReflectionL2 (n05CanonicalCutoffExtension S K m χ hχ C hC u) =
      n05CanonicalCutoffExtension S K m χ hχ C hC u := by
  rw [n05CanonicalCutoffExtension_apply]
  exact n05CanonicalZeroExtension_even S K m _
    (n05CanonicalRadialMultiply_even S K m χ hχ C hC u hu)


end ContinuousFlexibility.Statements

