module

public import ContinuousFlexibility.Radial.TailLowModeSynthesis
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual mass averages as a bounded coefficient map

Disjoint measurable mass cells of positive finite measure give normalized
indicator vectors in the physical `L²` space. Their analysis map has norm at
most one and its coordinates are exactly the normalized cell integrals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory Set
open scoped lp ENNReal InnerProductSpace RealInnerProductSpace

variable {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
  {μ : Measure α}

/-- The mass-normalized indicator of one cell in the actual `L²` space. -/
def tailNormalizedMass (s : Set α) (hs : MeasurableSet s) (hfin : μ s ≠ ∞) :
    Lp ℝ 2 μ :=
  (Real.sqrt (μ.real s))⁻¹ • indicatorConstLp 2 hs hfin (1 : ℝ)

theorem tailNormalizedMass_pairing (s : Set α) (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    (f : Lp ℝ 2 μ) :
    ⟪tailNormalizedMass s hs hfin, f⟫_ℝ =
      (Real.sqrt (μ.real s))⁻¹ * ∫ x in s, f x ∂μ := by
  rw [tailNormalizedMass, real_inner_smul_left, L2.inner_indicatorConstLp_one]

theorem tailNormalizedMass_inner (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfin : μ s ≠ ∞) (htfin : μ t ≠ ∞) :
    ⟪tailNormalizedMass s hs hfin, tailNormalizedMass t ht htfin⟫_ℝ =
      (Real.sqrt (μ.real s))⁻¹ * (Real.sqrt (μ.real t))⁻¹ * μ.real (s ∩ t) := by
  rw [tailNormalizedMass, tailNormalizedMass, real_inner_smul_left, real_inner_smul_right,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  ring

theorem tailNormalizedMass_orthonormal (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ (s i) ≠ ∞)
    (hpos : ∀ i, 0 < μ.real (s i))
    (hdisjoint : Pairwise (fun i j => Disjoint (s i) (s j))) :
    Orthonormal ℝ (fun i => tailNormalizedMass (s i) (hs i) (hfin i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [tailNormalizedMass_inner]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, inter_self]
    have hr : Real.sqrt (μ.real (s i)) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    field_simp [hr]
    nlinarith [Real.sq_sqrt (hpos i).le]
  · simp [Set.disjoint_iff_inter_eq_empty.mp (hdisjoint hij), hij]

/-- The normalized mass averages as an actual bounded map from physical `L²`
to the unweighted coefficient space. -/
def tailMassAnalysis (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ (s i) ≠ ∞)
    (hpos : ∀ i, 0 < μ.real (s i))
    (hdisjoint : Pairwise (fun i j => Disjoint (s i) (s j))) :
    Lp ℝ 2 μ →L[ℝ] ℓ²(ι, ℝ) :=
  tailOrthonormalAnalysis (fun i => tailNormalizedMass (s i) (hs i) (hfin i))
    (tailNormalizedMass_orthonormal s hs hfin hpos hdisjoint)

theorem tailMassAnalysis_apply (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ (s i) ≠ ∞)
    (hpos : ∀ i, 0 < μ.real (s i))
    (hdisjoint : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : Lp ℝ 2 μ) (i : ι) :
    tailMassAnalysis s hs hfin hpos hdisjoint f i =
      (Real.sqrt (μ.real (s i)))⁻¹ * ∫ x in s i, f x ∂μ := by
  rw [tailMassAnalysis, tailOrthonormalAnalysis_apply, tailNormalizedMass_pairing]

theorem norm_tailMassAnalysis_le (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ (s i) ≠ ∞)
    (hpos : ∀ i, 0 < μ.real (s i))
    (hdisjoint : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ‖tailMassAnalysis s hs hfin hpos hdisjoint‖ ≤ 1 :=
  norm_tailOrthonormalAnalysis_le _ _

end ContinuousFlexibility.Radial
