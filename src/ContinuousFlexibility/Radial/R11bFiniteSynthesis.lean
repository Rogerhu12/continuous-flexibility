module

public import ContinuousFlexibility.Radial.R11bPhysicalProjection
public import ContinuousFlexibility.Radial.ProfilePartitionBounds

/-!
# Actual finite angular synthesis and cell Parseval

The radial coefficients may be arbitrary L² functions. Orthogonality is only
used in the angular variable; localizers act on the original representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

def r11bFiniteSynthesis {ι : Type*} (s : Finset ι)
    (c e : ι → ℝ → ℝ) (x : PolarPoint) : ℝ :=
  ∑ i ∈ s, c i x.1 * e i x.2

theorem r11bFiniteSynthesis_radial_mul {ι : Type*} (s : Finset ι)
    (c e : ι → ℝ → ℝ) (a : ℝ → ℝ) :
    (fun x : PolarPoint => a x.1 * r11bFiniteSynthesis s c e x) =
      r11bFiniteSynthesis s (fun i r => a r * c i r) e := by
  funext x
  simp only [r11bFiniteSynthesis, Finset.mul_sum, mul_assoc]

theorem r11b_finiteSynthesis_memLp {D : ReferenceData} {ι : Type*}
    (s : Finset ι) (c e : ι → ℝ → ℝ)
    (hc : ∀ i ∈ s, MemLp (c i) 2 (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp (r11bFiniteSynthesis s c e) 2 (radialPhysicalMeasure D) := by
  rw [r11b_radialPhysicalMeasure_eq_prod]
  exact memLp_finsetSum s (fun i hi => r11b_memLp_tensor (hc i hi) (he i hi))

theorem r11b_finiteSynthesis_square_integral {D : ReferenceData}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c e : ι → ℝ → ℝ)
    (hc : ∀ i ∈ s, MemLp (c i) 2 (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    (1 / (2 * Real.pi)) *
        (∫ x, r11bFiniteSynthesis s c e x ^ 2 ∂radialPhysicalMeasure D) =
      ∑ i ∈ s, ∫ r, c i r ^ 2 ∂volume.restrict (radialCore D) := by
  have hp := r11b_finiteSynthesis_memLp (D := D) s c e hc he
  rw [← (r11b_angular_square_integral hp).2]
  calc
    (∫ r, angularAverage (fun θ => r11bFiniteSynthesis s c e (r, θ) ^ 2)
        ∂volume.restrict (radialCore D)) =
        ∫ r, ∑ i ∈ s, c i r ^ 2 ∂volume.restrict (radialCore D) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r =>
        angularAverage_sq_finite_sum s e he horth (fun i => c i r)
    _ = ∑ i ∈ s, ∫ r, c i r ^ 2 ∂volume.restrict (radialCore D) :=
      integral_finsetSum s (fun i hi => (hc i hi).integrable_sq)

theorem r11b_finiteSynthesis_cell_parseval_of_localized {D : ReferenceData}
    (hab : D.a ≤ D.b) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c e : ι → ℝ → ℝ)
    (hc : ∀ i ∈ s, ∀ m, MemLp (fun r => D.localizer m r * c i r) 2
      (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    RadialCellIntegrable D (r11bFiniteSynthesis s c e) ∧
      ∀ m, referenceCellSquare D m (r11bFiniteSynthesis s c e) =
        ∑ i ∈ s, ∫ r, (D.localizer m r * c i r) ^ 2
          ∂volume.restrict (radialCore D) := by
  have hcell : RadialCellIntegrable D (r11bFiniteSynthesis s c e) := by
    intro m
    rw [r11bFiniteSynthesis_radial_mul]
    exact r11b_finiteSynthesis_memLp (D := D) s
      (fun i r => D.localizer m r * c i r) e (fun i hi => hc i hi m) he
  refine ⟨hcell, fun m => ?_⟩
  rw [r11b_referenceCellSquare_eq_integral hab hcell m]
  have hmul (x : PolarPoint) :
      D.localizer m x.1 * r11bFiniteSynthesis s c e x =
        r11bFiniteSynthesis s (fun i r => D.localizer m r * c i r) e x :=
    congrFun (r11bFiniteSynthesis_radial_mul s c e (D.localizer m)) x
  simpa only [hmul, one_div] using r11b_finiteSynthesis_square_integral (D := D) s
    (fun i r => D.localizer m r * c i r) e (fun i hi => hc i hi m) he horth

theorem r11b_finiteSynthesis_cell_parseval {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c e : ι → ℝ → ℝ)
    (hc : ∀ i ∈ s, MemLp (c i) 2 (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, MemLp (e i) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    RadialCellIntegrable D (r11bFiniteSynthesis s c e) ∧
      ∀ m, referenceCellSquare D m (r11bFiniteSynthesis s c e) =
        ∑ i ∈ s, ∫ r, (D.localizer m r * c i r) ^ 2
          ∂volume.restrict (radialCore D) := by
  apply r11b_finiteSynthesis_cell_parseval_of_localized hab s c e _ he horth
  intro i hi m
  apply (hc i hi).mono
    ((hpart.1 m).continuous.aestronglyMeasurable.mul (hc i hi).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro r
  change ‖D.localizer m r * c i r‖ ≤ ‖c i r‖
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (profile_localizer_abs_le_one hpart m r)
    (norm_nonneg (c i r))).trans_eq (one_mul _)

end ContinuousFlexibility.Radial
