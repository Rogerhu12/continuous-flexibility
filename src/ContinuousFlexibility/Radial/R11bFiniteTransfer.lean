import ContinuousFlexibility.Radial.R11bCellProjection

/-!
# Finite transfer between normalized angular systems

Analysis in one orthonormal angular family followed by synthesis in another
contracts the actual physical and localized L² norms.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

def r11bFiniteTransfer {ι : Type*} (s : Finset ι)
    (e d : ι → ℝ → ℝ) (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  ∑ i ∈ s, angularPairing (fun θ => f (x.1, θ)) (e i) * d i x.2

theorem r11b_finiteTransfer_memLp {D : ReferenceData} {ι : Type*}
    (s : Finset ι) (e d : ι → ℝ → ℝ) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hd : ∀ i ∈ s, MemLp (d i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp (r11bFiniteTransfer s e d f) 2 (radialPhysicalMeasure D) := by
  have hc (i : ι) (hi : i ∈ s) :
      MemLp (fun r => angularPairing (fun θ => f (r, θ)) (e i))
        2 (volume.restrict (radialCore D)) :=
    (r11b_memLp_angularCoefficient hf (memLp_angularMeanMeasure (he i hi))).1
  have ht (i : ι) (hi : i ∈ s) :
      MemLp (fun z : PolarPoint =>
        angularPairing (fun θ => f (z.1, θ)) (e i) * d i z.2)
        2 (radialPhysicalMeasure D) := by
    rw [r11b_radialPhysicalMeasure_eq_prod]
    exact r11b_memLp_tensor (hc i hi) (hd i hi)
  have hsum := memLp_finsetSum s ht
  apply MemLp.ae_eq _ hsum
  exact Filter.Eventually.of_forall fun z => by
    simp only [Finset.sum_apply, r11bFiniteTransfer]

theorem r11b_finiteTransfer_angular_square_le {D : ReferenceData}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e d : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hd : ∀ i ∈ s, MemLp (d i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hdorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (d i) (d j) = if i = j then 1 else 0) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      angularAverage (fun θ => r11bFiniteTransfer s e d f (r, θ) ^ 2) ≤
        angularAverage (fun θ => f (r, θ) ^ 2) := by
  filter_upwards [r11b_physical_sections_memLp hf] with r hr
  change angularAverage
    (fun θ => (∑ i ∈ s, angularPairing (fun φ => f (r, φ)) (e i) * d i θ) ^ 2) ≤ _
  rw [angularAverage_sq_finite_sum s d hd hdorth]
  exact angularPairing_finite_bessel s e hr he heorth

theorem r11b_finiteTransfer_square_integral_le {D : ReferenceData}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e d : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hd : ∀ i ∈ s, MemLp (d i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hdorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (d i) (d j) = if i = j then 1 else 0) :
    (∫ z, r11bFiniteTransfer s e d f z ^ 2 ∂radialPhysicalMeasure D) ≤
      ∫ z, f z ^ 2 ∂radialPhysicalMeasure D :=
  r11b_physical_square_integral_le_of_angular (D := D) (f := f)
    (g := r11bFiniteTransfer s e d f) hf
    (r11b_finiteTransfer_memLp (D := D) s e d hf he hd)
    (r11b_finiteTransfer_angular_square_le (D := D) s e d hf he hd heorth hdorth)

theorem r11bFiniteTransfer_radial_mul {ι : Type*} (s : Finset ι)
    (e d : ι → ℝ → ℝ) (a : ℝ → ℝ) (f : PolarPoint → ℝ) :
    r11bFiniteTransfer s e d (fun x => a x.1 * f x) =
      fun x => a x.1 * r11bFiniteTransfer s e d f x := by
  funext x
  simp only [r11bFiniteTransfer, r11b_angularPairing_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem r11b_finiteTransfer_cell_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e d : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hd : ∀ i ∈ s, MemLp (d i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hdorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (d i) (d j) = if i = j then 1 else 0) :
    RadialCellIntegrable D (r11bFiniteTransfer s e d f) ∧
      ∀ m, referenceCellSquare D m (r11bFiniteTransfer s e d f) ≤
        referenceCellSquare D m f := by
  have hp : RadialCellIntegrable D (r11bFiniteTransfer s e d f) := by
    intro m
    have h := r11b_finiteTransfer_memLp s e d (hf m) he hd
    rw [r11bFiniteTransfer_radial_mul s e d (D.localizer m) f] at h
    exact h
  refine ⟨hp, fun m => ?_⟩
  have h := r11b_finiteTransfer_square_integral_le s e d (hf m) he hd heorth hdorth
  rw [r11bFiniteTransfer_radial_mul s e d (D.localizer m) f] at h
  rw [r11b_referenceCellSquare_eq_integral hab hp m,
    r11b_referenceCellSquare_eq_integral hab hf m]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end ContinuousFlexibility.Radial
