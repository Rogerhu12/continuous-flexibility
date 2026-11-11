import ContinuousFlexibility.Analysis.N05ReferenceHighProjection
import ContinuousFlexibility.Radial.R11bFourierReconstruction
import ContinuousFlexibility.Radial.R11bLpConvergence

/-!
# The actual high cosine cuts converge to the original high field

The normalized even basis used in the physical reconstruction is exactly
the reference basis. Removing its first two terms identifies the limit
of the higher projections with the original field minus its low projection.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

def n05_referenceHighPart (u : PolarPoint → ℝ) : PolarPoint → ℝ :=
  u - referenceBasisProjection {0, 1} u

theorem n05_referenceAngularBasis_eq_evenCosineBasis (n : ℕ) :
    referenceAngularBasis n = evenCosineBasis n := by
  cases n with
  | zero => exact evenCosineBasis_zero.symm
  | succ n => exact (evenCosineBasis_of_ne_zero (Nat.succ_ne_zero n)).symm

theorem n05_evenFourierCoefficient_eq_referenceRadialCoefficient
    (u : PolarPoint → ℝ) (n : ℕ) :
    evenFourierCoefficient u n = referenceRadialCoefficient u n := by
  funext r
  simp only [evenFourierCoefficient, referenceRadialCoefficient, referenceAngularCoefficient,
    n05_referenceAngularBasis_eq_evenCosineBasis, angularPairing, angularAverage,
    radialAngularMean, one_div]

theorem n05_evenPartialSum_eq_referenceBasisProjection
    (u : PolarPoint → ℝ) (N : ℕ) :
    r11bEvenPartialSum (evenFourierCoefficient u) N =
      referenceBasisProjection (Finset.range N) u := by
  funext x
  simp only [r11bEvenPartialSum, referenceBasisProjection, angularBasisProjection,
    n05_evenFourierCoefficient_eq_referenceRadialCoefficient,
    referenceRadialCoefficient, n05_referenceAngularBasis_eq_evenCosineBasis]

theorem n05_range_eq_low_union_high (N : ℕ) :
    Finset.range (N + 2) =
      ({0, 1} : Finset ℕ) ∪ (Finset.range N).image (fun n => n + 2) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image]
  constructor
  · intro hk
    by_cases hk2 : k < 2
    · exact Or.inl (by omega)
    · exact Or.inr ⟨k - 2, by omega, by omega⟩
  · rintro ((h0 | h1) | ⟨n, hn, he⟩) <;> omega

theorem n05_referenceHighProjection_range_split (u : PolarPoint → ℝ) (N : ℕ) :
    referenceBasisProjection (Finset.range (N + 2)) u -
        referenceBasisProjection {0, 1} u =
      referenceBasisProjection ((Finset.range N).image (fun n => n + 2)) u := by
  have hI : ∀ k ∈ (Finset.range N).image (fun n => n + 2), 2 ≤ k := by
    intro k hk
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hk
    omega
  simpa only [← n05_range_eq_low_union_high] using
    n05_referenceBasisProjection_high_sub hI u

theorem n05_referenceHighProjection_tendsto {D : ReferenceData}
    {u : PolarPoint → ℝ} (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hup : ∀ r, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (hue : ∀ r, Function.Even (fun θ => u (r, θ))) :
    ∃ hp : ∀ N, MemLp
      (referenceBasisProjection ((Finset.range N).image (fun n => n + 2)) u)
      2 (radialPhysicalMeasure D),
      ∃ hh : MemLp (n05_referenceHighPart u) 2 (radialPhysicalMeasure D),
        Tendsto (fun N => (hp N).toLp
          (referenceBasisProjection ((Finset.range N).image (fun n => n + 2)) u))
          atTop (𝓝 (hh.toLp (n05_referenceHighPart u))) := by
  have hprod : MemLp u 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu
  have hp (N : ℕ) : MemLp
      (referenceBasisProjection ((Finset.range N).image (fun n => n + 2)) u)
      2 (radialPhysicalMeasure D) := by
    simpa only [radialPhysicalMeasure_eq_prod] using
      memLp_referenceBasisProjection_prod hprod ((Finset.range N).image (fun n => n + 2))
  have hcore : MemLp (referenceBasisProjection {0, 1} u) 2 (radialPhysicalMeasure D) := by
    simpa only [radialPhysicalMeasure_eq_prod] using
      memLp_referenceBasisProjection_prod hprod {0, 1}
  have hh : MemLp (n05_referenceHighPart u) 2 (radialPhysicalMeasure D) := hu.sub hcore
  obtain ⟨hP, hlim⟩ := r11b_even_fourier_partialSums_tendsto hu hup hue
  have hsq := (r11b_tendsto_toLp_iff_integral_sq_sub hP hu).mp hlim
  have hshift := hsq.comp (tendsto_add_atTop_nat 2)
  have hraw (N : ℕ) (x : PolarPoint) :
      r11bEvenPartialSum (evenFourierCoefficient u) (N + 2) x - u x =
        referenceBasisProjection ((Finset.range N).image (fun n => n + 2)) u x -
          n05_referenceHighPart u x := by
    rw [n05_evenPartialSum_eq_referenceBasisProjection,
      ← n05_referenceHighProjection_range_split u N]
    simp only [Pi.sub_apply, n05_referenceHighPart]
    ring
  refine ⟨hp, hh, reference_memLp_tendsto_of_sub_sq hp hh ?_⟩
  simpa only [Function.comp_apply, hraw] using hshift

end ContinuousFlexibility.Radial
