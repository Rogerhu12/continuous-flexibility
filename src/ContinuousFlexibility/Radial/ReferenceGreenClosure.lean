import ContinuousFlexibility.Radial.ReferenceGraphNorms
import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# Passage of Green reciprocity from a smooth core to the weighted graph

The physical pairing is continuous when both entries converge in L².
The already established physical square bounds transfer the actual graph
norm convergence to that Hilbert topology, including both scalar components.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
open ContinuousFlexibility.Statements

theorem reference_mean_pairing_tendsto_of_sub_sq {D : ReferenceData}
    (hab : D.a ≤ D.b) {u v : ℕ → PolarPoint → ℝ} {u₀ v₀ : PolarPoint → ℝ}
    (hu : ∀ n, MemLp (u n) 2 (radialPhysicalMeasure D))
    (hv : ∀ n, MemLp (v n) 2 (radialPhysicalMeasure D))
    (hu₀ : MemLp u₀ 2 (radialPhysicalMeasure D))
    (hv₀ : MemLp v₀ 2 (radialPhysicalMeasure D))
    (huc : Tendsto (fun n => ∫ x, (u n x - u₀ x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0))
    (hvc : Tendsto (fun n => ∫ x, (v n x - v₀ x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r in D.a..D.b,
      radialAngularMean (fun θ => u n (r, θ) * v n (r, θ))) atTop
        (𝓝 (∫ r in D.a..D.b, radialAngularMean (fun θ => u₀ (r, θ) * v₀ (r, θ)))) := by
  have ht := (reference_memLp_tendsto_of_sub_sq hu hu₀ huc).inner (𝕜 := ℝ)
    (reference_memLp_tendsto_of_sub_sq hv hv₀ hvc)
  simp only [reference_memLp_inner_eq_integral] at ht
  have heq (n : ℕ) :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => u n (r, θ) * v n (r, θ))) =
        (2 * Real.pi)⁻¹ * ∫ x, u n x * v n x ∂radialPhysicalMeasure D :=
    r11b_integral_angularMean_eq hab ((hu n).integrable_mul (hv n))
  have hlim :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => u₀ (r, θ) * v₀ (r, θ))) =
        (2 * Real.pi)⁻¹ * ∫ x, u₀ x * v₀ x ∂radialPhysicalMeasure D :=
    r11b_integral_angularMean_eq hab (hu₀.integrable_mul hv₀)
  simpa only [heq, hlim] using ht.const_mul ((2 * Real.pi)⁻¹)

/-- Once Green's formula is proved on the actual smooth graph, graph-core
density extends it to the full maximal weighted graph. -/
theorem referenceGreenReciprocity_of_smoothCoreClosure {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    (hsmooth : ∀ U V F K, ReferenceGraph D γ M₀ M₁ U F →
      ReferenceGraph D γ M₀ M₁ V K →
      SmoothAdmissibleField D U → SmoothAdmissibleField D V →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => U.1 (r, θ) * K.1 (r, θ))) +
          U.2 * K.2 =
        (∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * V.1 (r, θ))) +
          F.2 * V.2) :
    ReferenceGreenReciprocity D γ M₀ M₁ := by
  intro U V F K hUF hVK
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hu : MemLp U.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ hUF.1
  have hv : MemLp V.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ hVK.1
  have hf : MemLp F.1 2 (radialPhysicalMeasure D) :=
    r11b_source_memLp hD hγ hUF.2.1
  have hk : MemLp K.1 2 (radialPhysicalMeasure D) :=
    r11b_source_memLp hD hγ hVK.2.1
  refine ⟨hu.integrable_mul hk, hf.integrable_mul hv, ?_⟩
  obtain ⟨Us, Fs, a, hUs, hFsconv, hUsconv⟩ := hcore U F hUF
  obtain ⟨Vs, Ks, b, hVs, hKsconv, hVsconv⟩ := hcore V K hVK
  have hus : ∀ n, MemLp (Us n).1 2 (radialPhysicalMeasure D) :=
    fun n => r11b_output_memLp hD hborder hγ (hUs n).1.1
  have hvs : ∀ n, MemLp (Vs n).1 2 (radialPhysicalMeasure D) :=
    fun n => r11b_output_memLp hD hborder hγ (hVs n).1.1
  have hfs : ∀ n, MemLp (Fs n).1 2 (radialPhysicalMeasure D) :=
    fun n => r11b_source_memLp hD hγ (hUs n).1.2.1
  have hks : ∀ n, MemLp (Ks n).1 2 (radialPhysicalMeasure D) :=
    fun n => r11b_source_memLp hD hγ (hVs n).1.2.1
  have huc := referenceOutput_sub_sq_tendsto hD hborder hγ
    (fun n => (hUs n).2.2) hUsconv
  have hvc := referenceOutput_sub_sq_tendsto hD hborder hγ
    (fun n => (hVs n).2.2) hVsconv
  have hfc := referenceSource_sub_sq_tendsto hD hγ
    (fun n => (hUs n).1.2.1) hUF.2.1 hFsconv
  have hkc := referenceSource_sub_sq_tendsto hD hγ
    (fun n => (hVs n).1.2.1) hVK.2.1 hKsconv
  have huScalar := referenceOutput_scalar_tendsto hD hborder hγ
    (fun n => (hUs n).2.2) hUsconv
  have hvScalar := referenceOutput_scalar_tendsto hD hborder hγ
    (fun n => (hVs n).2.2) hVsconv
  have hfScalar := referenceSource_scalar_tendsto hD hγ
    (fun n => (hUs n).1.2.1) hUF.2.1 hFsconv
  have hkScalar := referenceSource_scalar_tendsto hD hγ
    (fun n => (hVs n).1.2.1) hVK.2.1 hKsconv
  have hleft :=
    (reference_mean_pairing_tendsto_of_sub_sq hgeom.2.1.le hus hks hu hk huc hkc).add
      (huScalar.mul hkScalar)
  have hright :=
    (reference_mean_pairing_tendsto_of_sub_sq hgeom.2.1.le hfs hvs hf hv hfc hvc).add
      (hfScalar.mul hvScalar)
  have heq (n : ℕ) :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => (Us n).1 (r, θ) * (Ks n).1 (r, θ))) +
          (Us n).2 * (Ks n).2 =
        (∫ r in D.a..D.b, radialAngularMean (fun θ => (Fs n).1 (r, θ) * (Vs n).1 (r, θ))) +
          (Fs n).2 * (Vs n).2 :=
    hsmooth (Us n) (Vs n) (Fs n) (Ks n)
      (hUs n).1 (hVs n).1 (hUs n).2.1 (hVs n).2.1
  apply tendsto_nhds_unique hleft
  simpa only [heq] using hright

end ContinuousFlexibility.Radial
