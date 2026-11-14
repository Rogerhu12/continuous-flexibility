module

public import ContinuousFlexibility.Radial.R11bLocalL2
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of compact radial test pairings

A field that is physically L² on every compact radial subset can be paired
with every continuous test supported in such a subset. The proof uses the
actual product on the physical strip: Hölder on the compact restriction,
followed by extension through its measurable indicator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

/-- An abstract local-L² hypothesis suffices for every compact radial
continuous test. No parity, periodicity, or differential equation is used. -/
theorem r11b_pairing_integrable_of_local_memLp {D : ReferenceData}
    {f ψ : PolarPoint → ℝ}
    (hlocal : ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore D →
      MemLp f 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))))
    (hψ : Continuous ψ)
    (hsupp : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) :
    Integrable (fun x : PolarPoint => f x * ψ x) (radialPhysicalMeasure D) := by
  classical
  obtain ⟨K, hK, hKcore, hzero⟩ := hsupp
  let S : Set PolarPoint := K ×ˢ (Set.univ : Set ℝ)
  have hS : MeasurableSet S := hK.isClosed.measurableSet.prod MeasurableSet.univ
  have hfK : MemLp f 2 ((radialPhysicalMeasure D).restrict S) :=
    hlocal K hK hKcore
  have hψK : MemLp ψ 2 ((radialPhysicalMeasure D).restrict S) :=
    MemLp.mono_measure
      (μ := radialPhysicalMeasure D) (ν := (radialPhysicalMeasure D).restrict S)
      Measure.restrict_le_self (r11b_continuous_memLp (D := D) hψ)
  have hprod : Integrable (fun x : PolarPoint => f x * ψ x)
      ((radialPhysicalMeasure D).restrict S) := hfK.integrable_mul hψK
  have hindicator : Integrable (S.indicator (fun x : PolarPoint => f x * ψ x))
      (radialPhysicalMeasure D) := (integrable_indicator_iff hS).2 hprod
  have heq : S.indicator (fun x : PolarPoint => f x * ψ x) =
      (fun x : PolarPoint => f x * ψ x) := by
    funext x
    by_cases hx : x ∈ S
    · exact Set.indicator_of_mem hx _
    · have hr : x.1 ∉ K := fun hr => hx ⟨hr, Set.mem_univ _⟩
      simp only [Set.indicator_of_notMem hx, hzero x.1 hr x.2, mul_zero]
  rw [heq] at hindicator
  exact hindicator

theorem r11b_cell_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hψ : Continuous ψ)
    (hsupp : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) :
    Integrable (fun x : PolarPoint => f x * ψ x) (radialPhysicalMeasure D) :=
  r11b_pairing_integrable_of_local_memLp
    (fun K hK hKcore => r11b_cell_memLp_on_compact_of_profile hD hK hKcore hf)
    hψ hsupp

theorem r11b_source_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) {ψ : PolarPoint → ℝ} (hψ : Continuous ψ)
    (hsupp : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) :
    Integrable (fun x : PolarPoint => F.1 x * ψ x) (radialPhysicalMeasure D) :=
  r11b_cell_pairing_integrable hD hF.1 hψ hsupp

theorem r11b_sourceDerivative_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ M fθ) {ψ : PolarPoint → ℝ} (hψ : Continuous ψ)
    (hsupp : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) :
    Integrable (fun x : PolarPoint => fθ x * ψ x) (radialPhysicalMeasure D) :=
  r11b_cell_pairing_integrable hD hfθ.1 hψ hsupp

/-- For an output, the local-L² theorem adds back its smooth left-tail term. -/
theorem r11b_output_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} {U : RadialUnknown} (hU : OutputMember D γ M U)
    {ψ : PolarPoint → ℝ} (hψ : Continuous ψ)
    (hsupp : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) :
    Integrable (fun x : PolarPoint => U.1 x * ψ x) (radialPhysicalMeasure D) :=
  r11b_pairing_integrable_of_local_memLp
    (fun K hK hKcore => r11b_output_memLp_on_compact hD hborder hK hKcore hU)
    hψ hsupp

theorem r11b_radialTest_pairing_integrable_of_local_memLp {D : ReferenceData}
    {f ψ : PolarPoint → ℝ}
    (hlocal : ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore D →
      MemLp f 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))))
    (hψ : RadialTest D ψ) :
    Integrable (fun x : PolarPoint => f x * ψ x) (radialPhysicalMeasure D) :=
  r11b_pairing_integrable_of_local_memLp hlocal hψ.1.continuous hψ.2.2

theorem r11b_cell_radialTest_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hψ : RadialTest D ψ) :
    Integrable (fun x : PolarPoint => f x * ψ x) (radialPhysicalMeasure D) :=
  r11b_cell_pairing_integrable hD hf hψ.1.continuous hψ.2.2

theorem r11b_source_radialTest_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    Integrable (fun x : PolarPoint => F.1 x * ψ x) (radialPhysicalMeasure D) :=
  r11b_cell_radialTest_pairing_integrable hD hF.1 hψ

theorem r11b_sourceDerivative_radialTest_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ M fθ) {ψ : PolarPoint → ℝ}
    (hψ : RadialTest D ψ) :
    Integrable (fun x : PolarPoint => fθ x * ψ x) (radialPhysicalMeasure D) :=
  r11b_cell_radialTest_pairing_integrable hD hfθ.1 hψ

theorem r11b_output_radialTest_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} {U : RadialUnknown} (hU : OutputMember D γ M U)
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    Integrable (fun x : PolarPoint => U.1 x * ψ x) (radialPhysicalMeasure D) :=
  r11b_output_pairing_integrable hD hborder hU hψ.1.continuous hψ.2.2

end ContinuousFlexibility.Radial
