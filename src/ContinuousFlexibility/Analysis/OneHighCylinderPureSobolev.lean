import ContinuousFlexibility.Analysis.OneHighCylinderPureFourierJets
import ContinuousFlexibility.Analysis.OneHighL2Domination
import Mathlib.Tactic.FinCases

/-!
# Sobolev control by the two pure endpoint derivatives

The radial and angular towers are independent genuine derivative towers.
Only their physical L2 membership through the finite order s is needed.
The weighted frequency membership of the output is proved before taking
its real norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

theorem cylinder_sobolev_of_pure_derivatives
    (s : ℕ) (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (r a : ℕ → (ℝ × AddCircle P) → ℂ)
    (hr : ∀ k, Continuous (r k)) (ha : ∀ k, Continuous (a k))
    (hr0 : r 0 = f) (ha0 : a 0 = f)
    (hdr : ∀ k (θ : AddCircle P) (x : ℝ),
      HasDerivAt (fun y : ℝ => r k (y, θ)) (r (k + 1) (x, θ)) x)
    (hda : ∀ k (x y : ℝ),
      HasDerivAt (fun z : ℝ => a k (x, (z : AddCircle P)))
        (a (k + 1) (x, (y : AddCircle P))) y)
    (hr2 : ∀ k, k ≤ s → MemLp (r k) 2 (cylinderPhysicalMeasure P))
    (ha2 : ∀ k, k ≤ s → MemLp (a k) 2 (cylinderPhysicalMeasure P)) :
    MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure ∧
    cylinderSobolevNorm s f hf hf2 ≤ (3 : ℝ) ^ s *
      ((eLpNorm f 2 (cylinderPhysicalMeasure P)).toReal +
        (eLpNorm (r s) 2 (cylinderPhysicalMeasure P)).toReal +
          (eLpNorm (a s) 2 (cylinderPhysicalMeasure P)).toReal) := by
  let F := cylinderFourier f hf hf2
  let R := cylinderFourier (r s) (hr s) (hr2 s le_rfl)
  let A := cylinderFourier (a s) (ha s) (ha2 s le_rfl)
  have hF2 : MemLp F 2 cylinderFrequencyMeasure := cylinderFourier_memLp_two f hf hf2
  have hR2 : MemLp R 2 cylinderFrequencyMeasure :=
    cylinderFourier_memLp_two (r s) (hr s) (hr2 s le_rfl)
  have hA2 : MemLp A 2 cylinderFrequencyMeasure :=
    cylinderFourier_memLp_two (a s) (ha s) (ha2 s le_rfl)
  have hr0F : cylinderFourier (r 0) (hr 0) (hr2 0 (Nat.zero_le s)) = F := by
    subst f
    rfl
  have ha0F : cylinderFourier (a 0) (ha 0) (ha2 0 (Nat.zero_le s)) = F := by
    subst f
    rfl
  have hR : R =ᵐ[cylinderFrequencyMeasure] fun ζ => cylinderDerivativeMultiplier P s 0 ζ * F ζ := by
    have h := cylinderFourier_radialTower_ae r hr hdr s hr2 s le_rfl
    rwa [hr0F] at h
  have hA : A =ᵐ[cylinderFrequencyMeasure] fun ζ => cylinderDerivativeMultiplier P 0 s ζ * F ζ := by
    have h := cylinderFourier_angularTower_ae a ha hda s ha2 s le_rfl
    rwa [ha0F] at h
  let U : Fin 3 → (ℝ × ℤ) → ℝ :=
    Fin.cases (fun ζ => ‖F ζ‖)
      (Fin.cases (fun ζ => ‖R ζ‖) (fun _ => fun ζ => ‖A ζ‖))
  have hU : ∀ i, MemLp (U i) 2 cylinderFrequencyMeasure := by
    intro i
    fin_cases i
    · exact hF2.norm
    · exact hR2.norm
    · exact hA2.norm
  have hpoint : ∀ᵐ ζ ∂cylinderFrequencyMeasure,
      ‖frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P))
        (s : ℝ) F ζ‖ ≤ ∑ i : Fin 3, (3 : ℝ) ^ s * ‖U i ζ‖ := by
    filter_upwards [hR, hA] with ζ hRζ hAζ
    have hp := cylinder_norm_frequencyWeighted_le_pure_multipliers (P := P) F s ζ
    rw [← hRζ, ← hAζ] at hp
    simpa [U, Fin.sum_univ_succ, mul_add, add_assoc] using hp
  have hW := frequencyWeighted_aestronglyMeasurable
    (continuous_cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)).measurable.aemeasurable
    hF2.aestronglyMeasurable (s : ℝ)
  have hD := oneHigh_l2_finite_domination hW U hU (fun _ => (3 : ℝ) ^ s)
    (fun _ => by positivity) hpoint
  refine ⟨hD.1, ?_⟩
  have hb := hD.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, U, Fin.cases_zero, Fin.cases_succ,
    add_zero] at hb
  rw [eLpNorm_norm F hF2.aestronglyMeasurable,
    eLpNorm_norm R hR2.aestronglyMeasurable,
    eLpNorm_norm A hA2.aestronglyMeasurable] at hb
  dsimp only [F, R, A] at hb
  rw [cylinderFourier_eLpNorm_two f hf hf2,
    cylinderFourier_eLpNorm_two (r s) (hr s) (hr2 s le_rfl),
    cylinderFourier_eLpNorm_two (a s) (ha s) (ha2 s le_rfl)] at hb
  simpa only [cylinderSobolevNorm, frequencySobolevNorm, mul_add, add_assoc] using hb

theorem cylinder_frequencyWeighted_memLp_of_pure_derivatives
    (s : ℕ) (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (r a : ℕ → (ℝ × AddCircle P) → ℂ)
    (hr : ∀ k, Continuous (r k)) (ha : ∀ k, Continuous (a k))
    (hr0 : r 0 = f) (ha0 : a 0 = f)
    (hdr : ∀ k (θ : AddCircle P) (x : ℝ),
      HasDerivAt (fun y : ℝ => r k (y, θ)) (r (k + 1) (x, θ)) x)
    (hda : ∀ k (x y : ℝ),
      HasDerivAt (fun z : ℝ => a k (x, (z : AddCircle P)))
        (a (k + 1) (x, (y : AddCircle P))) y)
    (hr2 : ∀ k, k ≤ s → MemLp (r k) 2 (cylinderPhysicalMeasure P))
    (ha2 : ∀ k, k ≤ s → MemLp (a k) 2 (cylinderPhysicalMeasure P)) :
    MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier f hf hf2)) 2 cylinderFrequencyMeasure :=
  (cylinder_sobolev_of_pure_derivatives s f hf hf2 r a hr ha hr0 ha0 hdr hda hr2 ha2).1

theorem cylinder_sobolevNorm_le_pure_derivatives
    (s : ℕ) (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (r a : ℕ → (ℝ × AddCircle P) → ℂ)
    (hr : ∀ k, Continuous (r k)) (ha : ∀ k, Continuous (a k))
    (hr0 : r 0 = f) (ha0 : a 0 = f)
    (hdr : ∀ k (θ : AddCircle P) (x : ℝ),
      HasDerivAt (fun y : ℝ => r k (y, θ)) (r (k + 1) (x, θ)) x)
    (hda : ∀ k (x y : ℝ),
      HasDerivAt (fun z : ℝ => a k (x, (z : AddCircle P)))
        (a (k + 1) (x, (y : AddCircle P))) y)
    (hr2 : ∀ k, k ≤ s → MemLp (r k) 2 (cylinderPhysicalMeasure P))
    (ha2 : ∀ k, k ≤ s → MemLp (a k) 2 (cylinderPhysicalMeasure P)) :
    cylinderSobolevNorm s f hf hf2 ≤ (3 : ℝ) ^ s *
      ((eLpNorm f 2 (cylinderPhysicalMeasure P)).toReal +
        (eLpNorm (r s) 2 (cylinderPhysicalMeasure P)).toReal +
          (eLpNorm (a s) 2 (cylinderPhysicalMeasure P)).toReal) :=
  (cylinder_sobolev_of_pure_derivatives s f hf hf2 r a hr ha hr0 ha0 hdr hda hr2 ha2).2

end ContinuousFlexibility.Analysis
