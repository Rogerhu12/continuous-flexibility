module

public import ContinuousFlexibility.Radial.MatchedPhysicalScalarGate
public import ContinuousFlexibility.Radial.MatchedModeMeasureEmbedding
public import ContinuousFlexibility.Radial.MatchedModePhysicalEquation
public import ContinuousFlexibility.Radial.ReferenceSourceEnergy

/-!
# Positive reference modes from the actual scalar-gated Schur estimate

The source is divided by the true Hilbert density with the model sign.
The given inverse solves the actual modal graph. Its raw scalar-gated
Schur bounds prove membership in the desired weighted output space;
changing to that L² representative preserves the ordinary weak equation
and the physical bordered row. The scalar appears only at frequency two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff
open ContinuousFlexibility.Radial

/-- A single source threshold and Schur constant work before choosing the
operators, attenuation, source, or target loss. The conclusions are the
positive-mode inputs of `referenceSolution_of_radial_modes`. -/
theorem exists_referencePositiveSchurAssembly {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ Mmin C : ℝ, 0 < Mmin ∧ 0 < C ∧
      ∀ (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
        (γ M₀ M₁ : ℝ) (K : ℕ → ℕ → ℕ → ℝ),
      (∀ n : ℕ, ModeInverseProperties D (2 * (n + 1)) (G n)) →
      0 ≤ γ → Mmin ≤ M₀ →
      (∀ n k m, 0 ≤ K n k m) →
      (∀ n k, Summable (K n k) ∧ ∑' m, K n k m ≤ A) →
      (∀ n m, Summable (fun k => K n k m) ∧ ∑' k, K n k m ≤ B) →
      (∀ n k m,
        matchedPhysicalChannelWeight D γ (-M₁) k *
            matchedPhysicalRawKernel D hD hD.choose_spec.2.1
              (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
          K n k m * matchedPhysicalChannelWeight D γ M₀ m) →
      ∀ (F : RadialSource) (hF : SourceMember D γ M₀ F),
      ∃ (u : ℕ → Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁))) (ν : ℝ),
        (∀ n : ℕ, ‖u n‖ ^ 2 + (if n = 0 then ν ^ 2 else 0) ≤
          C ^ 2 * (‖referenceSourceCosineAnalysis
            (matchingProfileGeometry hD).2.1.le hD.choose_spec.2.1 hF (n + 1)‖ ^ 2 +
            if n = 0 then F.2 ^ 2 else 0)) ∧
        (∫ r in D.a..D.b, referenceColumn D r * u 0 r) = F.2 ∧
        (∀ (n : ℕ) (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ radialCore D →
          (∫ r in D.a..D.b, u n r *
            radialJacobi (((2 * (n + 1) : ℕ) : ℝ) ^ 2) D.w φ r) +
            (if n = 0 then ν else 0) *
              (∫ r in D.a..D.b, referenceColumn D r * φ r) =
          ∫ r in D.a..D.b, referenceCosineCoefficient F.1 (n + 1) r * φ r) := by
  have hP : RadialPartition D := hD.choose_spec.2.1
  have hab : D.a ≤ D.b := (matchingProfileGeometry hD).2.1.le
  obtain ⟨Mmin, hMmin, hsource⟩ := exists_matchedMode_source_memLp hD
  obtain ⟨C, hC, hschur⟩ := exists_matchedPhysicalSchur_uniform_bound hD hP hA hB
  refine ⟨Mmin, C, hMmin, hC, ?_⟩
  intro G γ M₀ M₁ K hG hγ hM₀ hK hKrow hKcol hmajor F hF
  let f : ℕ → ℝ → ℝ := fun n => referenceCosineCoefficient F.1 (n + 1)
  have hf (n : ℕ) : MemLp (f n) 2 (referenceRadialWeightedMeasure D γ M₀) :=
    hF.cosineCoefficient_memLp hab hP (n + 1)
  have hmodel (n : ℕ) :
      MemLp (fun r => -f n r / matchingDensity D r) 2 (radialHilbertMeasure D) :=
    hsource M₀ hM₀ γ hγ (f n) (hf n)
  let t : ℕ → ℝ := fun n => if n = 0 then F.2 else 0
  let X : ℕ → RadialModePair D := fun n =>
    matchedModePhysicalSource D (f n) (hmodel n) (t n)
  let W : ℕ → RadialModePair D := fun n => matchedModePhysicalSolution (G n) (X n)
  have hactive (n : ℕ) : 2 * (n + 1) ≠ 2 → t n = 0 := by
    intro hj
    have hn : n ≠ 0 := by omega
    simp only [t, if_neg hn]
  have hgate (n : ℕ) :
      (G n ∘L matchedModeScalarGate D (decide (n = 0))) (X n) = G n (X n) := by
    apply matchedMode_scalarGate_apply_inverse
    intro hfalse
    change t n = 0
    by_cases hn : n = 0
    · simp [hn] at hfalse
    · simp only [t, if_neg hn]
  have hraw (n : ℕ) :
      MemLp ((G n (X n)).1 : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ (-M₁)) ∧
        ((∫ r, (G n (X n)).1 r ^ 2 ∂referenceRadialWeightedMeasure D γ (-M₁)) +
          (G n (X n)).2 ^ 2) ≤
        C ^ 2 * ((∫ r, f n r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) + (t n) ^ 2) := by
    have hh := hschur (G n ∘L matchedModeScalarGate D (decide (n = 0)))
      γ M₀ (-M₁) (K n) hγ (hMmin.le.trans hM₀)
      (hK n) (hKrow n) (hKcol n) (hmajor n) (f n) (hf n) (X n)
      (matchedModePhysicalSource_ae D (f n) (hmodel n) (t n))
    rw [hgate n] at hh
    exact hh
  have hout (n : ℕ) :
      MemLp ((W n).1 : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ (-M₁)) :=
    (hraw n).1
  let u : ℕ → Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M₁)) :=
    fun n => (hout n).toLp ((W n).1 : ℝ → ℝ)
  let ν : ℝ := (W 0).2
  have hsol (n : ℕ) := matchedModePhysicalSolution_solves hD (hG n)
    (f n) (hmodel n) (t n) (hactive n)
  have hscalar (n : ℕ) : (W n).2 = if n = 0 then ν else 0 := by
    by_cases hn : n = 0
    · subst n
      simp only [ν, if_pos rfl, ite_true]
    · have hj : 2 * (n + 1) ≠ 2 := by omega
      have hz := (hsol n).2
      rw [if_neg hj] at hz
      rw [if_neg hn]
      exact hz.1
  have hu (n : ℕ) :
      (u n : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (W n).1 := by
    apply (radialHilbertMeasure_ae_iff hD).mpr
    apply (matchedRadialWeighted_ae_iff hP γ (-M₁)).mp
    exact (hout n).coeFn_toLp
  have henergy (n : ℕ) :
      ‖u n‖ ^ 2 + (W n).2 ^ 2 ≤
        C ^ 2 * (‖referenceSourceCosineAnalysis hab hP hF (n + 1)‖ ^ 2 + (t n) ^ 2) := by
    change ‖(hout n).toLp ((W n).1 : ℝ → ℝ)‖ ^ 2 + (W n).2 ^ 2 ≤ _
    rw [referenceL2_toLp_norm_sq, referenceSourceCosineAnalysis_energy hab hP hF (n + 1)]
    have hs : (W n).2 ^ 2 = (G n (X n)).2 ^ 2 := by
      change (-(G n (X n)).2) ^ 2 = (G n (X n)).2 ^ 2
      exact neg_sq _
    rw [hs]
    exact (hraw n).2
  refine ⟨u, ν, ?_, ?_, ?_⟩
  · intro n
    have he := henergy n
    rw [hscalar n] at he
    by_cases hn : n = 0
    · simpa only [t, if_pos hn, ite_true] using he
    · simpa only [t, if_neg hn, ite_false, zero_pow (by decide : (2 : ℕ) ≠ 0)] using he
  · calc
      (∫ r in D.a..D.b, referenceColumn D r * u 0 r) =
          ∫ r in D.a..D.b, referenceColumn D r * (W 0).1 r := by
        apply matchingInterval_congr_ae hD
        filter_upwards [hu 0] with r hr
        rw [hr]
      _ = F.2 := by
        simpa [W, X, t] using (hsol 0).2
  · intro n φ hφ hcφ hsφ
    have hw := (hsol n).1 φ hφ hcφ ((subset_tsupport φ).trans hsφ)
    have hi :
        (∫ r in D.a..D.b, u n r *
          radialJacobi (((2 * (n + 1) : ℕ) : ℝ) ^ 2) D.w φ r) =
        ∫ r in D.a..D.b, (W n).1 r *
          radialJacobi (((2 * (n + 1) : ℕ) : ℝ) ^ 2) D.w φ r := by
      apply matchingInterval_congr_ae hD
      filter_upwards [hu n] with r hr
      rw [hr]
    rw [hi, ← hscalar n]
    exact hw

end ContinuousFlexibility.Statements
