import ContinuousFlexibility.Analysis.N07aLocalizedWeakJets

/-!
# Classical first jets of a localized canonical weak class

The cylinder reconstruction identifies the genuine first derivatives of
the smooth localized representative with the product-rule weak classes.
This is used to identify classical jets after gluing the local pieces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_exists_smooth_localizedCanonical_first {χ : PolarPoint → ℝ}
    (hχ : CanonicalTest S K m χ) (u : CanonicalL2 S K m)
    (hu : ∀ n, N07aCanonicalNormalRegular S K m u n) :
    ∃ v : PolarPoint → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v (0, Real.pi) ∧
      v =ᵐ[canonicalMeasure S K m] (fun p => χ p * u p) ∧
      ∀ (j : Fin 2) (du : CanonicalL2 S K m),
        N07aWeakCanonicalMixedDerivative S K m u du
          (n07aFirstOrder j).1 (n07aFirstOrder j).2 →
        mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 v
          =ᵐ[canonicalMeasure S K m]
            (fun p => χ p * du p +
              mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ p * u p) := by
  choose d hd using fun a b => n07a_canonicalLocalization_allMixed a b χ hχ u hu
  obtain ⟨v, hv, hvp, hveq, _⟩ := n07a_exists_smooth_cylinderRepresentative
    (n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u)) d hd
  have hzero : d 0 0 = n07aCanonicalExtension (n07aSmoothCanonicalMul χ hχ.1 u) :=
    hasWeakMixedDerivative_unique (hd 0 0) (n07a_cylinderWeak_refl _)
  have he := hveq 0 0
  rw [spaces_mixedDerivative_zero, hzero] at he
  have hmeasure : canonicalMeasure S K m ≤ materialCylinderMeasure := by
    rw [n07a_canonicalMeasure_eq_cylinder_restrict]
    exact Measure.restrict_le_self
  refine ⟨v, hv, hvp, (he.filter_mono (ae_mono hmeasure)).trans
    ((n07aCanonicalExtension_restrict_ae _).trans
      (n07aSmoothCanonicalMul_ae χ hχ.1 u)), ?_⟩
  intro j du hdu
  let dχ := mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ
  have hdχ : ContDiff ℝ ∞ dχ := contDiff_mixedDerivative hχ.1 _ _
  let v₁ := n07aSmoothCanonicalMul χ hχ.1 du
  let v₂ := n07aSmoothCanonicalMul dχ hdχ u
  have hjet : d (n07aFirstOrder j).1 (n07aFirstOrder j).2 =
      n07aCanonicalExtension v₁ + n07aCanonicalExtension v₂ :=
    hasWeakMixedDerivative_unique (hd _ _)
      (n07a_canonicalLocalization_first hχ j hdu)
  have hejet := (hveq (n07aFirstOrder j).1 (n07aFirstOrder j).2).filter_mono
    (ae_mono hmeasure)
  rw [hjet] at hejet
  have hsum := (Lp.coeFn_add (n07aCanonicalExtension v₁)
    (n07aCanonicalExtension v₂)).filter_mono (ae_mono hmeasure)
  filter_upwards [hejet, hsum,
    n07aCanonicalExtension_restrict_ae v₁, n07aCanonicalExtension_restrict_ae v₂,
    n07aSmoothCanonicalMul_ae χ hχ.1 du, n07aSmoothCanonicalMul_ae dχ hdχ u]
    with p hp hs h₁ h₂ hχ₁ hχ₂
  exact hp.trans (hs.trans (congrArg₂ (· + ·) (h₁.trans hχ₁) (h₂.trans hχ₂)))

end ContinuousFlexibility.Analysis
