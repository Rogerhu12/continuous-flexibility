import ContinuousFlexibility.Radial.InnerGapPoissonMatrix
import ContinuousFlexibility.Radial.InnerRadialL2Mass
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual gap Poisson operator in the radial Hilbert space

The Poisson function is extended by zero into the existing physical
radial measure. This produces one continuous linear operator on the
Euclidean boundary space. Its norm is the physical mass, its quantitative
bound follows from the actual gap energy, and its adjoint pairs with
arbitrary L² sources through the physical radial integral.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

/-- Zero extension of the actual gap Poisson solution into the existing
radial Hilbert space. Continuity follows from finite-dimensionality of
the boundary source; the quantitative bound is proved separately. -/
def innerGapPoissonL2 (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] RadialModeL2 D := by
  let T : EuclideanSpace ℝ (Fin 2) → RadialModeL2 D := fun ξ =>
    innerRadialIntervalToLp D hw ha hcore hpos (innerGapPoisson p ξ)
      (innerGapPoisson_contDiff p hp ξ).continuous.continuousOn
  have hT : ∀ ξ, T ξ =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator (innerGapPoisson p ξ) :=
    fun ξ => innerRadialIntervalToLp_ae D hw ha hcore hpos (innerGapPoisson p ξ)
      (innerGapPoisson_contDiff p hp ξ).continuous.continuousOn
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] RadialModeL2 D :=
    { toFun := T
      map_add' := by
        intro ξ η
        apply Lp.ext
        filter_upwards [hT (ξ + η), hT ξ, hT η, Lp.coeFn_add (T ξ) (T η)]
          with r hsum hξ hη hadd
        simp only [hsum, hadd, Pi.add_apply, hξ, hη]
        by_cases hr : r ∈ Ioo a b
        · simp only [indicator_of_mem hr, map_add, Pi.add_apply]
        · simp only [indicator_of_notMem hr, zero_add]
      map_smul' := by
        intro c ξ
        apply Lp.ext
        filter_upwards [hT (c • ξ), hT ξ, Lp.coeFn_smul c (T ξ)] with r hsmul hξ hcoe
        simp only [RingHom.id_apply, hsmul, hcoe, Pi.smul_apply, hξ]
        by_cases hr : r ∈ Ioo a b
        · simp only [indicator_of_mem hr, map_smul, Pi.smul_apply]
        · simp only [indicator_of_notMem hr, smul_zero] }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

theorem innerGapPoissonL2_apply (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapPoissonL2 D hw ha hcore hpos p hp ξ =
      innerRadialIntervalToLp D hw ha hcore hpos (innerGapPoisson p ξ)
        (innerGapPoisson_contDiff p hp ξ).continuous.continuousOn := rfl

theorem innerGapPoissonL2_ae (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapPoissonL2 D hw ha hcore hpos p hp ξ =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapPoisson p ξ) := by
  rw [innerGapPoissonL2_apply]
  exact innerRadialIntervalToLp_ae D hw ha hcore hpos (innerGapPoisson p ξ)
    (innerGapPoisson_contDiff p hp ξ).continuous.continuousOn

theorem innerGapPoissonL2_support (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b →
      innerGapPoissonL2 D hw ha hcore hpos p hp ξ r = 0 := by
  filter_upwards [innerGapPoissonL2_ae D hw ha hcore hpos p hp ξ] with r hr
  intro hout
  rw [hr, indicator_of_notMem hout]

/-- This equality uses exactly the physical radial density. -/
theorem innerGapPoissonL2_norm_sq (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖innerGapPoissonL2 D hw ha hcore hpos p hp ξ‖ ^ 2 =
      innerRadialGapMass D.w (innerGapPoisson p ξ) a b := by
  rw [innerGapPoissonL2_apply]
  exact innerRadialIntervalToLp_norm_sq D hw hab ha hcore hpos (innerGapPoisson p ξ)
    (innerGapPoisson_contDiff p hp ξ).continuous.continuousOn

theorem innerGapPoissonL2_norm (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖innerGapPoissonL2 D hw ha hcore hpos p hp ξ‖ =
      Real.sqrt (innerRadialGapMass D.w (innerGapPoisson p ξ) a b) := by
  calc
    _ = Real.sqrt (‖innerGapPoissonL2 D hw ha hcore hpos p hp ξ‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := congrArg Real.sqrt (innerGapPoissonL2_norm_sq D hw hab ha hcore hpos p hp ξ)

/-- The frequency estimate for the actual Hilbert-space Poisson map,
derived from radial coercivity and the actual flux matrix. -/
theorem innerGapPoissonL2_norm_le (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (hstrict : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖innerGapPoissonL2 D hw.continuous ha hcore hpos p hp ξ‖ ≤
      (Real.sqrt (12 / s) / j) * Real.sqrt ⟪ξ, innerGapFluxOperator D.w a b p ξ⟫_ℝ := by
  rw [innerGapPoissonL2_norm D hw.continuous hab ha hcore hpos p hp ξ]
  exact innerGapPoisson_sqrt_mass_le hab ha hj hs hw p hp hb heq hstrict hslope ξ

/-- The Hilbert pairing with every L² source is the physical integral on
the retained gap. No smoothness assumption is made on the source. -/
theorem innerGapPoissonL2_inner (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) (F : RadialModeL2 D) :
    ⟪innerGapPoissonL2 D hw ha hcore hpos p hp ξ, F⟫_ℝ =
      ∫ r in Ioo a b, (12 * D.w r / r ^ 2) * F r * innerGapPoisson p ξ r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, (Ioo a b).indicator (fun r => F r * innerGapPoisson p ξ r) r
        ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards [innerGapPoissonL2_ae D hw ha hcore hpos p hp ξ] with r hr
      rw [hr]
      by_cases hmem : r ∈ Ioo a b
      · simp only [indicator_of_mem hmem, RCLike.inner_apply, conj_trivial] <;> ring
      · simp only [indicator_of_notMem hmem, inner_zero_left]
    _ = ∫ r in Ioo a b, F r * innerGapPoisson p ξ r ∂radialHilbertMeasure D :=
      integral_indicator measurableSet_Ioo
    _ = _ := by
      rw [innerRadialInterval_integral D hw hcore hpos]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r _
      ring

theorem innerGapPoissonL2_adjoint_pairing (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) (F : RadialModeL2 D) :
    ⟪ξ, (innerGapPoissonL2 D hw ha hcore hpos p hp).adjoint F⟫_ℝ =
      ∫ r in Ioo a b, (12 * D.w r / r ^ 2) * F r * innerGapPoisson p ξ r := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact innerGapPoissonL2_inner D hw ha hcore hpos p hp ξ F

end ContinuousFlexibility.Radial
