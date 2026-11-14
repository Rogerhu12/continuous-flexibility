module

public import ContinuousFlexibility.Analysis.N07aCanonicalBandAngular
public import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients

/-!
# Actual coefficient products between angular modes

The coefficient of a product is computed from the existing L²
representative and the actual circle multiplication matrix. Radial
factors remain arbitrary measurable representatives throughout.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalProduct_coefficient_ae
    (χ : N07aCanonicalOpenCoefficient S K m) {u : CanonicalL2 S K m}
    {f g : ℝ → ℝ}
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun p => f p.1 * g p.2)
    (l : ℕ) :
    n07aHalfRadialCoefficient (χ.mul u) l =ᵐ[
        volume.restrict (Ioo (K.left m) (K.right m))]
      fun r => f r * (Real.pi⁻¹ * ∫ θ, χ.value (r, θ) * g θ * referenceAngularBasis l θ
        ∂angleMeasure) := by
  have he : (χ.mul u : PolarPoint → ℝ) =ᵐ[
      (volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure]
      fun p => χ.value p * (f p.1 * g p.2) := by
    have he' := (χ.mul_ae u).trans (hu.mono fun p hp => congrArg (χ.value p * ·) hp)
    simpa only [n07aCanonicalMeasure_eq_prod] using he'
  filter_upwards [n07aHalfRadialCoefficient_congr_ae he l] with r hr
  rw [hr]
  unfold n07aHalfRadialCoefficient
  have hfun : (fun θ => χ.value (r, θ) * (f r * g θ) * referenceAngularBasis l θ) =
      fun θ => f r * (χ.value (r, θ) * g θ * referenceAngularBasis l θ) := by
    funext θ
    ring
  rw [hfun, integral_const_mul]
  unfold angleMeasure
  change Real.pi⁻¹ * (f r * _) = f r * (Real.pi⁻¹ * _)
  ring

theorem n07aCanonicalProduct_unitMode_ae (hm : K.left m < K.right m)
    (χ : N07aCanonicalOpenCoefficient S K m) {u : CanonicalL2 S K m}
    {f g : ℝ → ℝ}
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun p => f p.1 * g p.2)
    (l : ℕ) :
    (n07aCanonicalUnitMode hm (χ.mul u) l : ℝ → ℝ) =ᵐ[
        volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => f (n07aIntervalUnitMap (K.left m) (K.right m) x) *
        (Real.pi⁻¹ * ∫ θ, χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) *
          g θ * referenceAngularBasis l θ ∂angleMeasure) := by
  have h := n07aCanonicalProduct_coefficient_ae χ hu l
  have hs := Measure.ae_smul_measure h (ENNReal.ofReal (K.right m - K.left m)⁻¹)
  exact (n07aCanonicalUnitMode_ae hm (χ.mul u) l).trans
    ((n07aIntervalUnitMap_preserving hm).quasiMeasurePreserving.ae hs)

theorem n07aCanonicalProduct_cosine_unitMode (hm : K.left m < K.right m)
    (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (j l : ℕ)
    (hb : n07aAngularBand m hm j u = u) :
    (n07aCanonicalUnitMode hm (χ.mul u) l : ℝ → ℝ) =ᵐ[
        volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => n07aCanonicalUnitMode hm u j x *
        n07aCosineMatrixEntry
          (fun θ => χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j := by
  have he := n07aAngularBand_cosine_ae hm u hu j
  rw [hb] at he
  have hprod := n07aCanonicalProduct_unitMode_ae hm χ he l
  filter_upwards [hprod, n07aCanonicalUnitMode_ae hm u j] with x hx huj
  rw [hx, huj]
  rfl

theorem n07aCanonicalProduct_sine_unitMode (hm : K.left m < K.right m)
    (χ : N07aCanonicalOpenCoefficient S K m) (u d : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (j l : ℕ)
    (hb : n07aAngularBand m hm j u = u)
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 0 1) :
    (n07aCanonicalUnitMode hm (χ.mul d) l : ℝ → ℝ) =ᵐ[
        volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => -(2 * (j : ℝ)) * n07aCanonicalUnitMode hm u j x *
        n07aSineMatrixEntry
          (fun θ => χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j := by
  have he := n07a_firstAngular_singleBand_ae hm hu j hb hd
  have hprod := n07aCanonicalProduct_unitMode_ae hm χ
    (f := fun r => -(2 * (j : ℝ)) * n07aHalfRadialCoefficient u j r)
    (g := n07aSineBasis j) he l
  filter_upwards [hprod, n07aCanonicalUnitMode_ae hm u j] with x hx huj
  rw [hx, huj]
  rfl

end ContinuousFlexibility.Analysis
