import ContinuousFlexibility.Analysis.N07aCanonicalModeProducts
import ContinuousFlexibility.Analysis.N07aCanonicalModeBessel

/-!
# Linearity of the actual radial and unit modes

The maps below keep the already fixed coefficient representatives.
Fubini gives the integrability needed to pass addition through the circle
integral; affine normalization preserves these exact linear operations.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_referenceAngularBasis_memLp_half (n : ℕ) :
    MemLp (referenceAngularBasis n) 2 angleMeasure :=
  MemLp.of_bound (contDiff_referenceAngularBasis n).continuous.aestronglyMeasurable 2
    (Eventually.of_forall fun θ => by
      simpa only [Real.norm_eq_abs] using n07a_referenceAngularBasis_abs_le n θ)

theorem n07aCanonicalRadialMode_add (u v : CanonicalL2 S K m) (n : ℕ) :
    n07aCanonicalRadialMode (u + v) n =
      n07aCanonicalRadialMode u n + n07aCanonicalRadialMode v n := by
  let μ := volume.restrict (Ioo (K.left m) (K.right m))
  have hu : MemLp (u : PolarPoint → ℝ) 2 (μ.prod angleMeasure) := by
    simpa only [μ, n07aCanonicalMeasure_eq_prod] using Lp.memLp u
  have hv : MemLp (v : PolarPoint → ℝ) 2 (μ.prod angleMeasure) := by
    simpa only [μ, n07aCanonicalMeasure_eq_prod] using Lp.memLp v
  have he : ((u + v : CanonicalL2 S K m) : PolarPoint → ℝ) =ᵐ[μ.prod angleMeasure]
      fun p => u p + v p := by
    have h : ((u + v : CanonicalL2 S K m) : PolarPoint → ℝ) =ᵐ[μ.prod angleMeasure]
        ((u : PolarPoint → ℝ) + (v : PolarPoint → ℝ)) := by
      simpa only [μ, n07aCanonicalMeasure_eq_prod] using Lp.coeFn_add u v
    exact h.mono fun p hp => by simpa only [Pi.add_apply] using hp
  apply Lp.ext
  filter_upwards [n07aCanonicalRadialMode_ae (u + v) n,
    n07aCanonicalRadialMode_ae u n, n07aCanonicalRadialMode_ae v n,
    Lp.coeFn_add (n07aCanonicalRadialMode u n) (n07aCanonicalRadialMode v n),
    n07aHalfRadialCoefficient_congr_ae he n,
    memLp_two_prod_sections hu, memLp_two_prod_sections hv] with r hsum hur hvr hadd heq hui hvi
  rw [hsum, hadd, Pi.add_apply, hur, hvr, heq]
  have hiu := hui.integrable_mul (n07a_referenceAngularBasis_memLp_half n)
  have hiv := hvi.integrable_mul (n07a_referenceAngularBasis_memLp_half n)
  change Integrable (fun θ => u (r, θ) * referenceAngularBasis n θ) angleMeasure at hiu
  change Integrable (fun θ => v (r, θ) * referenceAngularBasis n θ) angleMeasure at hiv
  unfold n07aHalfRadialCoefficient
  simp only [add_mul]
  change Real.pi⁻¹ * (∫ θ, u (r, θ) * referenceAngularBasis n θ +
      v (r, θ) * referenceAngularBasis n θ ∂angleMeasure) = _
  rw [integral_add hiu hiv]
  unfold angleMeasure
  ring

theorem n07aCanonicalRadialMode_smul (c : ℝ) (u : CanonicalL2 S K m) (n : ℕ) :
    n07aCanonicalRadialMode (c • u) n = c • n07aCanonicalRadialMode u n := by
  have he : ((c • u : CanonicalL2 S K m) : PolarPoint → ℝ) =ᵐ[
      (volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure]
      fun p => c * u p := by
    have h : ((c • u : CanonicalL2 S K m) : PolarPoint → ℝ) =ᵐ[
        (volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure]
        c • (u : PolarPoint → ℝ) := by
      simpa only [n07aCanonicalMeasure_eq_prod] using Lp.coeFn_smul c u
    exact h.mono fun p hp => by simpa only [Pi.smul_apply, smul_eq_mul] using hp
  apply Lp.ext
  filter_upwards [n07aCanonicalRadialMode_ae (c • u) n,
    n07aCanonicalRadialMode_ae u n, Lp.coeFn_smul c (n07aCanonicalRadialMode u n),
    n07aHalfRadialCoefficient_congr_ae he n] with r hcu hu hsmul heq
  rw [hcu, hsmul, Pi.smul_apply, smul_eq_mul, hu, heq]
  exact n07aHalfRadialCoefficient_mul_radial (fun _ => c) u n r

def n07aCanonicalRadialModeLinear (n : ℕ) :
    CanonicalL2 S K m →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ioo (K.left m) (K.right m))) where
  toFun u := n07aCanonicalRadialMode u n
  map_add' u v := n07aCanonicalRadialMode_add u v n
  map_smul' c u := by simpa only [RingHom.id_apply] using n07aCanonicalRadialMode_smul c u n

theorem n07aCanonicalRadialModeLinear_apply (n : ℕ) (u : CanonicalL2 S K m) :
    n07aCanonicalRadialModeLinear n u = n07aCanonicalRadialMode u n := rfl

theorem n07aIntervalUnitPullback_add {a b : ℝ} (hab : a < b)
    (u v : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    n07aIntervalUnitPullback hab (u + v) =
      n07aIntervalUnitPullback hab u + n07aIntervalUnitPullback hab v := by
  unfold n07aIntervalUnitPullback
  rw [map_add, map_add]

theorem n07aIntervalUnitPullback_smul {a b : ℝ} (hab : a < b)
    (c : ℝ) (u : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    n07aIntervalUnitPullback hab (c • u) = c • n07aIntervalUnitPullback hab u := by
  unfold n07aIntervalUnitPullback
  rw [map_smul]
  exact (Lp.compMeasurePreservingₗ ℝ (n07aIntervalUnitMap a b)
    (n07aIntervalUnitMap_preserving hab)).map_smul c _

def n07aCanonicalUnitModeLinear (hm : K.left m < K.right m) (n : ℕ) :
    CanonicalL2 S K m →ₗ[ℝ] N07aIntervalL2 where
  toFun u := n07aCanonicalUnitMode hm u n
  map_add' u v := by
    rw [n07aCanonicalUnitMode, n07aCanonicalRadialMode_add, n07aIntervalUnitPullback_add]
    rfl
  map_smul' c u := by
    simp only [n07aCanonicalUnitMode, n07aCanonicalRadialMode_smul,
      n07aIntervalUnitPullback_smul, RingHom.id_apply]

theorem n07aCanonicalUnitModeLinear_apply (hm : K.left m < K.right m)
    (n : ℕ) (u : CanonicalL2 S K m) :
    n07aCanonicalUnitModeLinear hm n u = n07aCanonicalUnitMode hm u n := rfl

theorem n07aCanonicalUnitMode_add (hm : K.left m < K.right m)
    (u v : CanonicalL2 S K m) (n : ℕ) :
    n07aCanonicalUnitMode hm (u + v) n =
      n07aCanonicalUnitMode hm u n + n07aCanonicalUnitMode hm v n :=
  (n07aCanonicalUnitModeLinear hm n).map_add u v

theorem n07aCanonicalUnitMode_smul (hm : K.left m < K.right m)
    (c : ℝ) (u : CanonicalL2 S K m) (n : ℕ) :
    n07aCanonicalUnitMode hm (c • u) n = c • n07aCanonicalUnitMode hm u n :=
  (n07aCanonicalUnitModeLinear hm n).map_smul c u

end ContinuousFlexibility.Analysis
