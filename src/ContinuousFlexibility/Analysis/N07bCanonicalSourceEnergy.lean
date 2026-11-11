import ContinuousFlexibility.Analysis.CanonicalSourceConversion
import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative

/-!
# The actual physical energy of a canonical source

On a canonical piece the source conversion is `h * f / |J|`.
Its square integral is therefore the physical integral of
`(h^2 / |J|) * f^2`. This is a specialization of the already proved
change-of-variables pairing; no coordinate or measure is replaced.

The raw integral identity uses the totalized Bochner integral and makes
no integrability assertion. The final norm identity assumes actual
`MemLp` of the transformed source. Uniform bounds for the physical
density and summability over all pieces are separate analytic obligations.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The physical density whose integral is the canonical source energy. -/
def n07bCanonicalSourceDensity (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  K.height z m p ^ 2 / |planeJacobian (K.chart z m) p|

theorem n07bCanonicalSourceDensity_nonneg (S : PhysicalSpacesData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) :
    0 ≤ n07bCanonicalSourceDensity S K z m p :=
  div_nonneg (sq_nonneg _) (abs_nonneg _)

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

/-- The height conversion of the density-weighted field is exactly the
source conversion, at every point of the actual canonical piece. -/
theorem n07b_canonicalHeight_density_mul (m : ℕ) (f : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m (fun x => n07bCanonicalSourceDensity S K z m x * f x) p =
      canonicalSource S K z m f p := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hx := hcharts.2.1 hp
  have hregular := hcharts.2.2.2.2.2.2.2 (K.inverseChart z m p) hx
  have hh : K.height z m (K.inverseChart z m p) ≠ 0 := hregular.1.ne'
  have hJ : |planeJacobian (K.chart z m) (K.inverseChart z m p)| ≠ 0 :=
    abs_ne_zero.mpr hregular.2.1
  dsimp only [canonicalHeight, canonicalSource, n07bCanonicalSourceDensity]
  field_simp [hh, hJ] <;> ring

/-- The exact raw square-integral formula. It is valid under the same
totalized integral convention as the underlying change of variables. -/
theorem n07b_canonicalSource_square_integral (m : ℕ) (f : PolarPoint → ℝ) :
    (∫ p, canonicalSource S K z m f p ^ 2 ∂canonicalMeasure S K m) =
      ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        n07bCanonicalSourceDensity S K z m p * f p ^ 2 := by
  have hpair := canonicalSource_pairing_of_partA hK hz hsector m
    (fun p => n07bCanonicalSourceDensity S K z m p * f p) f
  have hcanonical :
      (∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        canonicalHeight S K z m
          (fun x => n07bCanonicalSourceDensity S K z m x * f x) p *
            canonicalSource S K z m f p) =
      ∫ p, canonicalSource S K z m f p ^ 2 ∂canonicalMeasure S K m := by
    simp only [canonicalOpen, canonicalMeasure, prod_inter_prod, inter_univ, univ_inter]
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioc)
    intro p hp
    rw [n07b_canonicalHeight_density_mul hK hz hsector m f
      (show p ∈ canonicalOpen S K m from ⟨hp.1, mem_univ _⟩), pow_two]
  calc
    _ = ∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        canonicalHeight S K z m
          (fun x => n07bCanonicalSourceDensity S K z m x * f x) p *
            canonicalSource S K z m f p := hcanonical.symm
    _ = ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        (n07bCanonicalSourceDensity S K z m p * f p) * f p := hpair.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => by ring)

/-- For an actual `L²` source, the same physical integral is its squared
Hilbert norm. The `MemLp` hypothesis is not inferred from the raw identity. -/
theorem n07b_canonicalSource_toLp_norm_sq (m : ℕ) (f : PolarPoint → ℝ)
    (hf : MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m)) :
    ‖hf.toLp (canonicalSource S K z m f)‖ ^ 2 =
      ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        n07bCanonicalSourceDensity S K z m p * f p ^ 2 := by
  rw [spaces_lp_norm_sq_toLp hf, n07b_canonicalSource_square_integral hK hz hsector m f]

end ContinuousFlexibility.Analysis
