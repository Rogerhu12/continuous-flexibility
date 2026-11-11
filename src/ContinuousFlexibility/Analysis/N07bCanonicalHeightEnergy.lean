import ContinuousFlexibility.Analysis.N07bCanonicalSourceEnergy

/-!
# The physical energy of the canonical unknown

The unknown and source conversions have reciprocal physical square densities.
This identifies the actual zeroth-order energy needed for membership in the
fixed reference domain. As with the source formula, integrability is asserted
only in the norm corollary, where it is an explicit hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hK hz hsector

/-- Multiplying by the reciprocal source density converts the source
formula into the actual canonical unknown. -/
theorem n07b_canonicalSource_inverseDensity_mul (m : ℕ) (u : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m
      (fun x => |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 * u x) p =
        canonicalHeight S K z m u p := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hx := hcharts.2.1 hp
  have hregular := hcharts.2.2.2.2.2.2.2 (K.inverseChart z m p) hx
  have hh := hregular.1.ne'
  have hJ := abs_ne_zero.mpr hregular.2.1
  dsimp only [canonicalSource, canonicalHeight]
  field_simp [hh, hJ] <;> ring

/-- Exact square-energy conversion for the actual canonical height. -/
theorem n07b_canonicalHeight_square_integral (m : ℕ) (u : PolarPoint → ℝ) :
    (∫ p, canonicalHeight S K z m u p ^ 2 ∂canonicalMeasure S K m) =
      ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p ^ 2 := by
  have hpair := canonicalSource_pairing_of_partA hK hz hsector m u
    (fun p => |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p)
  have hcanonical :
      (∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        canonicalHeight S K z m u p * canonicalSource S K z m
          (fun x => |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 * u x) p) =
      ∫ p, canonicalHeight S K z m u p ^ 2 ∂canonicalMeasure S K m := by
    simp only [canonicalOpen, canonicalMeasure, prod_inter_prod, inter_univ, univ_inter]
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioc)
    intro p hp
    change canonicalHeight S K z m u p * canonicalSource S K z m
      (fun x => |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 * u x) p =
        canonicalHeight S K z m u p ^ 2
    rw [n07b_canonicalSource_inverseDensity_mul hK hz hsector m u
      (show p ∈ canonicalOpen S K m from ⟨hp.1, mem_univ _⟩), pow_two]
  calc
    _ = _ := hcanonical.symm
    _ = _ := hpair.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => by ring)

/-- For a genuine L² unknown, the same integral is its Hilbert norm squared. -/
theorem n07b_canonicalHeight_toLp_norm_sq (m : ℕ) (u : PolarPoint → ℝ)
    (hu : MemLp (canonicalHeight S K z m u) 2 (canonicalMeasure S K m)) :
    ‖hu.toLp (canonicalHeight S K z m u)‖ ^ 2 =
      ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p ^ 2 := by
  rw [spaces_lp_norm_sq_toLp hu, n07b_canonicalHeight_square_integral hK hz hsector m u]

end ContinuousFlexibility.Analysis
