import ContinuousFlexibility.Analysis.N07aCanonicalCutoffColumn

/-!
# Pairing the actual canonical representatives

The physical unknown contains the left cutoff scalar in addition to its
canonical L² remainder. These identities retain that scalar exactly.
All pairings use actual compact tests, so the cutoff height only needs
interior smoothness. The source representative is the frozen L² class.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

namespace N07aCanonicalOpenCoefficient

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem memLp (χ : N07aCanonicalOpenCoefficient S K m) :
    MemLp χ.value 2 (canonicalMeasure S K m) := by
  let := n07a_canonicalMeasure_finite S K m
  apply MemLp.of_bound (n07a_canonicalOpen_aestronglyMeasurable χ.smooth.continuousOn) χ.bound
  simpa only [Real.norm_eq_abs] using χ.bound_ae

def toLp (χ : N07aCanonicalOpenCoefficient S K m) : CanonicalL2 S K m :=
  χ.memLp.toLp χ.value

theorem toLp_ae (χ : N07aCanonicalOpenCoefficient S K m) :
    (χ.toLp : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] χ.value :=
  χ.memLp.coeFn_toLp

end N07aCanonicalOpenCoefficient

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}

theorem n07a_canonicalRepresentation_height
    (hrep : HasCanonicalRepresentation D S C K z U F η f) (m : ℕ) :
    canonicalHeight S K z m η =ᵐ[canonicalMeasure S K m]
      fun p => U.1 m p + U.2.1 * n07aCanonicalCutoffHeight S K z m p := by
  filter_upwards [hrep.1 m] with p hp
  simp only [canonicalHeight, n07aCanonicalCutoffHeight] at hp ⊢
  rw [hp]
  ring

theorem n07a_canonicalRepresentation_height_integrable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft)
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    {m : ℕ} {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    Integrable (fun p => canonicalHeight S K z m η p * W p) (canonicalMeasure S K m) := by
  have hiU : Integrable (fun p => U.1 m p * W p) (canonicalMeasure S K m) :=
    (Lp.memLp (U.1 m)).integrable_mul (n07a_canonicalTest_memLp hW)
  have hiχ := n07a_canonicalOpen_integrable_mul_test
    (n07aCanonicalCutoffHeight_smooth h04 hz hs hχ)
    (n07aCanonicalCutoffHeight_periodic h04 hz hs) hW
  apply (integrable_congr (show (fun p => canonicalHeight S K z m η p * W p) =ᵐ[
    canonicalMeasure S K m] fun p => U.1 m p * W p +
      U.2.1 * (n07aCanonicalCutoffHeight S K z m p * W p) from ?_)).mpr
    (hiU.add (hiχ.const_mul U.2.1))
  filter_upwards [n07a_canonicalRepresentation_height hrep m] with p hp
  rw [hp]
  ring

theorem n07a_canonicalRepresentation_height_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft)
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    {m : ℕ} {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    (∫ p, canonicalHeight S K z m η p * W p ∂canonicalMeasure S K m) =
      (∫ p, U.1 m p * W p ∂canonicalMeasure S K m) +
        U.2.1 * ∫ p, n07aCanonicalCutoffHeight S K z m p * W p
          ∂canonicalMeasure S K m := by
  have hiU : Integrable (fun p => U.1 m p * W p) (canonicalMeasure S K m) :=
    (Lp.memLp (U.1 m)).integrable_mul (n07a_canonicalTest_memLp hW)
  have hiχ := n07a_canonicalOpen_integrable_mul_test
    (n07aCanonicalCutoffHeight_smooth h04 hz hs hχ)
    (n07aCanonicalCutoffHeight_periodic h04 hz hs) hW
  have he : (fun p => canonicalHeight S K z m η p * W p) =ᵐ[canonicalMeasure S K m]
      fun p => U.1 m p * W p + U.2.1 * (n07aCanonicalCutoffHeight S K z m p * W p) := by
    filter_upwards [n07a_canonicalRepresentation_height hrep m] with p hp
    rw [hp]
    ring
  rw [integral_congr_ae he, integral_add hiU (hiχ.const_mul U.2.1), integral_const_mul]

theorem n07a_canonicalRepresentation_source_integrable
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    {m : ℕ} {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    Integrable (fun p => canonicalSource S K z m f p * W p) (canonicalMeasure S K m) :=
  ((Lp.memLp (F m)).integrable_mul (n07a_canonicalTest_memLp hW)).congr
    ((hrep.2 m).mono fun p hp => congrArg (· * W p) hp)

theorem n07a_canonicalRepresentation_source_pairing
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    {m : ℕ} (W : PolarPoint → ℝ) :
    (∫ p, canonicalSource S K z m f p * W p ∂canonicalMeasure S K m) =
      ∫ p, F m p * W p ∂canonicalMeasure S K m :=
  integral_congr_ae ((hrep.2 m).symm.mono fun p hp => congrArg (· * W p) hp)

end ContinuousFlexibility.Analysis
