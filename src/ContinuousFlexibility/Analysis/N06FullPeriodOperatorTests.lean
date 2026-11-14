module

public import ContinuousFlexibility.Analysis.N06PositiveFullPeriodTests
public import ContinuousFlexibility.Analysis.N06NegativeFullPeriodGreen

/-!
# The actual full-period operator test on every current piece

The positive-piece proof uses the original coefficient germs. The negative
proof uses the actual canonical normal form and the potential periodicity
forced by N03. Together they identify exactly the source appearing in full
physical weak pairings, on every selected canonical piece.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- No periodicity of the bare corrected coefficients is an input. The
physical test is allowed to have precisely the original full period. -/
theorem n06_current_source_average
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p =
      canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p := by
  cases hm : K.positive m
  · exact n06_negative_current_source_average hT hS h.1.2 h.2.2.2.2.1 hz hs hm hφ hp
  · exact n06_positive_current_source_average hT hS h.1.1.1 h.1.2 h.2.2.2.2.1
      hz hs m hm hφ.1 hp

/-- The identity applies directly to the actual canonical bulk integral,
so finite interface cancellation may precede the L2 limit. -/
theorem n06_current_source_average_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) (u : PolarPoint → ℝ) :
    (∫ p, u p * canonicalSource S K z m
      (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
        ∂canonicalMeasure S K m) =
      ∫ p, u p * canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p
          ∂canonicalMeasure S K m := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  rw [n06_current_source_average hT hS h hz hs m hφ ⟨hp.1, mem_univ _⟩]

end ContinuousFlexibility.Statements
