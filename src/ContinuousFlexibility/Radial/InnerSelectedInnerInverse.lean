import ContinuousFlexibility.Radial.InnerSelectedInverseEstimates
import ContinuousFlexibility.Radial.InnerSelectedInverseStatement
import ContinuousFlexibility.Radial.InnerSelectedFrequencyBands

/-!
# The inner inverse for all bands of one physical realization

One actual inverse is fixed before the weight exponent. Every assertion
uses its original Dirichlet sum, Poisson map, full reference, and flux
matrix. The band depth may be zero, and the unique selected band
covers every positive even frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)
  {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)

/-- The full inner inverse lemma for the same selected physical
families. The ordered construction below supplies these families
from the proved original R09 theorem. -/
theorem innerInverseStatement
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (hCC : 0 ≤ CC) (hCM : 0 < CM) (hη : 0 ≤ η) (hηsmall : η < 1 / 4) :
    InnerSelectedInverseStatement P hCentralFamily hMorseFamily hX hsupport
      (P.inverseEstimateConstant CC CM) := by
  intro K q hq hband
  let A := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
  have hS : IsUnit A.fluxMatrix :=
    P.actualChain_flux_isUnit hCentralFamily hMorseFamily hX hsupport K q hq hband hη hηsmall
  let G := P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS
  refine ⟨G, hS, A.referenceMatrix_eq,
    P.actualChain_reference_posDef hCentralFamily hMorseFamily hX hsupport K q hq hband,
    P.actualChain_diagonal_le_reference hCentralFamily hMorseFamily hX hsupport K q hq hband,
    P.actualChain_reference_blocks hCentralFamily hMorseFamily hX hsupport K q hq hband,
    (fun g => innerModelChainGapOfCut_card_le_two g),
    P.inverse_eq_schur hCentralFamily hMorseFamily hX hsupport K q hq hband hS,
    P.inverse_graph_iff hCentralFamily hMorseFamily hX hsupport K q hq hband hS,
    P.inverse_selfAdjoint hCentralFamily hMorseFamily hX hsupport K q hq hband hS, ?_⟩
  intro γ hγ
  refine ⟨P.actualChain_reference_commute hCentralFamily hMorseFamily hX hsupport K q hq hband γ,
    ?_, ?_⟩
  · intro sign
    refine ⟨P.actualChain_normalized_error hCentralFamily hMorseFamily hX hsupport K q hq hband
      hη hηsmall hγ sign, ?_, ?_⟩
    · apply (P.actualChain_poisson_bound hCentralFamily hMorseFamily hX hsupport K q hq hband
        ha hN hNa hCM hγ sign).trans
      exact div_le_div_of_nonneg_right
        (P.poissonConstant_le_inverseEstimateConstant CC CM) (by positivity)
    · exact (P.inverse_coarse_bound hCentralFamily hMorseFamily hX hsupport K q hq hband hS
        ha hN hNa hCC hCM hη hηsmall hγ sign).trans
        (P.coarse_power_le_inverseEstimateConstant CC CM K)
  · exact (P.inverse_localized_bound hCentralFamily hMorseFamily hX hsupport K q hq hband hS
      ha hN hNa hCC hCM hη hηsmall hγ).trans
      (P.inverseLocalizedConstant_le_inverseEstimateConstant CC CM)

/-- A single positive constant works for every finite band, every
positive even mode in that band, and every permitted weight. -/
theorem exists_innerInverseStatement
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (hCC : 0 ≤ CC) (hCM : 0 < CM) (hη : 0 ≤ η) (hηsmall : η < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ InnerSelectedInverseStatement P
      hCentralFamily hMorseFamily hX hsupport C :=
  ⟨P.inverseEstimateConstant CC CM, P.inverseEstimateConstant_pos CC CM,
    P.innerInverseStatement hCentralFamily hMorseFamily hX hsupport
      ha hN hNa hCC hCM hη hηsmall⟩

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
