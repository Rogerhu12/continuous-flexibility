import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasOperator
import ContinuousFlexibility.Analysis.N04RealizationPotentialIdentity

/-!
# The actual atlas geometry available to the principal subnode

Admissibility retains the matching of the positive transport family.  The
already proved gauge construction therefore supplies the qualitative chart
and operator clauses for this same atlas, before any quantitative principal
estimate is used.  Auxiliary-column replacement preserves every field that
occurs here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The admissible reference-gauged atlas has the original qualitative
geometry and operator action, with the supplied auxiliary column. -/
theorem n04PrincipalPositive_admissible_parts {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    N04PartA G.W.D (G.S η) (G.C η) (G.V η) b ε ∧
      N04PartB (G.S η) (G.C η) (G.L η) (G.V η) b ε ∧
      ReferenceRadial (G.S η) (G.C η) (G.V η) := by
  have hm := h.2.2.2.2.2
  let B := hm.choose
  let lower := hm.choose_spec.choose
  let upper := hm.choose_spec.choose_spec.choose
  have hN : G.N = B.region := hm.choose_spec.choose_spec.choose_spec.1
  have hmatching := hm.choose_spec.choose_spec.choose_spec.2
  have hg := n04Realization_gaugeAtlas_of_family G.W.hT G.W.hS G.W.through03
    G.W.field G.X.e₀ G.e G.X.cell G.X.src B G.Y G.H h.2.2.2.1
    G.τ G.σ G.Q lower upper h.1 h.2.1 h.2.2.1 hmatching h.2.2.2.2.1
  have hA : CanonicalGeometry G.W.D G.W.S G.W.C
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) b ε := by
    rw [hN]
    exact hg.1
  have hB : CanonicalCutOperatorProperties G.W.S G.W.C G.W.L
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) b ε := by
    rw [hN]
    exact hg.2.1
  have hR : ReferenceRadial G.W.S G.W.C
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) := by
    rw [hN]
    exact hg.2.2.2.1
  exact ⟨canonicalGeometry_replaceAuxiliaryColumn hA η,
    cutOperator_replaceAuxiliaryColumn η hB,
    referenceRadial_replaceAuxiliaryColumn η hR⟩

/-- The stored coefficient and potential fields are the explicit coordinate
formulas at their own inverse point, for every piece and every state. -/
theorem n04PrincipalPositive_operatorFields
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (z : AnnularState (G.S η) × ℝ) (m : ℕ) :
    (G.V η).coefficients z m =
        inverseChartPrincipalCoefficients ((G.L η).coefficients z)
          ((G.V η).chart z m) ((G.V η).inverseChart z m) ((G.V η).height z m) ∧
      ∀ p, (G.V η).potential z m p =
        (if (G.V η).positive m then -1 else (1 : ℝ)) *
          inverseChartPotential ((G.L η).coefficients z)
            ((G.V η).chart z m) ((G.V η).inverseChart z m) ((G.V η).height z m) p :=
  n04WholeReferenceGaugeAtlasData_actual_operatorFields
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N z m

/-- The potential can be recovered from the same principal field and the
reciprocal pulled height.  This identity has no quantitative premise. -/
theorem n04PrincipalPositive_potential_identity {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood (G.S η) (G.C η) b ε)
    (hs : stateSector (G.S η) z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen (G.S η) (G.V η) m) :
    (G.V η).potential z m p =
      -(if (G.V η).positive m then -1 else (1 : ℝ)) *
        (G.V η).height z m ((G.V η).inverseChart z m p) *
        divergenceOperator ((G.V η).coefficients z m)
          (fun q => ((G.V η).height z m ((G.V η).inverseChart z m q))⁻¹) p :=
  n04Realization_canonicalPotential_eq_reciprocalHeight_divergence
    (G.n04PrincipalPositive_admissible_parts h η).1
    (G.n04PrincipalPositive_admissible_parts h η).2.1 hz hs m hp

end N04RealizationGauge

end ContinuousFlexibility.Analysis
