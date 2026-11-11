import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction
import ContinuousFlexibility.Blueprint.Statements

/-!
# The actual canonical operator from the chart data

The coefficient fields are the actual principal density composed with the
inverse chart. The potential is the actual height-generated potential,
with the elliptic or hyperbolic sign from the frozen canonical operator.
The proof uses the local inverse identities and regularity already in
N04PartA; no transformed operator identity is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The full frozen operator is expressed in the explicitly transported
coefficient and potential fields. Only physical coefficient regularity is
additional to the chart data. -/
theorem n04b_canonicalOperator_explicit_fields
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (ha : ContDiffAt ℝ ∞ (L.coefficients z).a (K.inverseChart z m p))
    (hb : ContDiffAt ℝ ∞ (L.coefficients z).b (K.inverseChart z m p))
    (hc : ContDiffAt ℝ ∞ (L.coefficients z).c (K.inverseChart z m p))
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W) :
    canonicalOperator S K L z m W p =
      (if K.positive m then -1 else (1 : ℝ)) *
        divergenceOperator
          (inverseChartPrincipalCoefficients (L.coefficients z)
            (K.chart z m) (K.inverseChart z m) (K.height z m)) W p +
      ((if K.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (K.chart z m) (K.inverseChart z m) (K.height z m) p) * W p := by
  let x : PolarPoint := K.inverseChart z m p
  have hcharts := hA.charts z hz hs m
  have hx : x ∈ physicalPieceOpen S K z m := hcharts.2.1 hp
  have hFx : K.chart z m x = p := hcharts.2.2.2.1 p hp
  have hOpen : IsOpen (physicalPieceOpen S K z m) := (hA.domains z hz hs m).1
  have hCanonicalOpen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hF : ContDiffAt ℝ ∞ (K.chart z m) x :=
    (hcharts.2.2.2.2.1 x hx).contDiffAt (hOpen.mem_nhds hx)
  have hG : ContDiffAt ℝ ∞ (K.inverseChart z m) (K.chart z m x) := by
    have hi : ContDiffAt ℝ ∞ (K.inverseChart z m) p :=
      (hcharts.2.2.2.2.2.1 p hp).contDiffAt (hCanonicalOpen.mem_nhds hp)
    simpa only [hFx] using hi
  have hh : ContDiffAt ℝ ∞ (K.height z m) x :=
    (hcharts.2.2.2.2.2.2.1 x hx).contDiffAt (hOpen.mem_nhds hx)
  have hJ : planeJacobian (K.chart z m) x ≠ 0 :=
    (hcharts.2.2.2.2.2.2.2 x hx).2.1
  have hInverse : ∀ᶠ y in 𝓝 x, K.inverseChart z m (K.chart z m y) = y := by
    filter_upwards [hOpen.mem_nhds hx] with y hy
    exact hcharts.2.2.1 y hy
  have hop := coordinateOperator_explicit_fields ha hb hc hF hG hh hW hJ hInverse
  rw [hFx] at hop
  change (if K.positive m then -1 else (1 : ℝ)) *
      (K.height z m x *
        divergenceOperator (L.coefficients z)
          (fun y => K.height z m y * W (K.chart z m y)) x /
        |planeJacobian (K.chart z m) x|) = _
  rw [hop]
  ring

/-- Replace only the coefficient and potential fields by their actual
coordinate formulas. The pieces, charts, heights and cut data are retained. -/
def n04bCanonicalOperatorData (S : PhysicalSpacesData)
    (L : ReturnCorrectionData S) (K : CanonicalData S) : CanonicalData S :=
  { K with
    coefficients := fun z m =>
      inverseChartPrincipalCoefficients (L.coefficients z)
        (K.chart z m) (K.inverseChart z m) (K.height z m)
    potential := fun z m p =>
      (if K.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (K.chart z m) (K.inverseChart z m) (K.height z m) p }

@[simp]
theorem n04bCanonicalOperatorData_canonicalHeight
    (S : PhysicalSpacesData) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalHeight S (n04bCanonicalOperatorData S L K) z m u p =
      canonicalHeight S K z m u p := rfl

@[simp]
theorem n04bCanonicalOperatorData_canonicalOperator
    (S : PhysicalSpacesData) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (W : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalOperator S (n04bCanonicalOperatorData S L K) L z m W p =
      canonicalOperator S K L z m W p := rfl

theorem n04bCanonicalOperatorData_partA
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (L : ReturnCorrectionData S) {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) :
    N04PartA D S C (n04bCanonicalOperatorData S L K) base ε := by
  exact hA

/-- Both signs in the frozen operator clause follow from the same actual
coordinate identity. -/
theorem n04bCanonicalOperatorData_operator
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (ha : ContDiffAt ℝ ∞ (L.coefficients z).a (K.inverseChart z m p))
    (hb : ContDiffAt ℝ ∞ (L.coefficients z).b (K.inverseChart z m p))
    (hc : ContDiffAt ℝ ∞ (L.coefficients z).c (K.inverseChart z m p))
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W) :
    canonicalOperator S (n04bCanonicalOperatorData S L K) L z m W p =
      (if (n04bCanonicalOperatorData S L K).positive m then -1 else (1 : ℝ)) *
        divergenceOperator ((n04bCanonicalOperatorData S L K).coefficients z m) W p +
      (n04bCanonicalOperatorData S L K).potential z m p * W p := by
  exact n04b_canonicalOperator_explicit_fields hA hz hs m hp ha hb hc W hW

/-- The quantified operator conjunct, with physical coefficient regularity
on the actual pieces and all geometric assumptions supplied by N04PartA. -/
theorem n04bCanonicalOperatorData_operator_clause
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    (hreg : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K z m →
        ContDiffAt ℝ ∞ (L.coefficients z).a x ∧
        ContDiffAt ℝ ∞ (L.coefficients z).b x ∧
        ContDiffAt ℝ ∞ (L.coefficients z).c x) :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m W, ContDiff ℝ ∞ W →
      ∀ p ∈ canonicalOpen S (n04bCanonicalOperatorData S L K) m,
        canonicalOperator S (n04bCanonicalOperatorData S L K) L z m W p =
          (if (n04bCanonicalOperatorData S L K).positive m then -1 else (1 : ℝ)) *
            divergenceOperator ((n04bCanonicalOperatorData S L K).coefficients z m) W p +
          (n04bCanonicalOperatorData S L K).potential z m p * W p := by
  intro z hz hs m W hW p hp
  have hp' : p ∈ canonicalOpen S K m := hp
  have hcharts := hA.charts z hz hs m
  have hx : K.inverseChart z m p ∈ physicalPieceOpen S K z m := hcharts.2.1 hp'
  obtain ⟨ha, hb, hc⟩ := hreg z hz hs m (K.inverseChart z m p) hx
  exact n04bCanonicalOperatorData_operator hA hz hs m hp' ha hb hc W hW

end ContinuousFlexibility.Analysis
