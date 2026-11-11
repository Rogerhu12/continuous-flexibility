import ContinuousFlexibility.Analysis.AdjugateInversePrincipalField

/-!
# A genuine closed-endpoint effective field on a negative piece

This field uses only the forward chart and height. PartA therefore gives
its actual pointwise infinite smoothness on the closed physical piece,
and the determinant identity holds there. In the interior it agrees with
the previously reconstructed reverse field and has the stored physical
operator's action. No boundary value of the total inverse is involved.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def negativeCanonicalClosedCoefficients
    (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : SymmetricCoefficients :=
  adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients
    (K.chart z m) (K.height z m)

/-- Actual smoothness at both physical endpoints comes from the forward
closed-piece assumptions, independently of the prescribed inverse. -/
theorem negativeCanonicalClosedCoefficients_contDiffAt
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    ContDiffAt ℝ ∞ (negativeCanonicalClosedCoefficients S K z m).a p ∧
      ContDiffAt ℝ ∞ (negativeCanonicalClosedCoefficients S K z m).b p ∧
      ContDiffAt ℝ ∞ (negativeCanonicalClosedCoefficients S K z m).c p := by
  have hs := hA.2.2.2.2.2.2.2.2.1 z hz hsector m p hp
  exact contDiffAt_adjugateCoordinatePrincipalCoefficients
    (A := canonicalAiryPrincipalCoefficients) (F := K.chart z m) (h := K.height z m)
    contDiffAt_const contDiffAt_const contDiff_fst.neg.contDiffAt
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.ne'

/-- The determinant formula holds at the actual closed endpoints. -/
theorem negativeCanonicalClosedCoefficients_determinant
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    (negativeCanonicalClosedCoefficients S K z m).a p *
          (negativeCanonicalClosedCoefficients S K z m).c p -
        (negativeCanonicalClosedCoefficients S K z m).b p ^ 2 =
      -(K.chart z m p).1 / K.height z m p ^ 4 := by
  have hs := hA.2.2.2.2.2.2.2.2.1 z hz hsector m p hp
  simpa only [negativeCanonicalClosedCoefficients, canonicalAiryPrincipalCoefficients,
    one_mul, zero_pow two_ne_zero, sub_zero] using
      adjugateCoordinatePrincipalCoefficients_determinant
        canonicalAiryPrincipalCoefficients (K.chart z m) (K.height z m) p
        hs.2.2.1 hs.2.2.2.ne'

/-- A zero determinant of the actual closed effective field forces the
canonical root boundary. No chosen inverse value appears in this test. -/
theorem negativeCanonicalClosedCoefficients_det_eq_zero_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    ((negativeCanonicalClosedCoefficients S K z m).a p *
          (negativeCanonicalClosedCoefficients S K z m).c p -
        (negativeCanonicalClosedCoefficients S K z m).b p ^ 2 = 0) ↔
      (K.chart z m p).1 = 0 := by
  have hs := hA.2.2.2.2.2.2.2.2.1 z hz hsector m p hp
  rw [negativeCanonicalClosedCoefficients_determinant hA hz hsector m hp]
  constructor
  · intro he
    have hn := (div_eq_iff (pow_ne_zero 4 hs.2.2.2.ne')).mp he
    simpa only [zero_mul, neg_eq_zero] using hn
  · intro he
    simp only [he, neg_zero, zero_div]

/-- On the open physical piece the actual inverse derivative identifies
the forward-only field with the reverse field. -/
theorem negativeCanonicalEffectiveCoefficients_eq_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    (negativeCanonicalEffectiveCoefficients S K z m).a p =
        (negativeCanonicalClosedCoefficients S K z m).a p ∧
      (negativeCanonicalEffectiveCoefficients S K z m).b p =
        (negativeCanonicalClosedCoefficients S K z m).b p ∧
      (negativeCanonicalEffectiveCoefficients S K z m).c p =
        (negativeCanonicalClosedCoefficients S K z m).c p := by
  have hU : IsOpen (physicalPieceOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  rcases hA.2.2.2.2.2.2.2.1 z hz hsector m with
    ⟨hFV, hGU, hGF, hFG, hF, hG, hh, hpoint⟩
  have hFp : K.chart z m p ∈ canonicalOpen S K m := hFV hp
  have hinverse : K.inverseChart z m ∘ K.chart z m =ᶠ[𝓝 p]
      (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hGF q hq
  exact reverseCoordinatePrincipalCoefficients_eq_adjugate
    canonicalAiryPrincipalCoefficients
    (((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (((hG (K.chart z m p) hFp).contDiffAt (hV.mem_nhds hFp)).differentiableAt
      (by simp)) hinverse (hpoint p hp).1.ne'

/-- The closed effective field has the original stored operator's actual
action on every locally smooth test in the negative open half. -/
theorem negativeCanonicalClosedOperator_of_parts
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    (u : PolarPoint → ℝ) (hu : ContDiffOn ℝ ∞ u (physicalPieceOpen S K m))
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    divergenceOperator (L.coefficients z) u p =
      divergenceOperator (negativeCanonicalClosedCoefficients S K z m) u p := by
  have hU : IsOpen (physicalPieceOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have he : ∀ᶠ q in 𝓝 p,
      (negativeCanonicalEffectiveCoefficients S K z m).a q =
          (negativeCanonicalClosedCoefficients S K z m).a q ∧
        (negativeCanonicalEffectiveCoefficients S K z m).b q =
          (negativeCanonicalClosedCoefficients S K z m).b q ∧
        (negativeCanonicalEffectiveCoefficients S K z m).c q =
          (negativeCanonicalClosedCoefficients S K z m).c q := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact negativeCanonicalEffectiveCoefficients_eq_closed hA hz hsector m hq
  exact ((negativeCanonicalEffectiveOperator_of_parts hA hB hz hsector m hm).2.2.2
    u hu p hp).trans (divergenceOperator_eq_of_coefficient_germs u
      (he.mono fun _ h => h.1) (he.mono fun _ h => h.2.1)
      (he.mono fun _ h => h.2.2))

end ContinuousFlexibility.Analysis
