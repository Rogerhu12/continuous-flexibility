import ContinuousFlexibility.Analysis.ReverseCoordinateOperator

/-!
# The actual smooth effective operator on a negative canonical piece

The frozen negative normal form supplies a smooth canonical principal
field even though the stored physical coefficients have no regularity
hypothesis. The reverse-coordinate theorem therefore gives an explicit
smooth physical field with the same actual divergence action on every
locally smooth physical test on the actual current domain. Only open-piece
inverse identities are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The divergence action is local in each coefficient as well as in the
test function; no differentiability of either coefficient field is needed. -/
theorem divergenceOperator_eq_of_coefficient_germs
    {A B : SymmetricCoefficients} (u : PolarPoint → ℝ) {x : PolarPoint}
    (ha : A.a =ᶠ[𝓝 x] B.a) (hb : A.b =ᶠ[𝓝 x] B.b)
    (hc : A.c =ᶠ[𝓝 x] B.c) :
    divergenceOperator A u x = divergenceOperator B u x := by
  have hr :
      (fun y => A.a y * radialPartial u y + A.b y * angularPartial u y) =ᶠ[𝓝 x]
        (fun y => B.a y * radialPartial u y + B.b y * angularPartial u y) := by
    filter_upwards [ha, hb] with y hya hyb
    rw [hya, hyb]
  have ht :
      (fun y => A.b y * radialPartial u y + A.c y * angularPartial u y) =ᶠ[𝓝 x]
        (fun y => B.b y * radialPartial u y + B.c y * angularPartial u y) := by
    filter_upwards [hb, hc] with y hyb hyc
    rw [hyb, hyc]
  change
    (fderiv ℝ (fun y => A.a y * radialPartial u y + A.b y * angularPartial u y) x) (1, 0) +
      (fderiv ℝ (fun y => A.b y * radialPartial u y + A.c y * angularPartial u y) x) (0, 1) =
    (fderiv ℝ (fun y => B.a y * radialPartial u y + B.b y * angularPartial u y) x) (1, 0) +
      (fderiv ℝ (fun y => B.b y * radialPartial u y + B.c y * angularPartial u y) x) (0, 1)
  rw [hr.fderiv_eq (𝕜 := ℝ), ht.fderiv_eq (𝕜 := ℝ)]

/-- The global smooth principal field of the negative Airy normal form. -/
def canonicalAiryPrincipalCoefficients : SymmetricCoefficients where
  a _ := 1
  b _ := 0
  c p := -p.1

/-- The explicit physical field obtained by reversing a negative chart.
Its definition uses the stored inverse only on the interior when applied
in the theorem below. -/
def negativeCanonicalEffectiveCoefficients
    (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : SymmetricCoefficients :=
  reverseCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients
    (K.chart z m) (K.inverseChart z m) (K.height z m)

/-- PartA and PartB alone give an actual smooth effective divergence
operator in each negative open physical half. No regularity of the stored
physical coefficients or of the total inverse on the boundary is assumed. -/
theorem negativeCanonicalEffectiveOperator_of_parts
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = false) :
    ContDiffOn ℝ ∞ (negativeCanonicalEffectiveCoefficients S K z m).a
        (physicalPieceOpen S K z m) ∧
      ContDiffOn ℝ ∞ (negativeCanonicalEffectiveCoefficients S K z m).b
        (physicalPieceOpen S K z m) ∧
      ContDiffOn ℝ ∞ (negativeCanonicalEffectiveCoefficients S K z m).c
        (physicalPieceOpen S K z m) ∧
      ∀ u : PolarPoint → ℝ, ContDiffOn ℝ ∞ u (physicalPieceOpen S K z m) →
        ∀ p ∈ physicalPieceOpen S K z m,
          divergenceOperator (L.coefficients z) u p =
            divergenceOperator (negativeCanonicalEffectiveCoefficients S K z m) u p := by
  have hU : IsOpen (physicalPieceOpen S K z m) := (hA.domains z hz hsector m).1
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  rcases hA.charts z hz hsector m with
    ⟨hFV, hGU, hGF, hFG, hF, hG, hh, hpoint⟩
  have hmodel := hB.2.2.2.1 z hz hsector m hm
  have ha : ContDiffOn ℝ ∞ canonicalAiryPrincipalCoefficients.a
      (canonicalOpen S K m) := contDiffOn_const
  have hb : ContDiffOn ℝ ∞ canonicalAiryPrincipalCoefficients.b
      (canonicalOpen S K m) := contDiffOn_const
  have hc : ContDiffOn ℝ ∞ canonicalAiryPrincipalCoefficients.c
      (canonicalOpen S K m) := contDiff_fst.neg.contDiffOn
  have hphysical (p : PolarPoint) (hp : p ∈ physicalPieceOpen S K z m) :
      ContDiffAt ℝ ∞ (negativeCanonicalEffectiveCoefficients S K z m).a p ∧
        ContDiffAt ℝ ∞ (negativeCanonicalEffectiveCoefficients S K z m).b p ∧
        ContDiffAt ℝ ∞ (negativeCanonicalEffectiveCoefficients S K z m).c p ∧
        ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
          divergenceOperator (L.coefficients z) u p =
            divergenceOperator (negativeCanonicalEffectiveCoefficients S K z m) u p := by
    apply reverseCoordinateOperator_action (pot := K.potential z m)
      hU hV hF hG hh ha hb hc
      hFV hGU hGF hFG (fun q hq => (hpoint q hq).1.ne') hp
    intro W hW
    have hFp : K.chart z m p ∈ canonicalOpen S K m := hFV hp
    have hea : (K.coefficients z m).a =ᶠ[𝓝 (K.chart z m p)]
        canonicalAiryPrincipalCoefficients.a := by
      filter_upwards [hV.mem_nhds hFp] with q hq
      exact (hmodel q hq).1
    have heb : (K.coefficients z m).b =ᶠ[𝓝 (K.chart z m p)]
        canonicalAiryPrincipalCoefficients.b := by
      filter_upwards [hV.mem_nhds hFp] with q hq
      exact (hmodel q hq).2.1
    have hec : (K.coefficients z m).c =ᶠ[𝓝 (K.chart z m p)]
        canonicalAiryPrincipalCoefficients.c := by
      filter_upwards [hV.mem_nhds hFp] with q hq
      exact (hmodel q hq).2.2
    have htest := hB.2.2.1 z hz hsector m W hW (K.chart z m p) hFp
    rw [divergenceOperator_eq_of_coefficient_germs W hea heb hec] at htest
    simpa only [canonicalOperator, canonicalSource, hm, Bool.false_eq_true,
      ↓reduceIte, one_mul, hGF p hp] using htest
  refine ⟨fun p hp => (hphysical p hp).1.contDiffWithinAt,
    fun p hp => (hphysical p hp).2.1.contDiffWithinAt,
    fun p hp => (hphysical p hp).2.2.1.contDiffWithinAt, ?_⟩
  intro u hu p hp
  obtain ⟨v, hv, hvgerm⟩ := exists_global_contDiff_germ_of_open hU hu hp
  have he := (hphysical p hp).2.2.2 v hv
  rw [divergenceOperator_eq_of_germ (L.coefficients z) hvgerm,
    divergenceOperator_eq_of_germ
      (negativeCanonicalEffectiveCoefficients S K z m) hvgerm] at he
  exact he

end ContinuousFlexibility.Analysis

