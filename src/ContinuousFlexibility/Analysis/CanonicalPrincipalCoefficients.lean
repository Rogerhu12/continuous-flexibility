import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback
import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# Principal density forced by the canonical operator identity

The qualitative canonical identity is tested on actual smooth quadratics.
Its type sign cancels from the principal terms. On a negative piece the
canonical coefficient regularity follows from the prescribed constant
normal form on the open piece, rather than being assumed separately.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem canonicalPrincipalCoefficients_eq_density
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (ha : DifferentiableAt ℝ (L.coefficients z).a (K.inverseChart z m p))
    (hb : DifferentiableAt ℝ (L.coefficients z).b (K.inverseChart z m p))
    (hc : DifferentiableAt ℝ (L.coefficients z).c (K.inverseChart z m p))
    (hKa : DifferentiableAt ℝ (K.coefficients z m).a p)
    (hKb : DifferentiableAt ℝ (K.coefficients z m).b p)
    (hKc : DifferentiableAt ℝ (K.coefficients z m).c p) :
    (K.coefficients z m).a p =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a
          (K.inverseChart z m p) ∧
      (K.coefficients z m).b p =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b
          (K.inverseChart z m p) ∧
      (K.coefficients z m).c p =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).c
          (K.inverseChart z m p) := by
  let x := K.inverseChart z m p
  have hcharts := hA.2.2.2.2.2.2.2.1 z hz hs m
  have hx : x ∈ physicalPieceOpen S K m := hcharts.2.1 hp
  have hFx : K.chart z m x = p := hcharts.2.2.2.1 p hp
  have hOpen : IsOpen (physicalPieceOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hF : ContDiffAt ℝ 2 (K.chart z m) x :=
    ((hcharts.2.2.2.2.1 x hx).contDiffAt (hOpen.mem_nhds hx)).of_le (by simp)
  have hh : ContDiffAt ℝ 2 (K.height z m) x :=
    ((hcharts.2.2.2.2.2.2.1 x hx).contDiffAt (hOpen.mem_nhds hx)).of_le (by simp)
  have hBa : DifferentiableAt ℝ (K.coefficients z m).a (K.chart z m x) := by
    simpa only [hFx] using hKa
  have hBb : DifferentiableAt ℝ (K.coefficients z m).b (K.chart z m x) := by
    simpa only [hFx] using hKb
  have hBc : DifferentiableAt ℝ (K.coefficients z m).c (K.chart z m x) := by
    simpa only [hFx] using hKc
  have hop (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W) :
      K.height z m x *
          divergenceOperator (L.coefficients z) (fun y => K.height z m y * W (K.chart z m y)) x /
            |planeJacobian (K.chart z m) x| =
        divergenceOperator (K.coefficients z m) W (K.chart z m x) +
          ((if K.positive m then -1 else (1 : ℝ)) * K.potential z m p) *
            W (K.chart z m x) := by
    have he := hB.2.2.1 z hz hs m W hW p hp
    simp only [hFx]
    cases hpos : K.positive m
    · simpa only [canonicalOperator, canonicalSource, hpos, Bool.false_eq_true,
        ↓reduceIte, one_mul] using he
    · simp only [canonicalOperator, canonicalSource, hpos, ↓reduceIte,
        neg_mul, one_mul] at he ⊢
      linarith [he]
  have h := principalCoefficients_of_operator_identity ha hb hc hF hh hBa hBb hBc hop
  simpa only [hFx] using h

/-- The negative canonical coefficient germs are the actual prescribed
normal form, so their differentiability follows from the open-piece identity. -/
theorem differentiableAt_negativeCanonicalCoefficients
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    DifferentiableAt ℝ (K.coefficients z m).a p ∧
      DifferentiableAt ℝ (K.coefficients z m).b p ∧
      DifferentiableAt ℝ (K.coefficients z m).c p := by
  have hOpen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have he : ∀ᶠ y in 𝓝 p,
      (K.coefficients z m).a y = 1 ∧ (K.coefficients z m).b y = 0 ∧
        (K.coefficients z m).c y = -y.1 := by
    filter_upwards [hOpen.mem_nhds hp] with y hy
    exact hB.2.2.2.1 z hz hs m hm y hy
  exact ⟨differentiableAt_const.congr_of_eventuallyEq (he.mono (fun _ hy => hy.1)),
    differentiableAt_const.congr_of_eventuallyEq (he.mono (fun _ hy => hy.2.1)),
    differentiableAt_fst.fun_neg.congr_of_eventuallyEq (he.mono (fun _ hy => hy.2.2))⟩

/-- On the actual physical negative piece the transported principal density
is the universal normal form, evaluated at the actual chart. -/
theorem negativePrincipalDensity_eq_normalForm
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m)
    (ha : DifferentiableAt ℝ (L.coefficients z).a x)
    (hb : DifferentiableAt ℝ (L.coefficients z).b x)
    (hc : DifferentiableAt ℝ (L.coefficients z).c x) :
    (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a x = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b x = 0 ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).c x =
        -(K.chart z m x).1 := by
  have hcharts := hA.2.2.2.2.2.2.2.1 z hz hs m
  have hp := hcharts.1 hx
  have hi := hcharts.2.2.1 x hx
  have hreg := differentiableAt_negativeCanonicalCoefficients hB hz hs m hm hp
  have ha' : DifferentiableAt ℝ (L.coefficients z).a
      (K.inverseChart z m (K.chart z m x)) := by simpa only [hi] using ha
  have hb' : DifferentiableAt ℝ (L.coefficients z).b
      (K.inverseChart z m (K.chart z m x)) := by simpa only [hi] using hb
  have hc' : DifferentiableAt ℝ (L.coefficients z).c
      (K.inverseChart z m (K.chart z m x)) := by simpa only [hi] using hc
  have h := canonicalPrincipalCoefficients_eq_density hA hB hz hs m hp
    ha' hb' hc' hreg.1 hreg.2.1 hreg.2.2
  simp only [hi] at h
  have hn := hB.2.2.2.1 z hz hs m hm _ hp
  exact ⟨h.1.symm.trans hn.1, h.2.1.symm.trans hn.2.1, h.2.2.symm.trans hn.2.2⟩

end ContinuousFlexibility.Analysis
