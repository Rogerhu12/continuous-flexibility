import ContinuousFlexibility.Analysis.N06EllipticConjugationProbes
import ContinuousFlexibility.Analysis.N06PositivePrincipal
import ContinuousFlexibility.Analysis.N06TurningRootDensity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual positive canonical coefficients are smooth

The physical positive form gives nonzero responses to the true quadratic
probes. These recover differentiability of the previously arbitrary
canonical coefficient functions. The actual principal-density identity
then expresses those functions as smooth forward jets composed with the
original inverse chart. The final neighbourhood is chosen from the original
cutoff data, rather than from an additional canonical regularity hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_coordinatePrincipalDensity_contDiffAt
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {x : PolarPoint} (ha : ContDiffAt ℝ ∞ A.a x) (hb : ContDiffAt ℝ ∞ A.b x)
    (hc : ContDiffAt ℝ ∞ A.c x) (hF : ContDiffAt ℝ ∞ F x)
    (hh : ContDiffAt ℝ ∞ h x) (hJ : planeJacobian F x ≠ 0) :
    ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).a x ∧
      ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).b x ∧
      ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).c x := by
  have hDF : ContDiffAt ℝ ∞ (fderiv ℝ F) x := hF.fderiv_right (by simp)
  have hfr : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (1, 0)) x :=
    hDF.clm_apply contDiffAt_const
  have hft : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (0, 1)) x :=
    hDF.clm_apply contDiffAt_const
  have hdet : ContDiffAt ℝ ∞ (planeJacobian F) x :=
    (hfr.fst.mul hft.snd).sub (hfr.snd.mul hft.fst)
  have hscale : ContDiffAt ℝ ∞ (fun q => h q ^ 2 / |planeJacobian F q|) x :=
    (hh.pow 2).div (hdet.abs hJ) (abs_ne_zero.mpr hJ)
  refine ⟨?_, ?_, ?_⟩
  · exact hscale.mul
      (((ha.mul (hfr.fst.pow 2)).add
        (((contDiffAt_const.mul hb).mul hfr.fst).mul hft.fst)).add
        (hc.mul (hft.fst.pow 2)))
  · exact hscale.mul
      ((((ha.mul hfr.fst).mul hfr.snd).add
        (hb.mul ((hfr.fst.mul hft.snd).add (hft.fst.mul hfr.snd)))).add
        ((hc.mul hft.fst).mul hft.snd))
  · exact hscale.mul
      (((ha.mul (hfr.snd.pow 2)).add
        (((contDiffAt_const.mul hb).mul hfr.snd).mul hft.snd)).add
        (hc.mul (hft.snd.pow 2)))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The original operator identity and actual ellipticity recover
canonical differentiability, without presupposing it in a transformation rule. -/
theorem n06_positive_canonical_coefficients_differentiableAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (hprincipal : 0 < (L.coefficients z).a (K.inverseChart z m p) ∧
      0 < (L.coefficients z).a (K.inverseChart z m p) *
        (L.coefficients z).c (K.inverseChart z m p) -
          (L.coefficients z).b (K.inverseChart z m p) ^ 2) :
    DifferentiableAt ℝ (K.coefficients z m).a p ∧
      DifferentiableAt ℝ (K.coefficients z m).b p ∧
      DifferentiableAt ℝ (K.coefficients z m).c p := by
  let x := K.inverseChart z m p
  have hparts := n06_N04_qualitative_parts h04
  have hcharts := hparts.1.charts z hz hs m
  have hx : x ∈ physicalPieceOpen S K z m := hcharts.2.1 hp
  have hFx : K.chart z m x = p := hcharts.2.2.2.1 p hp
  have hpa : x ∈ annularOpen D := (h04.1.domains z hz hs m).2.2.1 hx
  have hpos : 0 < deriv D.w x.1 := (h04.1.domains z hz hs m).2.2.2.2.2.2.1 x hx hm
  have hphys := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03
    hz hs hpa hpos.le
  have hF := hcharts.2.2.2.2.1.contDiffAt ((h04.1.domains z hz hs m).1.mem_nhds hx)
  have hH := hcharts.2.2.2.2.2.2.1.contDiffAt ((h04.1.domains z hz hs m).1.mem_nhds hx)
  have hgood := hcharts.2.2.2.2.2.2.2 x hx
  have hresponse := n06_principalPair_coordinates_pos hprincipal.1 hprincipal.2
    (hF.differentiableAt (by simp)) hgood.2.1
  have hop (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W) :
      K.height z m x / |planeJacobian (K.chart z m) x| *
          divergenceOperator (L.coefficients z) (fun y => K.height z m y * W (K.chart z m y)) x =
        divergenceOperator (K.coefficients z m) W (K.chart z m x) +
          (-K.potential z m p) * W (K.chart z m x) := by
    have he := hparts.2.2.2.1 z hz hs m W hW p hp
    simp only [canonicalOperator, canonicalSource, hm, ↓reduceIte, neg_mul, one_mul] at he
    rw [hFx]
    simp only [div_mul_eq_mul_div]
    linarith only [he]
  have hd := n06_coefficients_differentiable_of_conjugation
    hphys.1 hphys.2.1 hphys.2.2 hH hF hgood.1.ne' hgood.2.1
    hresponse.1.ne' hresponse.2.ne' hop
  simpa only [hFx] using hd

/-- With differentiability now derived, the existing quadratic identity
identifies all three actual canonical coefficient values. -/
theorem n06_positive_canonical_coefficients_eq_density
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (hprincipal : 0 < (L.coefficients z).a (K.inverseChart z m p) ∧
      0 < (L.coefficients z).a (K.inverseChart z m p) *
        (L.coefficients z).c (K.inverseChart z m p) -
          (L.coefficients z).b (K.inverseChart z m p) ^ 2) :
    (K.coefficients z m).a p =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a
          (K.inverseChart z m p) ∧
      (K.coefficients z m).b p =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b
          (K.inverseChart z m p) ∧
      (K.coefficients z m).c p =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).c
          (K.inverseChart z m p) := by
  have hparts := n06_N04_qualitative_parts h04
  have hcharts := hparts.1.charts z hz hs m
  have hx := hcharts.2.1 hp
  have hpa : K.inverseChart z m p ∈ annularOpen D :=
    (h04.1.domains z hz hs m).2.2.1 hx
  have hpos := (h04.1.domains z hz hs m).2.2.2.2.2.2.1 _ hx hm
  have hphys := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03
    hz hs hpa hpos.le
  have hd := n06_positive_canonical_coefficients_differentiableAt hT hS h01 h03 h04
    hz hs m hm hp hprincipal
  exact canonicalPrincipalCoefficients_eq_density hparts.1 hparts.2 hz hs m hp
    (hphys.1.differentiableAt (by simp)) (hphys.2.1.differentiableAt (by simp))
    (hphys.2.2.differentiableAt (by simp)) hd.1 hd.2.1 hd.2.2

/-- Smoothness of the actual canonical functions follows from equality
with the genuine smooth forward density on the open piece. -/
theorem n06_positive_canonical_coefficients_contDiffOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    (hprincipal : ∀ x ∈ physicalPieceOpen S K z m,
      0 < (L.coefficients z).a x ∧
        0 < (L.coefficients z).a x * (L.coefficients z).c x - (L.coefficients z).b x ^ 2) :
    ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m) := by
  have hparts := n06_N04_qualitative_parts h04
  have hcharts := hparts.1.charts z hz hs m
  have hloc (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
      ContDiffAt ℝ ∞ (K.coefficients z m).a p ∧
        ContDiffAt ℝ ∞ (K.coefficients z m).b p ∧
        ContDiffAt ℝ ∞ (K.coefficients z m).c p := by
    let x := K.inverseChart z m p
    have hx : x ∈ physicalPieceOpen S K z m := hcharts.2.1 hp
    have hpa : x ∈ annularOpen D := (h04.1.domains z hz hs m).2.2.1 hx
    have hpos := (h04.1.domains z hz hs m).2.2.2.2.2.2.1 x hx hm
    have hphys := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03
      hz hs hpa hpos.le
    have hF := hcharts.2.2.2.2.1.contDiffAt ((h04.1.domains z hz hs m).1.mem_nhds hx)
    have hH := hcharts.2.2.2.2.2.2.1.contDiffAt ((h04.1.domains z hz hs m).1.mem_nhds hx)
    have hG := hcharts.2.2.2.2.2.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
    have hJ := (hcharts.2.2.2.2.2.2.2 x hx).2.1
    have hden := n06_coordinatePrincipalDensity_contDiffAt
      hphys.1 hphys.2.1 hphys.2.2 hF hH hJ
    have he : ∀ᶠ q in 𝓝 p,
        (K.coefficients z m).a q =
          (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a
            (K.inverseChart z m q) ∧
        (K.coefficients z m).b q =
          (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b
            (K.inverseChart z m q) ∧
        (K.coefficients z m).c q =
          (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).c
            (K.inverseChart z m q) := by
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
      exact n06_positive_canonical_coefficients_eq_density hT hS h01 h03 h04
        hz hs m hm hq (hprincipal _ (hcharts.2.1 hq))
    exact ⟨(hden.1.comp p hG).congr_of_eventuallyEq (he.mono fun _ h => h.1),
      (hden.2.1.comp p hG).congr_of_eventuallyEq (he.mono fun _ h => h.2.1),
      (hden.2.2.comp p hG).congr_of_eventuallyEq (he.mono fun _ h => h.2.2)⟩
  exact ⟨fun p hp => (hloc p hp).1.contDiffWithinAt,
    fun p hp => (hloc p hp).2.1.contDiffWithinAt,
    fun p hp => (hloc p hp).2.2.contDiffWithinAt⟩

/-- The original N01--N04 data supply one actual neighbourhood on which
all positive canonical principal coefficients are smooth. -/
theorem n06_exists_positive_canonical_regular_neighborhood
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base ε', stateSector S z.1 →
        ∀ m, K.positive m = true →
          ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
          ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
          ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m) := by
  obtain ⟨ε', hε', hle, hpos⟩ := n06_exists_positivePrincipal_neighborhood hT hS h01 h03
  refine ⟨ε', hε', hle, ?_⟩
  intro z hz hs m hm
  have hzold : z ∈ stateNeighborhood S C base ε :=
    ⟨hz.1.trans_le hle, hz.2.trans_le hle⟩
  apply n06_positive_canonical_coefficients_contDiffOn hT hS h01 h03 h04 hzold hs m hm
  intro x hx
  exact hpos z hz hs x ((h04.1.domains z hzold hs m).2.2.1 hx)
    ((h04.1.domains z hzold hs m).2.2.2.2.2.2.1 x hx hm)

end ContinuousFlexibility.Statements
