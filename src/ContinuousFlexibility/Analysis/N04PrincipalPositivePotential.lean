import ContinuousFlexibility.Analysis.N04PrincipalPositiveFormula
import ContinuousFlexibility.Analysis.N07aCanonicalOpenTests

/-!
# The positive potential in reciprocal-height flux form

The operator identity with the physical constant function gives the
potential as the pulled height times the divergence of the reciprocal
pulled height. On the positive unit interval this is a sum of two first
mixed derivatives of products of the principal fields and height jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

/-- The displayed two fluxes use ordinary mixed derivatives, exactly
the derivatives retained by the current interface. -/
theorem n04PrincipalPositive_divergence_mixed_flux
    {U : Set PolarPoint} (hU : IsOpen U) (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a U) (hb : ContDiffOn ℝ ∞ A.b U)
    (hc : ContDiffOn ℝ ∞ A.c U) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v U) :
    EqOn (divergenceOperator A v)
      (fun p =>
        mixedDerivative 1 0
          (fun q => A.a q * mixedDerivative 1 0 v q + A.b q * mixedDerivative 0 1 v q) p +
        mixedDerivative 0 1
          (fun q => A.b q * mixedDerivative 1 0 v q + A.c q * mixedDerivative 0 1 v q) p)
      U := by
  have hvr : ContDiffOn ℝ ∞ (radialPartial v) U :=
    (hv.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hvt : ContDiffOn ℝ ∞ (angularPartial v) U :=
    (hv.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hR := (ha.mul hvr).add (hb.mul hvt)
  have hT := (hb.mul hvr).add (hc.mul hvt)
  have heR : EqOn (fun q => A.a q * radialPartial v q + A.b q * angularPartial v q)
      (fun q => A.a q * mixedDerivative 1 0 v q + A.b q * mixedDerivative 0 1 v q) U := by
    intro q hq
    dsimp only
    rw [radialPartial_eq_mixedDerivative_on hU hv hq,
      angularPartial_eq_mixedDerivative_on hU hv hq]
  have heT : EqOn (fun q => A.b q * radialPartial v q + A.c q * angularPartial v q)
      (fun q => A.b q * mixedDerivative 1 0 v q + A.c q * mixedDerivative 0 1 v q) U := by
    intro q hq
    dsimp only
    rw [radialPartial_eq_mixedDerivative_on hU hv hq,
      angularPartial_eq_mixedDerivative_on hU hv hq]
  intro p hp
  change radialPartial (fun q => A.a q * radialPartial v q + A.b q * angularPartial v q) p +
    angularPartial (fun q => A.b q * radialPartial v q + A.c q * angularPartial v q) p = _
  rw [radialPartial_eq_mixedDerivative_on hU hR hp,
    angularPartial_eq_mixedDerivative_on hU hT hp,
    mixedDerivative_congr_on_open hU heR 1 0 hp,
    mixedDerivative_congr_on_open hU heT 0 1 hp]

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Smoothness of the positive reciprocal pulled height follows from
the actual qualitative range certificate, without an inverse estimate. -/
theorem n04PrincipalPositive_reciprocal_pulledHeight_smooth {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m) :
    ContDiff ℝ ∞ (fun q => (G.pulledHeight η z m q)⁻¹) := by
  have hw : G.lift η z ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector (G.S η) (G.lift η z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hg := G.n04PrincipalPositive_rangeGeometry h η hw hs hm
  have hv : ContDiff ℝ ∞ (fun p : PolarPoint =>
      ((G.V η).height (G.lift η z) m ((G.V η).inverseChart (G.lift η z) m p))⁻¹) :=
    (hg.height_smooth.comp hg.inverse_smooth).inv
      (fun p => (hg.height_positive ((G.V η).inverseChart (G.lift η z) m p)).ne')
  simpa only [pulledHeight, heightField, pulledPoint,
    G.n04PrincipalPositive_unitPoint_eq η hm, id_eq, Function.comp_apply] using hv

/-- Positive potential formula after the principal families have been
constructed. The hypotheses here are only their spatial smoothness. -/
theorem n04PrincipalPositive_potential_unit_formula {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m)
    (ha : ContDiffOn ℝ ∞ (G.atomFamily η .principalA z m) unitStrip)
    (hb : ContDiffOn ℝ ∞ (G.atomFamily η .principalB z m) unitStrip)
    (hc : ContDiffOn ℝ ∞ (G.atomFamily η .principalC z m) unitStrip)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    let H := G.pulledHeight η z m
    let V := fun p => (H p)⁻¹
    let A := G.atomFamily η .principalA z m
    let B := G.atomFamily η .principalB z m
    let C := G.atomFamily η .principalC z m
    G.atomFamily η .potential z m q = H q *
      (mixedDerivative 1 0
        (fun p => A p * mixedDerivative 1 0 V p + B p * mixedDerivative 0 1 V p) q +
       mixedDerivative 0 1
        (fun p => B p * mixedDerivative 1 0 V p + C p * mixedDerivative 0 1 V p) q) := by
  let w := G.lift η z
  have hw : w ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector (G.S η) w.1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hunit := G.n04PrincipalPositive_unitPoint_eq η hm
  have hend := G.n04PrincipalDivided_positive_endpoints η hm
  have hqK : q ∈ canonicalOpen (G.S η) (G.V η) m := by
    simpa only [canonicalOpen, unitStrip, hend.1, hend.2] using hq
  let v : PolarPoint → ℝ := fun p =>
    ((G.V η).height w m ((G.V η).inverseChart w m p))⁻¹
  have hv : ContDiffOn ℝ ∞ v unitStrip := by
    apply (G.n04PrincipalPositive_reciprocal_pulledHeight_smooth h η hz hm).contDiffOn.congr
    intro p hp
    simp only [v, w, pulledHeight, heightField, pulledPoint, hunit, id_eq]
  have ha' : ContDiffOn ℝ ∞ ((G.V η).coefficients w m).a unitStrip := by
    apply ha.congr
    intro p hp
    simp only [atomFamily, atom, hunit, id_eq, w]
  have hb' : ContDiffOn ℝ ∞ ((G.V η).coefficients w m).b unitStrip := by
    apply hb.congr
    intro p hp
    simp only [atomFamily, atom, hunit, id_eq, w]
  have hc' : ContDiffOn ℝ ∞ ((G.V η).coefficients w m).c unitStrip := by
    apply hc.congr
    intro p hp
    simp only [atomFamily, atom, hunit, id_eq, w]
  have hdiv := n04PrincipalPositive_divergence_mixed_flux
    (isOpen_Ioo.prod isOpen_univ) ((G.V η).coefficients w m) ha' hb' hc' hv hq
  have hpot := G.n04PrincipalPositive_potential_identity h η hw hs m hqK
  have hpositive : (G.V η).positive m = true := hm
  rw [hpositive] at hpot
  simp only [↓reduceIte, neg_neg, one_mul] at hpot
  rw [hdiv] at hpot
  simpa only [atomFamily, atom, pulledHeight, heightField, pulledPoint,
    hunit, id_eq, v, w] using hpot

end N04RealizationGauge

end ContinuousFlexibility.Analysis
