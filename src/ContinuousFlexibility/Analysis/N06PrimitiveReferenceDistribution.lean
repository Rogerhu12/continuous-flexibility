import ContinuousFlexibility.Statements.N06PrimitiveGeometryBridge
import ContinuousFlexibility.Analysis.N06ReferenceCanonicalEquation
import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns
import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients
import ContinuousFlexibility.Analysis.N07aCanonicalTestDivergence

/-!
# The genuine N05 reference equation in the open coefficient algebra

The source below is the original source, the actual reference potential,
and the three original scalar columns.  The equation comes from the same
N05 graph, before a relative operator or an N06 inverse has been built.
No unit-length assertion is made about the canonical interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- On a positive piece the primitive scalar atoms are precisely the
three physical columns in the original N05 reference relation. -/
theorem n06_primitiveReference_positive_columns
    (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    {m : ℕ} (hm : K.positive m = true) (i : Fin 3) :
    EqOn (n07aScalarColumn D S C L K (C.referenceState, 0) m i)
      (canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
      (canonicalOpen S K m) := by
  intro p hp
  let x : PolarPoint := K.inverseChart (C.referenceState, 0) m p
  have hx : x ∈ physicalPieceOpen S K (C.referenceState, 0) m :=
    (hA.charts _ hz hs m).2.1 hp
  have hxref : x ∈ referencePhysicalPieceOpen S K m := by
    simpa only [hA.referenceDomain m] using hx
  have hxcore : x ∈ annularOpen D := (hA.domains _ hz hs m).2.2.1 hx
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hxne : x.1 ≠ 0 := (hgeom.1.trans hxcore.1.1).ne'
  fin_cases i
  · have hχ : ContDiff ℝ ∞ (n06ReferenceLeftField S.chiLeft) :=
      n06_referenceLeftField_contDiff hS.2.2.1.1
    obtain ⟨ha, hbeta, hc⟩ :=
      n06_correctedReference_positivePiece_germ h03 hA hw href hz hs m hm hxref
    let A0 : SymmetricCoefficients :=
      ⟨fun q => D.w q.1, fun _ => 0, fun q => deriv D.w q.1 / q.1⟩
    have he : divergenceOperator (L.coefficients (C.referenceState, 0))
        (n06ReferenceLeftField S.chiLeft) x =
          n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) x := by
      calc
        _ = divergenceOperator A0 (n06ReferenceLeftField S.chiLeft) x :=
          n06_divergenceOperator_congr_germ _ ha hbeta hc
        _ = _ := Radial.reference_divergence_eq_radialPDE hw hχ hxne
    change K.height (C.referenceState, 0) m x *
        divergenceOperator (L.coefficients (C.referenceState, 0))
          (n06ReferenceLeftField S.chiLeft) x /
          |planeJacobian (K.chart (C.referenceState, 0) m) x| =
      K.height (C.referenceState, 0) m x *
        n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) x /
          |planeJacobian (K.chart (C.referenceState, 0) m) x|
    rw [he]
  · have he := n06_referenceScalarField_nu_actual hD hb href hxcore
    change K.height (C.referenceState, 0) m x *
        nuColumnField D S C (C.referenceState, 0) x /
          |planeJacobian (K.chart (C.referenceState, 0) m) x| =
      K.height (C.referenceState, 0) m x * n06ReferenceScalarField D S 1 x /
          |planeJacobian (K.chart (C.referenceState, 0) m) x|
    rw [he]
  · rfl

private theorem n06_primitiveReference_rhs_ae
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    {m : ℕ} (hlen : K.left m < K.right m) (hm : K.positive m = true)
    (hcol : ∀ i : Fin 3,
      EqOn (n07aScalarColumn D S C L K (C.referenceState, 0) m i)
        (canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
        (canonicalOpen S K m))
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) :
    (n07aReferenceCanonicalRhs hJ m hlen U F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => K.potential (C.referenceState, 0) m p * U.1 m p -
        n06ReferenceCanonicalForcing D S C K U F m p := by
  let q := N07aCanonicalOpenCoefficient.constMul
    (if K.positive m then -1 else (1 : ℝ)) (n07aReferenceOpenCoefficient hJ m hlen 4)
  let col := n07aReferenceScalarOpenCoefficient hJ m hlen
  filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m),
    Lp.coeFn_sub (F m) (q.mul (U.1 m)),
    Lp.coeFn_sub (F m - q.mul (U.1 m)) (U.2.1 • (col 0).toLp),
    Lp.coeFn_sub (F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp)
      (U.2.2.1 • (col 1).toLp),
    Lp.coeFn_sub (F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp -
      U.2.2.1 • (col 1).toLp) (U.2.2.2 • (col 2).toLp),
    q.mul_ae (U.1 m),
    Lp.coeFn_smul U.2.1 (col 0).toLp,
    Lp.coeFn_smul U.2.2.1 (col 1).toLp,
    Lp.coeFn_smul U.2.2.2 (col 2).toLp,
    (col 0).toLp_ae, (col 1).toLp_ae, (col 2).toLp_ae]
    with p hp h₀ h₁ h₂ h₃ hq hs₀ hs₁ hs₂ hc₀ hc₁ hc₂
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h₀ h₁ h₂ h₃ hs₀ hs₁ hs₂
  change (F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp -
      U.2.2.1 • (col 1).toLp - U.2.2.2 • (col 2).toLp) p = _
  rw [h₃, h₂, h₁, h₀, hq, hs₀, hs₁, hs₂, hc₀, hc₁, hc₂]
  have hqval : q.value p = -K.potential (C.referenceState, 0) m p := by
    change (if K.positive m then -1 else (1 : ℝ)) *
      K.potential (C.referenceState, 0) m p = _
    simp only [hm, ↓reduceIte, neg_one_mul]
  have hcval (i : Fin 3) : (col i).value p =
      canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i) p :=
    hcol i hp
  rw [hqval, hcval 0, hcval 1, hcval 2]
  change F m p - (-K.potential (C.referenceState, 0) m p * U.1 m p) -
      U.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 0) p -
      U.2.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 1) p -
      U.2.2.2 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 2) p =
    K.potential (C.referenceState, 0) m p * U.1 m p -
      (-F m p +
        U.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 0) p +
        U.2.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 1) p +
        U.2.2.2 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S 2) p)
  ring

variable {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}

/-- Every original N05 graph element obeys the actual divergence-only
reference equation used by the open normal bootstrap. -/
theorem n06_primitiveReference_positive_distribution
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (u : B.Space) (m : ℕ) (hm : K.positive m = true) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m)
      (u.val.1.1 m)
      (n07aReferenceCanonicalRhs hJ m (h04.1.referenceBounds m).2.1
        u.val.1 (V.forget (3 / 4 : ℝ) 0 b u.val.2)) := by
  have hD : IsAccumulatingProfile D := h01.1.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  have href : referenceStateConditions D S C := h01.2.2.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector href
  let hlen : K.left m < K.right m := (h04.1.referenceBounds m).2.1
  let U : CanonicalL2 S K m := u.val.1.1 m
  let G : CanonicalL2 S K m := n07aReferenceCanonicalRhs hJ m hlen
    u.val.1 (V.forget (3 / 4 : ℝ) 0 b u.val.2)
  let q := n07aReferenceOpenCoefficient hJ m hlen 4
  have hcol := n06_primitiveReference_positive_columns hD hb hS h03 h04.1 href hz hs hm
  have hG := n06_primitiveReference_rhs_ae hJ hlen hm hcol u.val.1
    (V.forget (3 / 4 : ℝ) 0 b u.val.2)
  intro φ hφ
  have hdiv := n07a_canonicalTest_divergence (K.coefficients (C.referenceState, 0) m)
    (n07aReferenceOpenCoefficient hJ m hlen 0).smooth
    (n07aReferenceOpenCoefficient hJ m hlen 1).smooth
    (n07aReferenceOpenCoefficient hJ m hlen 2).smooth
    (n07aReferenceOpenCoefficient hJ m hlen 0).periodic
    (n07aReferenceOpenCoefficient hJ m hlen 1).periodic
    (n07aReferenceOpenCoefficient hJ m hlen 2).periodic hφ
  have hiD : Integrable (fun p => U p *
      divergenceOperator (K.coefficients (C.referenceState, 0) m) φ p)
      (canonicalMeasure S K m) := (Lp.memLp U).integrable_mul (n07a_canonicalTest_memLp hdiv)
  have hiV : Integrable (fun p => U p * (K.potential (C.referenceState, 0) m p * φ p))
      (canonicalMeasure S K m) :=
    (Lp.memLp U).integrable_mul
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mul_on hφ q.smooth q.periodic))
  have hiG : Integrable (fun p => G p * φ p) (canonicalMeasure S K m) :=
    (Lp.memLp G).integrable_mul (n07a_canonicalTest_memLp hφ)
  have hop : (fun p => U p * canonicalOperator S K L (C.referenceState, 0) m φ p)
      =ᵐ[canonicalMeasure S K m] fun p =>
        -(U p * divergenceOperator (K.coefficients (C.referenceState, 0) m) φ p) +
          U p * (K.potential (C.referenceState, 0) m p * φ p) := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    rw [h04.2.1.2.2.1 _ hz hs m φ hφ.1 p hp, hm, if_pos rfl]
    ring
  have hforcing : (fun p => n06ReferenceCanonicalForcing D S C K u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) m p * φ p)
      =ᵐ[canonicalMeasure S K m] fun p =>
        U p * (K.potential (C.referenceState, 0) m p * φ p) - G p * φ p := by
    filter_upwards [hG] with p hp
    change G p = K.potential (C.referenceState, 0) m p * U p - _ at hp
    rw [hp]
    ring
  have he := n06N05_positive_canonicalWeakPairing hD hb hS h03 h04.1 h05
    href hz hs u hm hφ
  rw [integral_congr_ae hop, integral_add hiD.neg hiV, integral_neg,
    integral_congr_ae hforcing, integral_sub hiV hiG] at he
  change (∫ p, U p * divergenceOperator (K.coefficients (C.referenceState, 0) m) φ p
    ∂canonicalMeasure S K m) = ∫ p, G p * φ p ∂canonicalMeasure S K m
  linarith only [he]

end ContinuousFlexibility.Analysis
