module

public import ContinuousFlexibility.Analysis.N06IntervalCubicPairing
public import ContinuousFlexibility.Analysis.N06PrimitiveC1Green
public import ContinuousFlexibility.Analysis.N06PrimitiveJetRescaling
public import ContinuousFlexibility.Analysis.N06CurrentPositiveRelativePairing
public import ContinuousFlexibility.Scalar.WeightedPartialIdentities

/-!
# Actual cubic tests on the original positive interval

The primitive divided coefficients are smooth after undoing their unit
parametrization.  N04's actual cubic factorization then identifies the
operator on a current physical test.  Its cubic part is L2 because the
actual physical source, the C1 reference operator, and the potential
difference are L2.  The original two-endpoint cubic weight extends the
compact weak equation to the actual averaged physical test.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory CanonicalGeometry
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- The actual positive divided coefficients are smooth on the original
canonical interval; its length is not normalized in this conclusion. -/
theorem n06_primitive_current_divided_contDiff
    (href : referenceStateConditions D S C)
    (hcur : CurrentJets D T S C L K base ε)
    (hlen : K.left m < K.right m)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true) :
    ContDiffOn ℝ ∞ (K.dividedDifference z m).a (canonicalOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.dividedDifference z m).b (canonicalOpen S K m) ∧
    ContDiffOn ℝ ∞ (K.dividedDifference z m).c (canonicalOpen S K m) := by
  have hunit (a : Atom) : ContDiffOn ℝ ∞ (atom D T S C L K z m a) unitStrip := by
    simpa only [n06PrimitiveParameterOfState_lift] using
      (hcur.1 (n06PrimitiveParameterOfState href z hs)
        (n06PrimitiveParameterOfState_mem href hz hs) m a).1
  have hcompose (a : Atom) : ContDiffOn ℝ ∞
      (atom D T S C L K z m a ∘ n07aCanonicalUnitInversePoint K m)
        (canonicalOpen S K m) :=
    (hunit a).comp n07aCanonicalUnitInversePoint_contDiff.contDiffOn
      (n07aCanonicalUnitInversePoint_maps hlen)
  refine ⟨?_, ?_, ?_⟩
  · exact (hcompose .dividedA).congr (fun p _ => by
      simp only [Function.comp_apply, atom, hm, ↓reduceIte,
        n07aCanonicalUnitPoint_inverse hlen])
  · exact (hcompose .dividedB).congr (fun p _ => by
      simp only [Function.comp_apply, atom, hm, ↓reduceIte,
        n07aCanonicalUnitPoint_inverse hlen])
  · exact (hcompose .dividedC).congr (fun p _ => by
      simp only [Function.comp_apply, atom, hm, ↓reduceIte,
        n07aCanonicalUnitPoint_inverse hlen])

/-- The actual current operator separates into the radial reference
operator, the true interval cubic divergence, and the potential difference.
Only one derivative of the reference leading coefficient is needed. -/
theorem n06_primitive_positive_operatorTest_difference
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (_href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S K m))
    (heV : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S K m))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (hcd : DifferentiableAt ℝ c p.1) :
    canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p =
      -n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p +
        divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) (canonicalHeight S K z m φ) p -
        (K.potential z m p - K.potential (C.referenceState, 0) m p) *
          canonicalHeight S K z m φ p := by
  obtain ⟨hA, hB, hCc⟩ := n06_primitive_current_divided_contDiff h01.2.2.1 hcur
    (h04.1.referenceBounds m).2.1 hz hs hm
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q ∈ canonicalOpen S K m :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hga : (K.coefficients (C.referenceState, 0) m).a =ᶠ[𝓝 p] fun q => a q.1 :=
    hnear.mono (fun _ hq => hea hq)
  have hgb : (K.coefficients (C.referenceState, 0) m).b =ᶠ[𝓝 p] fun _ => 0 :=
    hnear.mono (fun _ hq => heb hq)
  have hgc : (K.coefficients (C.referenceState, 0) m).c =ᶠ[𝓝 p] fun q => c q.1 :=
    hnear.mono (fun _ hq => hec hq)
  have hda : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).a p :=
    ((ha.differentiable (by simp) p.1).comp p differentiableAt_fst).congr_of_eventuallyEq hga
  have hdb : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).b p :=
    (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hgb
  have hdc : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).c p :=
    (hcd.comp p differentiableAt_fst).congr_of_eventuallyEq hgc
  have hW : ContDiffAt ℝ 2 (canonicalHeight S K z m φ) p :=
    ((n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ).contDiffAt hnear).of_le (by simp)
  have hd : DifferentiableAt ℝ
      (fun q : PolarPoint => (q.1 - K.left m) * (K.right m - q.1)) p :=
    (differentiableAt_fst.sub (differentiableAt_const (K.left m))).mul
      ((differentiableAt_const (K.right m)).sub differentiableAt_fst)
  have hcurrent := n06_current_source_operatorTest_eq h04 hz hs hφ hp
  have hreference := n06_divergence_radial_coefficients_germ_at hga hgb hgc hcd hW
  have hg := hnear.mono (fun q hq => h04.2.1.2.2.2.2 z hz hs m hm q hq)
  have hdiff := n06_divergenceDifference_eq_cubic_of_germ hda hdb hdc hd
    ((hA.contDiffAt hnear).differentiableAt (by simp))
    ((hB.contDiffAt hnear).differentiableAt (by simp))
    ((hCc.contDiffAt hnear).differentiableAt (by simp)) hW
    (hg.mono fun _ h => h.1) (hg.mono fun _ h => h.2.1) (hg.mono fun _ h => h.2.2)
  rw [hreference] at hdiff
  rw [hcurrent, heV hp]
  simp only [hm, ↓reduceIte, neg_one_mul, n06UnitReferenceTestOperator]
  linear_combination hdiff

/-- The true cubic image of a physical test is L2 on the original piece.
This follows from the actual source identity, with no separate cubic
test estimate supplied as an assumption. -/
theorem n06_primitive_cubicTest_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hV : Continuous V)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S K m))
    (heV : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S K m))
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    MemLp (divergenceOperator
      (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
        (K.dividedDifference z m).a (K.dividedDifference z m).b
        (K.dividedDifference z m).c) (canonicalHeight S K z m φ))
      2 (canonicalMeasure S K m) := by
  have hsource := n06_current_operatorTest_memLp hT hS h01 h03 h04 hz hs m hφ
  have hreference := n06_currentHeight_positiveOperator_memLp_C1 h04 hz hs hφ.1 ha hc hV
    (m := m)
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.1.continuous.continuousOn
  have hpotential := n06_positive_potentialDifference_mul_memLp h04 hz hs hV heV hW
  apply (memLp_congr_ae ?_).mpr ((hsource.add hreference).add hpotential)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  have he := n06_primitive_positive_operatorTest_difference h01 h04 href hcur hz hs hm
    ha hea heb hec heV hφ.1 ⟨hp.1, mem_univ _⟩ (hcd p.1 hp.1)
  simp only [Pi.add_apply]
  linarith only [he]

private theorem n06_middle_abs_le_of_sum {x a b c t : ℝ}
    (h : |x| + |a| + |b| + |c| ≤ t) : |a| ≤ |t| ∧ |b| ≤ |t| := by
  constructor <;> linarith only [h, abs_nonneg x, abs_nonneg a, abs_nonneg b,
    abs_nonneg c, le_abs_self t]

/-- The four coefficients used by the cubic cutoff commutator have a
genuine finite bound on the entire open strip.  The bound is extracted
from the original N04 jet estimate. -/
theorem n06_primitive_cubic_commutator_bounds
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ p ∈ canonicalOpen S K m,
      |(K.dividedDifference z m).a p| ≤ δ ∧
      |(K.dividedDifference z m).b p| ≤ δ ∧
      |radialPartial (K.dividedDifference z m).a p| ≤ δ ∧
      |angularPartial (K.dividedDifference z m).b p| ≤ δ := by
  obtain ⟨hA, hB, _⟩ := n06_primitive_current_divided_contDiff h01.2.2.1 hcur
    (h04.1.referenceBounds m).2.1 hz hs hm
  obtain ⟨B, _hBpos, hbound⟩ := h04.2.2.1 1
  let t : ℝ := B * T.E0 (T.sample (K.cell m)) ^ B *
    (1 + stateGrading S (1 + loss) (z.1 - C.referenceState) + |z.2|)
  have hj (p : PolarPoint) (hp : p ∈ canonicalOpen S K m)
      (i j : ℕ) (hij : i + j ≤ 1) :
      |mixedDerivative i j (K.potential z m) p| +
        |mixedDerivative i j (K.dividedDifference z m).a p| +
        |mixedDerivative i j (K.dividedDifference z m).b p| +
        |mixedDerivative i j (K.dividedDifference z m).c p| ≤ t :=
    hbound z hz m p hp i j hij
  refine ⟨|t|, abs_nonneg t, fun p hp => ?_⟩
  have hzero := n06_middle_abs_le_of_sum (hj p hp 0 0 (by norm_num))
  have hradial := (n06_middle_abs_le_of_sum (hj p hp 1 0 (by norm_num))).1
  have hangular := (n06_middle_abs_le_of_sum (hj p hp 0 1 (by norm_num))).2
  simp only [spaces_mixedDerivative_zero] at hzero
  refine ⟨hzero.1, hzero.2, ?_, ?_⟩
  · rw [radialPartial_eq_mixedDerivative_on (isOpen_Ioo.prod isOpen_univ) hA hp]
    exact hradial
  · rw [angularPartial_eq_mixedDerivative_on (isOpen_Ioo.prod isOpen_univ) hB hp]
    exact hangular

/-- The actual compact principal equation pairs with the half-period
average of every original physical test, on the same canonical measure
and the original interval. -/
theorem n06_primitive_cubic_pairing_fullPhysical_test
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hV : Continuous V)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S K m))
    (heV : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S K m))
    (u g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) ψ p ∂canonicalMeasure S K m)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    (∫ p, g p * canonicalHeight S K z m (n06_radialTestAverage φ) p
      ∂canonicalMeasure S K m) =
      ∫ p, u p * divergenceOperator
        (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
          (K.dividedDifference z m).a (K.dividedDifference z m).b
          (K.dividedDifference z m).c)
        (canonicalHeight S K z m (n06_radialTestAverage φ)) p ∂canonicalMeasure S K m := by
  obtain ⟨hA, hB, hCc⟩ := n06_primitive_current_divided_contDiff h01.2.2.1 hcur
    (h04.1.referenceBounds m).2.1 hz hs hm
  obtain ⟨δ, hδ, hjet⟩ := n06_primitive_cubic_commutator_bounds h01 h04 hcur hz hs hm
  have hψ := n06_radialTestAverage_test hφ
  have hψp := n06_radialTestAverage_periodic hφ.2.1
  exact n06_intervalCubic_pairing_of_openTest (h04.1.referenceBounds m).2.1.le
    hδ hA hB hCc hjet u g hweak
    (n06_current_canonicalHeight_contDiffOn h04 hz hs m hψ.1)
    (fun _ hp => n06_current_canonicalHeight_periodic_on h04 hz hs m hψp hp)
    (n06_current_canonicalHeight_memLp h04 hz hs m hψ.1.continuous.continuousOn)
    (n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (1, 0) (1, 0) hψ.1).1
    (n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (0, 1) (0, 1) hψ.1).1
    (n06_primitive_cubicTest_memLp hT hS h01 h03 h04 href hcur hz hs hm
      ha hc hV hcd hea heb hec heV hψ)

end ContinuousFlexibility.Statements
