import ContinuousFlexibility.Analysis.N06CurrentTestLp
import ContinuousFlexibility.Analysis.N06CanonicalTestOperator
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeedExtension

/-!
# The actual current operator on a positive closed physical piece

The N03 correction agrees with the original coefficients on germs at
positive-type points and at turning points. Positivity of the reference
slope in a positive piece and continuity of that slope make it nonnegative
on the whole closed piece. N01's actual denominator bounds then give
smoothness of the corrected coefficients at every point of this closed
piece inside the annulus. Outside the annulus a genuine RadialTest has a
zero germ, as does its actual differential expression. This proves L2
membership of the transformed operator test without a smooth-coefficient
assumption on the correction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Local smooth coefficients suffice for the actual divergence expression. -/
theorem n06_contDiffAt_divergenceOperator
    {A : SymmetricCoefficients} {φ : PolarPoint → ℝ} {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a p) (hb : ContDiffAt ℝ ∞ A.b p)
    (hc : ContDiffAt ℝ ∞ A.c p) (hφ : ContDiffAt ℝ ∞ φ p) :
    ContDiffAt ℝ ∞ (divergenceOperator A φ) p := by
  have hr := contDiffAt_radialPartial hφ (m := ∞) (by simp)
  have ht := contDiffAt_angularPartial hφ (m := ∞) (by simp)
  exact (contDiffAt_radialPartial ((ha.mul hr).add (hb.mul ht)) (m := ∞) (by simp)).add
    (contDiffAt_angularPartial ((hb.mul hr).add (hc.mul ht)) (m := ∞) (by simp))

/-- A zero test germ gives a zero operator germ even when no regularity
of the coefficients has yet been established. -/
theorem n06_divergenceOperator_eventually_zero
    (A : SymmetricCoefficients) {φ : PolarPoint → ℝ} {p : PolarPoint}
    (hφ : φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ)) :
    divergenceOperator A φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  filter_upwards [hφ.eventuallyEq_nhds] with q hq
  exact (n06_divergenceOperator_input_congr_germ A hq).trans
    (divergenceOperator_const A 0 q)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- N01 supplies every denominator and regularity fact required by the
original physical coefficient formula at an actual annular point. -/
theorem n06_originalCoefficients_contDiffAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p ∧
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p ∧
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).c p := by
  have hw := contDiff_stateProfile_of_n01 hS hT h01 z.1
  have hh := neighborhood_stateHeight_contDiff hT hS hw
  have ha := h01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hwr : 0 < D.w p.1 := h01.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1
  have hws : 0 < stateProfile D S C z.1 p.1 :=
    (div_pos_iff_of_pos_right hwr).mp (lt_of_lt_of_le (by norm_num) ha.1)
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hws).mp (lt_of_lt_of_le (by norm_num) ha.2.2.1)
  have hdisc : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p := lt_of_lt_of_le (by norm_num) ha.2.2.2.2.1
  have hr : p.1 ≠ 0 := (h01.1.1.choose_spec.1.1.trans hp.1.1).ne'
  have hreg := contDiffAt_heightLinearCoefficients hw.contDiffAt hh.contDiffAt hr hdisc hQ.ne'
  exact ⟨hreg.1, hreg.2.1, hreg.2.2.2.1⟩

/-- The real N03 germs preserve full local smoothness wherever the
reference slope is nonnegative, including its zero set. -/
theorem n06_correctedCoefficients_contDiffAt_of_nonneg
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hpos : 0 ≤ deriv D.w p.1) :
    ContDiffAt ℝ ∞ (L.coefficients z).a p ∧
      ContDiffAt ℝ ∞ (L.coefficients z).b p ∧
      ContDiffAt ℝ ∞ (L.coefficients z).c p := by
  have hreg := n06_originalCoefficients_contDiffAt hT hS h01 hz hs hp
  have hea : (L.coefficients z).a =ᶠ[𝓝 p] (originalCoefficients D S C z).a :=
    Filter.Eventually.of_forall (h03.1 z hz hs)
  have hbc : (L.coefficients z).b =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
      (L.coefficients z).c =ᶠ[𝓝 p] (originalCoefficients D S C z).c := by
    rcases lt_or_eq_of_le hpos with h | h
    · exact h03.2.1 z hz hs p hp h
    · exact h03.2.2.1 z hz hs p hp h.symm
  exact ⟨hreg.1.congr_of_eventuallyEq hea,
    hreg.2.1.congr_of_eventuallyEq hbc.1, hreg.2.2.congr_of_eventuallyEq hbc.2⟩

/-- The actual closed positive piece has nonnegative reference slope.
Its endpoints need not be stipulated to be turning points. -/
theorem n06_positivePiece_closed_slope_nonneg
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (m : ℕ) (hm : K.positive m = true) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    0 ≤ deriv D.w r := by
  have hw : ContDiff ℝ ∞ D.w := h01.1.1.choose_spec.1.2.2.1.1
  have hc : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hrcl : r ∈ closure (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    rw [closure_Ioo (h04.1.referenceBounds m).1.ne]
    exact hr
  exact le_on_closure (fun s hs => (h04.1.referencePositive m hm s hs).le)
    continuousOn_const hc.continuousOn hrcl

/-- Every original physical RadialTest has a smooth actual corrected
differential expression at every point of a positive closed piece. -/
theorem n06_positive_current_test_contDiffOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    ContDiffOn ℝ ∞ (divergenceOperator (L.coefficients z) φ)
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ (univ : Set ℝ)) := by
  intro p hp
  by_cases hpa : p ∈ annularOpen D
  · have hc := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03 hz hs hpa
      (n06_positivePiece_closed_slope_nonneg h01 h04 m hm hp.1)
    exact (n06_contDiffAt_divergenceOperator hc.1 hc.2.1 hc.2.2
      hφ.1.contDiffAt).contDiffWithinAt
  · obtain ⟨J, hJ, hJcore, hzero⟩ := hφ.2.2
    have hpJ : p.1 ∉ J := fun h => hpa ⟨hJcore h, mem_univ _⟩
    have he : φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
      filter_upwards [(continuous_fst.tendsto p).eventually
        (hJ.isClosed.isOpen_compl.mem_nhds hpJ)] with q hq
      exact hzero q.1 hq q.2
    have hc : ContDiffAt ℝ ∞ (0 : PolarPoint → ℝ) p := contDiffAt_const
    exact (hc.congr_of_eventuallyEq
      (n06_divergenceOperator_eventually_zero (L.coefficients z) he)).contDiffWithinAt

/-- The actual height-side distribution test on a positive piece is in
the original canonical L2 space. Its coefficients are the same current
N03 coefficients, with all regularity derived above. -/
theorem n06_positive_current_operatorTest_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    MemLp (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ))
      2 (canonicalMeasure S K m) := by
  apply n06_current_canonicalSource_memLp h04 hz hs m
  have hΩ := n06_positivePhysicalPiece_eq_reference h04.1 hz hs m hm
  rw [n06_physicalPieceClosed_eq_reference_rectangle h04.1 m hΩ]
  exact (n06_positive_current_test_contDiffOn hT hS h01 h03 h04 hz hs m hm hφ).continuousOn

end ContinuousFlexibility.Statements
