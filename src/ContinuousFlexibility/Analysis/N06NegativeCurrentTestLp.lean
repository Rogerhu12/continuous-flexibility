module

public import ContinuousFlexibility.Analysis.N06CurrentInverseTestJets
public import ContinuousFlexibility.Analysis.N06PositiveCurrentTestLp
public import ContinuousFlexibility.Analysis.N06CubicDifferential
public import ContinuousFlexibility.Radial.MatchingCutoffTests
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Actual current operator tests on negative pieces

The N04 operator identity applies to global smooth canonical fields. A
radial cutoff equal to one near the point applies it to the actual local
height transform of any smooth physical test. The negative normal form
then expresses its source transform as W_yy - y W_theta_theta + V W.
The genuine inverse test jets are L2, and the original order-zero N04
bound controls V. Measurability of the totalized actual Frechet derivative
supplies measurability of the physical differential expression without a
regularity premise on the corrected coefficient fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

/-- An actual smooth function on an open strip has a global smooth
representative of its germ at any interior point. Angular symmetry and
periodicity are not needed for this local extension. -/
theorem n06_exists_smooth_strip_germ {l r : ℝ} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ univ))
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    ∃ g : PolarPoint → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] f := by
  obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
    exists_matching_interval_cutoff hp.1.1 (le_refl p.1) hp.1.2
  refine ⟨fun q => χ q.1 * f q, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hqt : q.1 ∈ tsupport χ
    · exact (hχ.comp contDiff_fst).contDiffAt.mul
        (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
          ⟨hχs hqt, mem_univ q.2⟩))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [(continuous_fst.tendsto q).eventually
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hqt)] with t ht
      change χ t.1 * f t = 0
      rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  · filter_upwards [(continuous_fst.tendsto p).eventually
      (hχone p.1 ⟨le_rfl, le_rfl⟩)] with q hq
    change χ q.1 = 1 at hq
    change χ q.1 * f q = f q
    rw [hq, one_mul]

/-- The actual totalized Frechet derivative is Borel measurable even
before any regularity of its input is known. This applies separately to
the two genuine fluxes in the divergence definition. -/
theorem n06_divergenceOperator_measurable (A : SymmetricCoefficients)
    (φ : PolarPoint → ℝ) : Measurable (divergenceOperator A φ) := by
  exact (measurable_fderiv_apply_const ℝ
      (fun q => A.a q * radialPartial φ q + A.b q * angularPartial φ q) (1, 0)).add
    (measurable_fderiv_apply_const ℝ
      (fun q => A.b q * radialPartial φ q + A.c q * angularPartial φ q) (0, 1))

private theorem negative_normalForm_divergence
    {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) (p : PolarPoint) :
    divergenceOperator ⟨fun _ => 1, fun _ => 0, fun q => -q.1⟩ g p =
      radialPartial (radialPartial g) p - p.1 * angularPartial (angularPartial g) p := by
  have hC : ContDiff ℝ ∞ (fun q : PolarPoint => -q.1) := contDiff_fst.neg
  have hCθ : angularPartial (fun q : PolarPoint => -q.1) p = 0 := by
    have hd : HasFDerivAt (fun q : PolarPoint => -q.1)
        (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) p := hasFDerivAt_fst.neg
    simp only [angularPartial, hd.fderiv]
    change -(0 : ℝ) = 0
    exact neg_zero
  rw [divergenceOperator_expansion contDiff_const contDiff_const hC hg]
  simp only [radialPartial_const, angularPartial_const, hCθ, zero_mul, mul_zero,
    one_mul, zero_add, add_zero, neg_mul, sub_eq_add_neg]

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

/-- The actual height transform is smooth on the recorded open domain
of the current inverse chart. -/
theorem n06_current_canonicalHeight_contDiffOn
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞ (canonicalHeight S K z m φ) (canonicalOpen S K m) := by
  have hc := h04.1.charts z hz hs m
  have hdiv : ContDiffOn ℝ ∞ (fun x => φ x / K.height z m x)
      (physicalPieceOpen S K z m) :=
    hφ.contDiffOn.div hc.2.2.2.2.2.2.1
      (fun x hx => (hc.2.2.2.2.2.2.2 x hx).1.ne')
  exact hdiv.comp hc.2.2.2.2.2.1 hc.2.1

/-- Measurable physical data have an almost everywhere measurable source
transform under the genuine current inverse chart. -/
theorem n06_current_canonicalSource_aestronglyMeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : Measurable f) :
    AEStronglyMeasurable (canonicalSource S K z m f) (canonicalMeasure S K m) := by
  have hc := h04.1.charts z hz hs m
  let Q : Set PolarPoint := physicalPieceClosed S K z m
  let U : Set PolarPoint := Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  have hsub : U ⊆ canonicalOpen S K m := fun _ hp => ⟨hp.1, mem_univ _⟩
  have hG : ContinuousOn (K.inverseChart z m) U :=
    hc.2.2.2.2.2.1.continuousOn.mono hsub
  have hGQ : MapsTo (K.inverseChart z m) U Q := by
    intro p hp
    exact subset_closure (hc.2.1 (hsub hp))
  have hw := n06_currentChart_closed_weights h04 hz hs m
  have hH : AEMeasurable (fun p => K.height z m (K.inverseChart z m p))
      (canonicalMeasure S K m) :=
    (hw.1.comp hG hGQ).aemeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
  have hJ : AEMeasurable (fun p => planeJacobian (K.chart z m) (K.inverseChart z m p))
      (canonicalMeasure S K m) :=
    (hw.2.1.comp hG hGQ).aemeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
  have hfG : AEMeasurable (fun p => f (K.inverseChart z m p))
      (canonicalMeasure S K m) :=
    hf.comp_aemeasurable (hG.aemeasurable (measurableSet_Ioo.prod measurableSet_Ioc))
  have hJabs : AEMeasurable (fun p => |planeJacobian (K.chart z m) (K.inverseChart z m p)|)
      (canonicalMeasure S K m) := continuous_abs.measurable.comp_aemeasurable hJ
  exact ((hH.mul hfG).div hJabs).aestronglyMeasurable

/-- The frozen order-zero N04 bound supplies a finite bound on the actual
potential of every fixed piece and state. No continuity of V is assumed. -/
theorem n06_actual_canonicalPotential_bounded
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ p ∈ canonicalOpen S K m, |K.potential z m p| ≤ Q := by
  have hjets := h04.2.2.1
  obtain ⟨B, _, hB⟩ := hjets 0
  let Q := B * T.E0 (T.sample (K.cell m)) ^ B *
    (1 + stateGrading S loss (z.1 - C.referenceState) + |z.2|)
  refine ⟨|Q|, abs_nonneg Q, fun p hp => ?_⟩
  have hb := hB z hz m p hp 0 0 (by norm_num)
  simp only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] at hb
  have hv : |K.potential z m p| ≤ Q := by
    dsimp only [Q]
    linarith only [hb, abs_nonneg ((K.dividedDifference z m).a p),
      abs_nonneg ((K.dividedDifference z m).b p), abs_nonneg ((K.dividedDifference z m).c p)]
  exact hv.trans (le_abs_self Q)

/-- The actual physical operator, transported by its current source
formula, is the negative normal form on the actual height test. The
application of N04 uses a global smooth representative of the local germ. -/
theorem n06_negative_current_operatorTest_eq
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p =
      radialPartial (radialPartial (canonicalHeight S K z m φ)) p -
        p.1 * angularPartial (angularPartial (canonicalHeight S K z m φ)) p +
        K.potential z m p * canonicalHeight S K z m φ p := by
  let W := canonicalHeight S K z m φ
  have hW := n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ
  obtain ⟨g, hg, hgW⟩ := n06_exists_smooth_strip_germ hW hp
  have hA := (n06_N04_qualitative_parts h04).1
  have hB := (n06_N04_qualitative_parts h04).2
  have hc := hA.charts z hz hs m
  let x := K.inverseChart z m p
  have hx : x ∈ physicalPieceOpen S K z m := hc.2.1 hp
  have hFx : K.chart z m x = p := hc.2.2.2.1 p hp
  have hF : ContinuousAt (K.chart z m) x :=
    hc.2.2.2.2.1.continuousOn.continuousAt ((hA.domains z hz hs m).1.mem_nhds hx)
  have hnear : ∀ᶠ q in 𝓝 x, g (K.chart z m q) = W (K.chart z m q) := by
    exact (hFx ▸ hF.tendsto).eventually hgW
  have hphys : φ =ᶠ[𝓝 x] (fun q => K.height z m q * g (K.chart z m q)) := by
    filter_upwards [(hA.domains z hz hs m).1.mem_nhds hx, hnear] with q hq hqg
    rw [hqg]
    change φ q = K.height z m q * (φ (K.inverseChart z m (K.chart z m q)) /
      K.height z m (K.inverseChart z m (K.chart z m q)))
    rw [hc.2.2.1 q hq]
    field_simp [(hc.2.2.2.2.2.2.2 q hq).1.ne'] <;> ring
  have hop := hB.2.2.1 z hz hs m g hg p hp
  simp only [canonicalOperator, hm, Bool.false_eq_true, ↓reduceIte, one_mul] at hop
  have hn : ∀ᶠ q in 𝓝 p,
      (K.coefficients z m).a q = 1 ∧ (K.coefficients z m).b q = 0 ∧
        (K.coefficients z m).c q = -q.1 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hB.2.2.2.1 z hz hs m hm q hq
  have hnormal := n06_divergenceOperator_congr_germ g
    (L' := ⟨fun _ => 1, fun _ => 0, fun q => -q.1⟩)
    (hn.mono fun _ h => h.1) (hn.mono fun _ h => h.2.1) (hn.mono fun _ h => h.2.2)
  have hjet (v : PolarPoint) : (fun q => fderiv ℝ g q v) =ᶠ[𝓝 p]
      fun q => fderiv ℝ W q v := by
    filter_upwards [hgW.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A v) hq
  have hrr : radialPartial (radialPartial g) p = radialPartial (radialPartial W) p :=
    congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) ((hjet (1, 0)).fderiv_eq (𝕜 := ℝ))
  have htt : angularPartial (angularPartial g) p = angularPartial (angularPartial W) p :=
    congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) ((hjet (0, 1)).fderiv_eq (𝕜 := ℝ))
  calc
    _ = canonicalSource S K z m (divergenceOperator (L.coefficients z)
        (fun q => K.height z m q * g (K.chart z m q))) p := by
      change K.height z m x * divergenceOperator (L.coefficients z) φ x /
          |planeJacobian (K.chart z m) x| =
        K.height z m x * divergenceOperator (L.coefficients z)
          (fun q => K.height z m q * g (K.chart z m q)) x / |planeJacobian (K.chart z m) x|
      exact congrArg (fun c : ℝ => K.height z m x * c / |planeJacobian (K.chart z m) x|)
        (n06_divergenceOperator_input_congr_germ (L.coefficients z) hphys)
    _ = divergenceOperator (K.coefficients z m) g p + K.potential z m p * g p := hop
    _ = _ := by
      rw [hnormal, negative_normalForm_divergence hg p, hrr, htt, hgW.eq_of_nhds]

/-- The genuine negative-piece operator test belongs to the original L2
space for every smooth physical test, with no parity or endpoint condition. -/
theorem n06_negative_current_operatorTest_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MemLp (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ))
      2 (canonicalMeasure S K m) := by
  let W := canonicalHeight S K z m φ
  have hW : MemLp W 2 (canonicalMeasure S K m) :=
    n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  obtain ⟨hrr, htt⟩ := n06_current_canonicalHeight_second_memLp h04 hz hs m hφ
  obtain ⟨Q, hQ, hV⟩ := n06_actual_canonicalPotential_bounded h04 hz m
  let Y := |K.left m| + |K.right m|
  have hY : 0 ≤ Y := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnormrr : MemLp (fun p => |radialPartial (radialPartial W) p|)
      2 (canonicalMeasure S K m) := by simpa only [Real.norm_eq_abs] using hrr.norm
  have hnormtt : MemLp (fun p => |angularPartial (angularPartial W) p|)
      2 (canonicalMeasure S K m) := by simpa only [Real.norm_eq_abs] using htt.norm
  have hnormW : MemLp (fun p => |W p|) 2 (canonicalMeasure S K m) := by
    simpa only [Real.norm_eq_abs] using hW.norm
  have hmajor : MemLp (fun p => |radialPartial (radialPartial W) p| +
      Y * |angularPartial (angularPartial W) p| + Q * |W p|)
      2 (canonicalMeasure S K m) := (hnormrr.add (hnormtt.const_mul Y)).add (hnormW.const_mul Q)
  apply hmajor.of_le (n06_current_canonicalSource_aestronglyMeasurable h04 hz hs m
    (n06_divergenceOperator_measurable (L.coefficients z) φ))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hy : |p.1| ≤ Y := by
    apply abs_le.mpr
    constructor
    · have hl := neg_abs_le (K.left m)
      have hr := abs_nonneg (K.right m)
      dsimp only [Y]
      linarith only [hp.1.1, hl, hr]
    · have hl := abs_nonneg (K.left m)
      have hr := le_abs_self (K.right m)
      dsimp only [Y]
      linarith only [hp.1.2, hl, hr]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg
    (add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hY (abs_nonneg _)))
      (mul_nonneg hQ (abs_nonneg _)))]
  rw [n06_negative_current_operatorTest_eq h04 hz hs m hm hφ hpU]
  calc
    _ ≤ |radialPartial (radialPartial W) p| +
        |p.1| * |angularPartial (angularPartial W) p| + |K.potential z m p| * |W p| := by
      simpa only [abs_mul] using (abs_add_le
        (radialPartial (radialPartial W) p - p.1 * angularPartial (angularPartial W) p)
        (K.potential z m p * W p)).trans
          (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hy (abs_nonneg _)))
      (mul_le_mul_of_nonneg_right (hV p hpU) (abs_nonneg _))

/-- Every original RadialTest supplies an actual current operator test
in the same canonical L2 space, on both kinds of pieces. -/
theorem n06_current_operatorTest_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    MemLp (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ))
      2 (canonicalMeasure S K m) := by
  cases hm : K.positive m with
  | false => exact n06_negative_current_operatorTest_memLp h04 hz hs m hm hφ.1
  | true => exact n06_positive_current_operatorTest_memLp hT hS h01 h03 h04 hz hs m hm hφ

end ContinuousFlexibility.Statements
