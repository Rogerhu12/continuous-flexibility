import ContinuousFlexibility.Analysis.N06NegativeCurrentTestLp
import ContinuousFlexibility.Analysis.N06PositiveCanonicalDifference
import ContinuousFlexibility.Analysis.N06RadialCanonicalOperator
import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities

/-!
# The actual positive operator on current physical tests

The N04 identity is applied to a smooth representative of the true current
height transform near each interior point. Consequently the source of the
actual physical operator is identified without regularity assumptions on
its bare coefficients or on the inverse chart at the boundary.

The original cubic factorization then separates the radial reference test
operator, the cubic divergence, and the actual potential difference. Only
the divided coefficients need local differentiability in this intermediate
identity; current principal differentiability follows from the same cubic
germs and the reference coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The radial divergence identity needs only the actual second-order
test germ, not a global extension of the current height transform. -/
theorem n06_divergence_radial_coefficients_germ_at
    {A : SymmetricCoefficients} {a c : ℝ → ℝ}
    {φ : PolarPoint → ℝ} {p : PolarPoint}
    (ha : A.a =ᶠ[𝓝 p] fun q => a q.1)
    (hb : A.b =ᶠ[𝓝 p] fun _ => 0)
    (hc : A.c =ᶠ[𝓝 p] fun q => c q.1)
    (hcd : DifferentiableAt ℝ c p.1) (hφ : ContDiffAt ℝ 2 φ p) :
    divergenceOperator A φ p =
      radialPartial (fun q => a q.1 * radialPartial φ q) p +
        c p.1 * angularPartial (angularPartial φ) p := by
  let A0 : SymmetricCoefficients := ⟨fun q => a q.1, fun _ => 0, fun q => c q.1⟩
  have he : divergenceOperator A φ p = divergenceOperator A0 φ p :=
    n06_divergenceOperator_congr_germ φ ha hb hc
  have hcf : DifferentiableAt ℝ (fun q : PolarPoint => c q.1) p :=
    hcd.comp p differentiableAt_fst
  have hφθ : DifferentiableAt ℝ (angularPartial φ) p :=
    (contDiffAt_angularPartial hφ (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hprod := angularPartial_mul hcf hφθ
  have hct : angularPartial (fun q : PolarPoint => c q.1) p = 0 :=
    angularPartial_radialHeightField hcd
  rw [he]
  simp only [A0, divergenceOperator, zero_mul, add_zero, zero_add]
  rw [hprod, hct, zero_mul, zero_add]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- N04's actual operator identity holds on the true current height of
every smooth physical test, with its original type sign. -/
theorem n06_current_source_operatorTest_eq
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p =
      divergenceOperator (K.coefficients z m) (canonicalHeight S K z m φ) p +
        (if K.positive m then -1 else (1 : ℝ)) *
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
  have hnear : ∀ᶠ q in 𝓝 x, g (K.chart z m q) = W (K.chart z m q) :=
    (hFx ▸ hF.tendsto).eventually hgW
  have hphys : φ =ᶠ[𝓝 x] (fun q => K.height z m q * g (K.chart z m q)) := by
    filter_upwards [(hA.domains z hz hs m).1.mem_nhds hx, hnear] with q hq hqg
    rw [hqg]
    change φ q = K.height z m q * (φ (K.inverseChart z m (K.chart z m q)) /
      K.height z m (K.inverseChart z m (K.chart z m q)))
    rw [hc.2.2.1 q hq]
    field_simp [(hc.2.2.2.2.2.2.2 q hq).1.ne'] <;> ring
  have hop := hB.2.2.1 z hz hs m g hg p hp
  have hsource : canonicalSource S K z m (divergenceOperator (L.coefficients z)
      (fun q => K.height z m q * g (K.chart z m q))) p =
        divergenceOperator (K.coefficients z m) g p +
          (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p * g p := by
    dsimp only [canonicalOperator] at hop
    cases hm : K.positive m <;>
      simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hop ⊢ <;>
      linarith only [hop]
  calc
    _ = canonicalSource S K z m (divergenceOperator (L.coefficients z)
        (fun q => K.height z m q * g (K.chart z m q))) p := by
      change K.height z m x * divergenceOperator (L.coefficients z) φ x /
          |planeJacobian (K.chart z m) x| =
        K.height z m x * divergenceOperator (L.coefficients z)
          (fun q => K.height z m q * g (K.chart z m q)) x / |planeJacobian (K.chart z m) x|
      exact congrArg (fun t : ℝ => K.height z m x * t / |planeJacobian (K.chart z m) x|)
        (n06_divergenceOperator_input_congr_germ (L.coefficients z) hphys)
    _ = _ := by
      rw [hsource, n06_divergenceOperator_input_congr_germ (K.coefficients z m) hgW,
        hgW.eq_of_nhds]

/-- Constant canonical tests identify a measurable actual potential on
every piece. No physical coefficient regularity is needed for this fact. -/
theorem n06_actualPotential_aestronglyMeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    AEStronglyMeasurable (K.potential z m) (canonicalMeasure S K m) := by
  have hf := n06_current_canonicalSource_aestronglyMeasurable h04 hz hs m
    (n06_divergenceOperator_measurable (L.coefficients z) (K.height z m))
  apply (hf.const_mul (if K.positive m then -1 else (1 : ℝ))).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact (canonicalPotential_eq_source_height (n06_N04_qualitative_parts h04).2
    hz hs m ⟨hp.1, mem_univ _⟩).symm

/-- The true order-zero N04 bound makes the actual potential a multiplier
on the unchanged canonical L2 piece, for both canonical types. -/
theorem n06_actualPotential_mul_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {U : PolarPoint → ℝ} (hU : MemLp U 2 (canonicalMeasure S K m)) :
    MemLp (fun p => K.potential z m p * U p) 2 (canonicalMeasure S K m) := by
  obtain ⟨Q, hQ, hbound⟩ := n06_actual_canonicalPotential_bounded h04 hz m
  apply (hU.const_mul Q).of_le
    ((n06_actualPotential_aestronglyMeasurable h04 hz hs m).mul hU.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hQ]
  exact mul_le_mul_of_nonneg_right (hbound p ⟨hp.1, mem_univ _⟩) (abs_nonneg _)

/-- The actual positive source of a physical test differs from the
negative reference test operator by positive cubic divergence and
negative potential difference. Every coefficient in this identity is
the original selected N04 coefficient. -/
theorem n06_positive_current_operatorTest_difference
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true) (hl : K.left m = 0) (hr : K.right m = 1)
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
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
    (hcd : DifferentiableAt ℝ c p.1)
    (hA : DifferentiableAt ℝ (K.dividedDifference z m).a p)
    (hB : DifferentiableAt ℝ (K.dividedDifference z m).b p)
    (hCc : DifferentiableAt ℝ (K.dividedDifference z m).c p) :
    canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p =
      -n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p +
        divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1)
          (K.dividedDifference z m).a (K.dividedDifference z m).b
          (K.dividedDifference z m).c) (canonicalHeight S K z m φ) p -
        (K.potential z m p - K.potential (C.referenceState, 0) m p) *
          canonicalHeight S K z m φ p := by
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
    ((n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).of_le (by simp)
  have hd : DifferentiableAt ℝ (fun q : PolarPoint => cylinderWeight q.1) p :=
    differentiableAt_fst.mul ((differentiableAt_const (1 : ℝ)).sub differentiableAt_fst)
  have hcur := n06_current_source_operatorTest_eq h04 hz hs hφ hp
  have href := n06_divergence_radial_coefficients_germ_at hga hgb hgc hcd hW
  have hcubic := h04.2.1.2.2.2.2
  have hg : ∀ᶠ q : PolarPoint in 𝓝 p,
      (K.coefficients z m).a q - (K.coefficients (C.referenceState, 0) m).a q =
        cylinderWeight q.1 ^ 3 * (K.dividedDifference z m).a q ∧
      (K.coefficients z m).b q - (K.coefficients (C.referenceState, 0) m).b q =
        cylinderWeight q.1 ^ 3 * (K.dividedDifference z m).b q ∧
      (K.coefficients z m).c q - (K.coefficients (C.referenceState, 0) m).c q =
        cylinderWeight q.1 ^ 3 * (K.dividedDifference z m).c q := by
    filter_upwards [hnear] with q hq
    simpa only [hl, hr, sub_zero, cylinderWeight] using hcubic z hz hs m hm q hq
  have hdiff := n06_divergenceDifference_eq_cubic_of_germ hda hdb hdc hd hA hB hCc hW
    (hg.mono fun _ h => h.1) (hg.mono fun _ h => h.2.1) (hg.mono fun _ h => h.2.2)
  rw [href] at hdiff
  rw [hcur, heV hp]
  simp only [hm, ↓reduceIte, neg_one_mul, n06UnitReferenceTestOperator]
  linear_combination hdiff

end ContinuousFlexibility.Statements
