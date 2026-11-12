import ContinuousFlexibility.Analysis.N06NegativeCurrentTestLp
import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity

/-!
# Shifted actual operator tests for the original full angular period

The chart and height equivariance, including the actual Jacobian identity,
commute the source and height transforms with every nonnegative integral
multiple of pi. This does not assert periodicity of the physical operator.
On negative pieces the true normal-form identity is applied at the shifted
canonical point; its potential is bounded there by the same original N04
bound. These facts give L2 tests for both halves of a full-period physical
pairing, and more generally for every integral angular shift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem transform_nat_angular_shift
    {l r τ : ℝ} (A : (PolarPoint → ℝ) → PolarPoint → ℝ)
    (hA : ∀ f : PolarPoint → ℝ, ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      A (fun q => f (q + (0, τ))) p = A f (p + (0, τ)))
    (f : PolarPoint → ℝ) (j : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    A (fun q => f (q + (0, (j : ℝ) * τ))) p = A f (p + (0, (j : ℝ) * τ)) := by
  induction j generalizing f p with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    change A (fun q => f (q + (0 : PolarPoint))) p = A f (p + (0 : PolarPoint))
    simp only [add_zero]
  | succ j ih =>
    have hshift : ((0, ((j + 1 : ℕ) : ℝ) * τ) : PolarPoint) =
        (0, (j : ℝ) * τ) + (0, τ) := by
      ext <;> simp [Nat.cast_add, add_mul]
    have hpj : p + (0, (j : ℝ) * τ) ∈ Ioo l r ×ˢ (univ : Set ℝ) :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    calc
      _ = A (fun q => (fun t => f (t + (0, τ))) (q + (0, (j : ℝ) * τ))) p := by
        congr 1
        funext q
        rw [hshift]
        exact congrArg f (add_assoc q (0, (j : ℝ) * τ) (0, τ)).symm
      _ = A (fun q => f (q + (0, τ))) (p + (0, (j : ℝ) * τ)) :=
        ih (fun t : PolarPoint => f (t + (0, τ))) hp
      _ = A f ((p + (0, (j : ℝ) * τ)) + (0, τ)) := hA _ _ hpj
      _ = _ := by rw [hshift, add_assoc]

theorem n06_radialPartial_comp_add (f : PolarPoint → ℝ) (v : PolarPoint) :
    radialPartial (fun q => f (q + v)) = fun q => radialPartial f (q + v) := by
  funext q
  exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (fderiv_comp_add_right v)

theorem n06_angularPartial_comp_add (f : PolarPoint → ℝ) (v : PolarPoint) :
    angularPartial (fun q => f (q + v)) = fun q => angularPartial f (q + v) := by
  funext q
  exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) (fderiv_comp_add_right v)

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

private theorem canonicalTransforms_shift_pi
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (f : PolarPoint → ℝ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m (fun q => f (q + (0, Real.pi))) p =
      canonicalHeight S K z m f (p + (0, Real.pi)) ∧
    canonicalSource S K z m (fun q => f (q + (0, Real.pi))) p =
      canonicalSource S K z m f (p + (0, Real.pi)) := by
  have hc := h04.1.charts z hz hs m
  have hx := hc.2.1 hp
  have hG := inverseChart_periodic_of_chart_periodic_on hc.2.1
    (fun q hq => ((h04.1.domains z hz hs m).2.2.2.1 q).mpr hq) hc.2.2.1 hc.2.2.2.1
    (fun q hq => (hc.2.2.2.2.2.2.2 q hq).2.2.1) hp
  have hH := (hc.2.2.2.2.2.2.2 _ hx).2.2.2
  have hJ := n06_planeJacobian_chart_lift_on (h04.1.domains z hz hs m).1 hc.2.2.2.2.1
    (fun q hq => ((h04.1.domains z hz hs m).2.2.2.1 q).mpr hq)
    (fun q hq => (hc.2.2.2.2.2.2.2 q hq).2.2.1) hx
  constructor <;> simp only [canonicalHeight, canonicalSource, hG, hH, hJ]

/-- Height transforms commute with the actual lift; f itself need not
have any angular period. -/
theorem n06_current_canonicalHeight_shift
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (f : PolarPoint → ℝ) (j : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m (fun q => f (q + (0, (j : ℝ) * Real.pi))) p =
      canonicalHeight S K z m f (p + (0, (j : ℝ) * Real.pi)) :=
  transform_nat_angular_shift (canonicalHeight S K z m)
    (fun g _ hq => (canonicalTransforms_shift_pi h04 hz hs m g hq).1) f j hp

/-- The actual source Jacobian has the same lift law, without a
periodicity hypothesis on the source or on the physical operator. -/
theorem n06_current_canonicalSource_shift
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (f : PolarPoint → ℝ) (j : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (fun q => f (q + (0, (j : ℝ) * Real.pi))) p =
      canonicalSource S K z m f (p + (0, (j : ℝ) * Real.pi)) :=
  transform_nat_angular_shift (canonicalSource S K z m)
    (fun g _ hq => (canonicalTransforms_shift_pi h04 hz hs m g hq).2) f j hp

/-- The shifted negative-piece equation keeps the potential evaluated at
the shifted point. No periodicity of that potential is used. -/
theorem n06_negative_current_shifted_operatorTest_eq
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m j : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (fun q =>
        divergenceOperator (L.coefficients z) φ (q + (0, (j : ℝ) * Real.pi))) p =
      radialPartial (radialPartial (canonicalHeight S K z m
        (fun q => φ (q + (0, (j : ℝ) * Real.pi))))) p -
      p.1 * angularPartial (angularPartial (canonicalHeight S K z m
        (fun q => φ (q + (0, (j : ℝ) * Real.pi))))) p +
      K.potential z m (p + (0, (j : ℝ) * Real.pi)) *
        canonicalHeight S K z m (fun q => φ (q + (0, (j : ℝ) * Real.pi))) p := by
  let v : PolarPoint := (0, (j : ℝ) * Real.pi)
  let W := canonicalHeight S K z m φ
  let Wj := canonicalHeight S K z m (fun q => φ (q + v))
  have hpj : p + v ∈ canonicalOpen S K m :=
    ⟨by simpa only [v, Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  have he : (fun q => W (q + v)) =ᶠ[𝓝 p] Wj := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (n06_current_canonicalHeight_shift h04 hz hs m φ j hq).symm
  have hjet (e : PolarPoint) :
      (fun q => fderiv ℝ (fun t => W (t + v)) q e) =ᶠ[𝓝 p]
        fun q => fderiv ℝ Wj q e := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A e) hq
  have hrr : radialPartial (radialPartial W) (p + v) = radialPartial (radialPartial Wj) p := by
    have hh : radialPartial (radialPartial (fun q => W (q + v))) p =
        radialPartial (radialPartial Wj) p :=
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) ((hjet (1, 0)).fderiv_eq (𝕜 := ℝ))
    simpa only [n06_radialPartial_comp_add] using hh
  have htt : angularPartial (angularPartial W) (p + v) = angularPartial (angularPartial Wj) p := by
    have hh : angularPartial (angularPartial (fun q => W (q + v))) p =
        angularPartial (angularPartial Wj) p :=
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) ((hjet (0, 1)).fderiv_eq (𝕜 := ℝ))
    simpa only [n06_angularPartial_comp_add] using hh
  rw [n06_current_canonicalSource_shift h04 hz hs m _ j hp,
    n06_negative_current_operatorTest_eq h04 hz hs m hm hφ hpj]
  change radialPartial (radialPartial W) (p + v) -
      (p + v).1 * angularPartial (angularPartial W) (p + v) +
      K.potential z m (p + v) * W (p + v) = _
  rw [hrr, htt, he.eq_of_nhds]
  simp only [Wj, v, Prod.fst_add, add_zero]

/-- Every integral half-period shift of the actual negative-piece
operator test is L2, without any assumption that the operator is periodic. -/
theorem n06_negative_current_shifted_operatorTest_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m j : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MemLp (canonicalSource S K z m (fun q =>
      divergenceOperator (L.coefficients z) φ (q + (0, (j : ℝ) * Real.pi))))
      2 (canonicalMeasure S K m) := by
  let v : PolarPoint := (0, (j : ℝ) * Real.pi)
  let φj : PolarPoint → ℝ := fun q => φ (q + v)
  let W := canonicalHeight S K z m φj
  have hφj : ContDiff ℝ ∞ φj := hφ.comp (contDiff_id.add contDiff_const)
  have hW : MemLp W 2 (canonicalMeasure S K m) :=
    n06_current_canonicalHeight_memLp h04 hz hs m hφj.continuous.continuousOn
  obtain ⟨hrr, htt⟩ := n06_current_canonicalHeight_second_memLp h04 hz hs m hφj
  obtain ⟨Q, hQ, hV⟩ := n06_actual_canonicalPotential_bounded h04 hz m
  let Y := |K.left m| + |K.right m|
  have hY : 0 ≤ Y := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hrra : MemLp (fun p => |radialPartial (radialPartial W) p|)
      2 (canonicalMeasure S K m) := by simpa only [Real.norm_eq_abs] using hrr.norm
  have htta : MemLp (fun p => |angularPartial (angularPartial W) p|)
      2 (canonicalMeasure S K m) := by simpa only [Real.norm_eq_abs] using htt.norm
  have hWa : MemLp (fun p => |W p|) 2 (canonicalMeasure S K m) := by
    simpa only [Real.norm_eq_abs] using hW.norm
  have hmajor : MemLp (fun p => |radialPartial (radialPartial W) p| +
      Y * |angularPartial (angularPartial W) p| + Q * |W p|)
      2 (canonicalMeasure S K m) := (hrra.add (htta.const_mul Y)).add (hWa.const_mul Q)
  have hmeas : Measurable (fun q => divergenceOperator (L.coefficients z) φ (q + v)) :=
    (n06_divergenceOperator_measurable (L.coefficients z) φ).comp
      (measurable_id.add measurable_const)
  apply hmajor.of_le (n06_current_canonicalSource_aestronglyMeasurable h04 hz hs m hmeas)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hpj : p + v ∈ canonicalOpen S K m :=
    ⟨by simpa only [v, Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
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
  rw [abs_of_nonneg (add_nonneg
    (add_nonneg (abs_nonneg _) (mul_nonneg hY (abs_nonneg _))) (mul_nonneg hQ (abs_nonneg _)))]
  rw [n06_negative_current_shifted_operatorTest_eq h04 hz hs m j hm hφ hpU]
  calc
    _ ≤ |radialPartial (radialPartial W) p| +
        |p.1| * |angularPartial (angularPartial W) p| + |K.potential z m (p + v)| * |W p| := by
      simpa only [abs_mul] using (abs_add_le
        (radialPartial (radialPartial W) p - p.1 * angularPartial (angularPartial W) p)
        (K.potential z m (p + v) * W p)).trans
          (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hy (abs_nonneg _)))
      (mul_le_mul_of_nonneg_right (hV (p + v) hpj) (abs_nonneg _))

/-- Positive-piece regularity was proved for every physical angle, so it
also controls the shifted test on the same original canonical measure. -/
theorem n06_positive_current_shifted_operatorTest_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m j : ℕ) (hm : K.positive m = true)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    MemLp (canonicalSource S K z m (fun q =>
      divergenceOperator (L.coefficients z) φ (q + (0, (j : ℝ) * Real.pi))))
      2 (canonicalMeasure S K m) := by
  apply n06_current_canonicalSource_memLp h04 hz hs m
  have hΩ := n06_positivePhysicalPiece_eq_reference h04.1 hz hs m hm
  rw [n06_physicalPieceClosed_eq_reference_rectangle h04.1 m hΩ]
  have hc := (n06_positive_current_test_contDiffOn hT hS h01 h03 h04 hz hs m hm hφ).continuousOn
  exact hc.comp (continuous_id.add continuous_const).continuousOn
    (fun p hp => ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩)

/-- The actual transformed tests required for all angular tiles belong
to the same original L2 space on both canonical types. In particular j=0
and j=1 suffice for the original full-period weak equation. -/
theorem n06_current_shifted_operatorTest_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m j : ℕ) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    MemLp (canonicalSource S K z m (fun q =>
      divergenceOperator (L.coefficients z) φ (q + (0, (j : ℝ) * Real.pi))))
      2 (canonicalMeasure S K m) := by
  cases hm : K.positive m with
  | false => exact n06_negative_current_shifted_operatorTest_memLp h04 hz hs m j hm hφ.1
  | true => exact n06_positive_current_shifted_operatorTest_memLp hT hS h01 h03 h04 hz hs m j hm hφ

end ContinuousFlexibility.Statements
