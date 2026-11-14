module

public import ContinuousFlexibility.Analysis.N06ReferenceNegativeInverse
public import ContinuousFlexibility.Analysis.N06NegativeReferenceEquation
public import ContinuousFlexibility.Radial.MatchingCutoffTests

/-!
# The actual reciprocal reference height solves the negative scalar ODE

A local radial cutoff turns the reciprocal height into a genuine global
smooth canonical test.  Its physical pullback equals the constant one
near the point under consideration, so its physical divergence is zero.
The original negative normal form then gives `W'' + V W = 0`.

The second-derivative bound extends to the genuine closed inverse germs
by continuity.  The potential bound remains indexed by the actual
`K.cell`; no identification with a physical profile cell is made here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n06_exists_smooth_radial_germ
    {W : ℝ → ℝ} {a b y : ℝ}
    (hW : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t) (hy : y ∈ Ioo a b) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝 y] W := by
  obtain ⟨χ, hχ, _, hsupp, hone⟩ := exists_matching_cutoff hy.1 hy.2
  let F : ℝ → ℝ := fun t => χ t * W t
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : t ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hW t (hsupp ht))
    · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) t).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
      change χ s = 0 at hs
      simp only [F, hs, zero_mul, Pi.zero_apply]
  refine ⟨F, hF, ?_⟩
  filter_upwards [hone] with t ht
  change χ t = 1 at ht
  simp only [F, ht, one_mul]

private theorem n06_negativePrincipal_radial
    {F W : ℝ → ℝ} {y θ : ℝ} (hF : ContDiff ℝ ∞ F)
    (heq : F =ᶠ[𝓝 y] W) :
    n06NegativePrincipalTest (radialHeightField F) (y, θ) = deriv (deriv W) y := by
  have hFr : radialPartial (radialHeightField F) = radialHeightField (deriv F) :=
    funext fun p => radialPartial_radialHeightField (hF.differentiable (by simp) p.1)
  have hFt : angularPartial (radialHeightField F) = fun _ => (0 : ℝ) :=
    funext fun p => angularPartial_radialHeightField (hF.differentiable (by simp) p.1)
  rw [n06NegativePrincipalTest, hFr, hFt, angularPartial_const, mul_zero, sub_zero,
    radialPartial_radialHeightField
      ((contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp) y)]
  exact heq.deriv.deriv_eq

private theorem n06_seminorm_self_difference
    {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (x : E) :
    p (x - x) = 0 := by
  simp only [sub_self, map_zero]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The selected inverse height solves the actual ODE at every angle.
Only the original N04 identity is tested, on a genuinely smooth test. -/
theorem N06ReferenceNegativeInverseData.reciprocalHeight_ode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {y : ℝ} (hy : y ∈ Ioo (K.left i) (K.right i)) (θ : ℝ) :
    deriv (deriv P.reciprocalHeight) y +
      K.potential (C.referenceState, 0) i (y, θ) * P.reciprocalHeight y = 0 := by
  let W : ℝ → ℝ := P.reciprocalHeight
  obtain ⟨F, hF, hFW⟩ := n06_exists_smooth_radial_germ
    (fun t ht => (P.reciprocalHeight_regular hT hS h hi ⟨ht.1.le, ht.2.le⟩).1) hy
  let φ : PolarPoint → ℝ := radialHeightField F
  have hφ : ContDiff ℝ ∞ φ := hF.comp contDiff_fst
  have hp : (y, θ) ∈ canonicalOpen S K i := ⟨hy, mem_univ _⟩
  let x : PolarPoint := K.inverseChart (C.referenceState, 0) i (y, θ)
  have h01 := h.1.1.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hA := (n06_N04_qualitative_parts h.2.2.2.2.1).1
  have hc := hA.charts (C.referenceState, 0) hz hs i
  rw [hA.referenceDomain i] at hc
  have hx : x ∈ referencePhysicalPieceOpen S K i := hc.2.1 hp
  have hxp : K.chart (C.referenceState, 0) i x = (y, θ) := hc.2.2.2.1 _ hp
  have hchart : ContinuousAt (K.chart (C.referenceState, 0) i) x :=
    (hc.2.2.2.2.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)).continuousAt
  have hfirst := congrArg (fun q : PolarPoint => q.1) hxp
  change (K.chart (C.referenceState, 0) i x).1 = y at hfirst
  have hto : Tendsto (fun q => (K.chart (C.referenceState, 0) i q).1)
      (𝓝 x) (𝓝 y) := by
    rw [← hfirst]
    exact hchart.fst
  have hpull : (fun q => K.height (C.referenceState, 0) i q *
      φ (K.chart (C.referenceState, 0) i q)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hx,
      hto.eventually hFW] with q hq hFq
    have hqclosed : q.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
      ⟨hq.1.1.le, hq.1.2.le⟩
    have hshape := n06_reference_negative_radial hT hS h hi q.1 hqclosed q.2
    have hheight : K.height (C.referenceState, 0) i q =
        n06ReferenceNegativeH C K i q.1 := hshape.2
    have hrad : (K.chart (C.referenceState, 0) i q).1 =
        n06ReferenceNegativeY C K i q.1 := by
      have he := congrArg (fun p : PolarPoint => p.1) hshape.1
      exact he
    change K.height (C.referenceState, 0) i q * F ((K.chart (C.referenceState, 0) i q).1) = 1
    rw [hFq]
    change K.height (C.referenceState, 0) i q *
      (n06ReferenceNegativeH C K i (P.inverse ((K.chart (C.referenceState, 0) i q).1)))⁻¹ = 1
    rw [hrad, P.left_inverse _ hqclosed, hheight]
    exact mul_inv_cancel₀
      (n06_reference_negative_height_normalization hT hS h hi hqclosed).2.2.1.ne'
  have hdiv : divergenceOperator (L.coefficients (C.referenceState, 0))
      (fun q => K.height (C.referenceState, 0) i q * φ (K.chart (C.referenceState, 0) i q)) x = 0 :=
    (n05_divergenceOperator_congr _ hpull).trans (divergenceOperator_const _ _ _)
  have hzero : canonicalOperator S K L (C.referenceState, 0) i φ (y, θ) = 0 := by
    simp only [canonicalOperator, canonicalSource, hi, Bool.false_eq_true, ↓reduceIte, one_mul]
    change K.height (C.referenceState, 0) i x *
      divergenceOperator (L.coefficients (C.referenceState, 0))
        (fun q => K.height (C.referenceState, 0) i q * φ (K.chart (C.referenceState, 0) i q)) x /
      |planeJacobian (K.chart (C.referenceState, 0) i) x| = 0
    rw [hdiv, mul_zero, zero_div]
  have he := n06_negative_canonicalOperator h.2.2.2.2.1 hz hs i hi hφ hp
  have hprincipal := n06_negativePrincipal_radial (θ := θ) hF hFW
  have hvalue : φ (y, θ) = P.reciprocalHeight y := hFW.eq_of_nhds
  rw [hzero, hprincipal, hvalue] at he
  exact he.symm

/-- Since the true reciprocal height is positive and radial, the actual
reference potential is radial as a consequence of the ODE. -/
theorem N06ReferenceNegativeInverseData.potential_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {y : ℝ} (hy : y ∈ Ioo (K.left i) (K.right i)) (θ : ℝ) :
    K.potential (C.referenceState, 0) i (y, θ) =
      -deriv (deriv P.reciprocalHeight) y / P.reciprocalHeight y := by
  apply (eq_div_iff
    (P.reciprocalHeight_regular hT hS h hi ⟨hy.1.le, hy.2.le⟩).2.ne').mpr
  linarith only [P.reciprocalHeight_ode hT hS h hi hy θ]

/-- A genuine relative second-derivative estimate on the open interval
extends to the constructed closed germs, without assigning endpoint
values to the original potential. -/
theorem N06ReferenceNegativeInverseData.secondDerivative_bound_closed
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i) {M : ℝ}
    (hV : ∀ y ∈ Ioo (K.left i) (K.right i),
      |K.potential (C.referenceState, 0) i (y, 0)| ≤ M)
    {y : ℝ} (hy : y ∈ Icc (K.left i) (K.right i)) :
    |deriv (deriv P.reciprocalHeight) y| ≤ M * P.reciprocalHeight y := by
  have hreg := P.reciprocalHeight_regular hT hS h hi hy
  have hW₂ : ContDiffAt ℝ ∞ (deriv (deriv P.reciprocalHeight)) y :=
    (hreg.1.derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)
  have hclosure : y ∈ closure (Ioo (K.left i) (K.right i)) := by
    rw [closure_Ioo (h.2.2.2.2.1.1.referenceBounds i).2.1.ne]
    exact hy
  haveI : NeBot (𝓝[Ioo (K.left i) (K.right i)] y) :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosure
  apply le_of_tendsto_of_tendsto (b := 𝓝[Ioo (K.left i) (K.right i)] y)
    (hW₂.continuousAt.abs.mono_left nhdsWithin_le_nhds)
    ((continuousAt_const.mul hreg.1.continuousAt).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos := (P.reciprocalHeight_regular hT hS h hi ⟨ht.1.le, ht.2.le⟩).2
  have he : deriv (deriv P.reciprocalHeight) t =
      -(K.potential (C.referenceState, 0) i (t, 0) * P.reciprocalHeight t) := by
    linarith only [P.reciprocalHeight_ode hT hS h hi ht 0]
  rw [he, abs_neg, abs_mul, abs_of_pos htpos]
  exact mul_le_mul_of_nonneg_right (hV t ht) htpos.le

/-- The constant in the closed ODE estimate is supplied by the original
N04 zero-order bound and uses its actual canonical cell label. -/
theorem n06_referenceNegative_reciprocalHeight_secondDerivative_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, K.positive i = false →
      ∀ P : N06ReferenceNegativeInverseData C K i,
      ∀ y ∈ Icc (K.left i) (K.right i),
        |deriv (deriv P.reciprocalHeight) y| ≤
          (M * T.E0 (T.sample (K.cell i)) ^ M) * P.reciprocalHeight y := by
  have h01 := h.1.1.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hbounds := h.2.2.2.2.1.2.2.1
  obtain ⟨M, hM, hbound⟩ := hbounds 0
  refine ⟨M, hM, fun i hi P y hy => P.secondDerivative_bound_closed hT hS h hi ?_ hy⟩
  intro t ht
  have hb := hbound (C.referenceState, 0) hz i (t, 0) ⟨ht, mem_univ _⟩ 0 0 (by omega)
  have hgrading : stateGrading S (0 + loss) (C.referenceState - C.referenceState) = 0 :=
    n06_seminorm_self_difference (stateGrading S (0 + loss)) C.referenceState
  rw [hgrading] at hb
  simp only [mixedDerivative, iteratedDeriv_zero,
    abs_zero, zero_add, add_zero, mul_one] at hb
  linarith only [hb, abs_nonneg ((K.dividedDifference (C.referenceState, 0) i).a (t, 0)),
    abs_nonneg ((K.dividedDifference (C.referenceState, 0) i).b (t, 0)),
    abs_nonneg ((K.dividedDifference (C.referenceState, 0) i).c (t, 0))]

end ContinuousFlexibility.Statements
