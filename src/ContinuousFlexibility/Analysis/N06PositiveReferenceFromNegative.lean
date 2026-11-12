import ContinuousFlexibility.Analysis.N06ReferenceNegativeHeight
import ContinuousFlexibility.Analysis.N06BoundaryRadialOrientation
import ContinuousFlexibility.Analysis.PositiveReferenceInterpolation
import ContinuousFlexibility.Analysis.BoundaryTaylorExtension

/-!
# A positive reference coordinate from its actual negative neighbours

The two endpoint inputs are extracted from the selected negative reference
charts.  Their slopes have the correct signs because the actual charts map
their reference intervals into the positive Tricomi interval.  An interface
with a positive piece is a genuine profile root, so its collar can avoid the
closed support of chi.

Only pointwise infinite differentiability is part of the closed-chart
contract.  We therefore use the actual finite Taylor data, rather than
assuming a common smooth extension of the old chart across a root.  The
constructed global diffeomorphism matches coordinate jets through order four
and logarithmic-height jets through order three.  The four local interpolation
functions are concrete polynomials (and exponentials of polynomials), not
additional geometry inputs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The polynomial determined by the actual finite jet at one endpoint. -/
def n06ReferenceEndpointTaylor (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  boundaryTaylorPolynomial n c (fun j _ => iteratedDeriv j f c) (x, 0)

theorem contDiff_n06ReferenceEndpointTaylor (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    ContDiff ℝ ∞ (n06ReferenceEndpointTaylor n c f) :=
  (contDiff_boundaryTaylorPolynomial (fun _ _ => contDiff_const) c).comp
    (contDiff_id.prodMk contDiff_const)

theorem iteratedDeriv_n06ReferenceEndpointTaylor (n : ℕ) (c : ℝ) (f : ℝ → ℝ)
    {k : ℕ} (hk : k ≤ n) :
    iteratedDeriv k (n06ReferenceEndpointTaylor n c f) c = iteratedDeriv k f c :=
  iteratedDeriv_boundaryTaylorPolynomial n c
    (fun j _ => iteratedDeriv j f c) hk 0

theorem n06ReferenceEndpointTaylor_value (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    n06ReferenceEndpointTaylor n c f c = f c := by
  simpa only [iteratedDeriv_zero] using
    iteratedDeriv_n06ReferenceEndpointTaylor n c f (k := 0) (Nat.zero_le n)

theorem deriv_n06ReferenceEndpointTaylor (n : ℕ) (c : ℝ) (f : ℝ → ℝ)
    (hn : 1 ≤ n) :
    deriv (n06ReferenceEndpointTaylor n c f) c = deriv f c := by
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_n06ReferenceEndpointTaylor n c f (k := 1) hn

/-- The actual finite endpoint jets, positive first slopes, and positive
endpoint heights determine a smooth positive interpolation.  No smooth
neighbourhood of the original endpoint functions is assumed. -/
theorem n06_positiveReference_from_finite_endpoint_jets
    {F : Set ℝ} (hF : IsClosed F) {l r η : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r) (hη : 0 < η)
    {yL yR hL hR : ℝ → ℝ}
    (hvL : yL l = 0) (hvR : yR r = 1)
    (hdL : 0 < deriv yL l) (hdR : 0 < deriv yR r)
    (hpL : 0 < hL l) (hpR : 0 < hR r) :
    ∃ δ : ℝ, ∃ Y H : ℝ → ℝ,
      0 < δ ∧ δ < η ∧ 2 * δ < r - l ∧
      Disjoint (Metric.ball l δ) F ∧ Disjoint (Metric.ball r δ) F ∧
      ContDiff ℝ ∞ Y ∧ (∀ x, 0 < deriv Y x) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ x, B ≤ deriv Y x) ∧
      Function.Bijective Y ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
      Y '' Ioo l r = Ioo 0 1 ∧ Y l = 0 ∧ Y r = 1 ∧
      ContDiff ℝ ∞ H ∧ (∀ x, 0 < H x) ∧ (∀ x ∈ F, H x = 1) ∧
      H l = hL l ∧ H r = hR r ∧
      ∀ side : Bool,
        (∀ k : ℕ, k ≤ 4 →
          iteratedDeriv k Y (if side then r else l) =
            iteratedDeriv k (if side then yR else yL) (if side then r else l)) ∧
        (∀ k : ℕ, k ≤ 3 →
          iteratedDeriv k (fun x => Real.log (H x)) (if side then r else l) =
            iteratedDeriv k (fun x => Real.log ((if side then hR else hL) x))
              (if side then r else l)) := by
  let yL' := n06ReferenceEndpointTaylor 4 l yL
  let yR' := n06ReferenceEndpointTaylor 4 r yR
  let hL' : ℝ → ℝ := fun x =>
    Real.exp (n06ReferenceEndpointTaylor 3 l (fun t => Real.log (hL t)) x)
  let hR' : ℝ → ℝ := fun x =>
    Real.exp (n06ReferenceEndpointTaylor 3 r (fun t => Real.log (hR t)) x)
  have hyL' : ContDiff ℝ ∞ yL' := contDiff_n06ReferenceEndpointTaylor 4 l yL
  have hyR' : ContDiff ℝ ∞ yR' := contDiff_n06ReferenceEndpointTaylor 4 r yR
  have hhL' : ContDiff ℝ ∞ hL' :=
    (contDiff_n06ReferenceEndpointTaylor 3 l (fun t => Real.log (hL t))).exp
  have hhR' : ContDiff ℝ ∞ hR' :=
    (contDiff_n06ReferenceEndpointTaylor 3 r (fun t => Real.log (hR t))).exp
  have hvL' : yL' l = 0 := (n06ReferenceEndpointTaylor_value 4 l yL).trans hvL
  have hvR' : yR' r = 1 := (n06ReferenceEndpointTaylor_value 4 r yR).trans hvR
  have hdL' : 0 < deriv yL' l := by
    rw [show deriv yL' l = deriv yL l from
      deriv_n06ReferenceEndpointTaylor 4 l yL (by norm_num)]
    exact hdL
  have hdR' : 0 < deriv yR' r := by
    rw [show deriv yR' r = deriv yR r from
      deriv_n06ReferenceEndpointTaylor 4 r yR (by norm_num)]
    exact hdR
  obtain ⟨δ, hδ, _, hδη, hgap, havoidL, havoidR, hresult⟩ :=
    exists_positiveReferenceInterpolation hF hl hr hlr hη
      (ρL := 1) (ρR := 1) zero_lt_one zero_lt_one
      (fun _ _ => hyL'.contDiffAt) (fun _ _ => hyR'.contDiffAt)
      (fun _ _ => hhL'.contDiffAt) (fun _ _ => hhR'.contDiffAt)
      hvL' hvR' hdL' hdR' (Real.exp_pos _) (Real.exp_pos _)
  let Y := positiveReferenceCoordinate l r δ (deriv yL') (deriv yR')
  let H := positiveReferenceHeight l r δ hL' hR'
  change ContDiff ℝ ∞ Y ∧ (∀ x, 0 < deriv Y x) ∧
    (∃ B : ℝ, 0 < B ∧ ∀ x, B ≤ deriv Y x) ∧
    Function.Bijective Y ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
    Y '' Ioo l r = Ioo 0 1 ∧ ContDiff ℝ ∞ H ∧
    (∀ x, 0 < H x) ∧ (∀ x ∈ F, H x = 1) ∧
    ∀ side : Bool,
      Y =ᶠ[𝓝 (if side then r else l)] (if side then yR' else yL') ∧
      H =ᶠ[𝓝 (if side then r else l)] (if side then hR' else hL') at hresult
  rcases hresult with ⟨hY, hYpos, hfloor, hbij, hinv, himage, hH, hHpos, hHone, hgerm⟩
  have hYl : Y l = 0 := (hgerm false).1.eq_of_nhds.trans hvL'
  have hYr : Y r = 1 := (hgerm true).1.eq_of_nhds.trans hvR'
  have hHl : H l = hL l := by
    calc
      H l = hL' l := (hgerm false).2.eq_of_nhds
      _ = Real.exp (Real.log (hL l)) := congrArg Real.exp
        (n06ReferenceEndpointTaylor_value 3 l (fun t => Real.log (hL t)))
      _ = hL l := Real.exp_log hpL
  have hHr : H r = hR r := by
    calc
      H r = hR' r := (hgerm true).2.eq_of_nhds
      _ = Real.exp (Real.log (hR r)) := congrArg Real.exp
        (n06ReferenceEndpointTaylor_value 3 r (fun t => Real.log (hR t)))
      _ = hR r := Real.exp_log hpR
  refine ⟨δ, Y, H, hδ, hδη, hgap, havoidL, havoidR, hY, hYpos,
    hfloor, hbij, hinv, himage, hYl, hYr, hH, hHpos, hHone, hHl, hHr, ?_⟩
  intro side
  constructor
  · intro k hk
    have he := ((hgerm side).1.iteratedDeriv k).eq_of_nhds
    cases side with
    | false => exact he.trans (iteratedDeriv_n06ReferenceEndpointTaylor 4 l yL hk)
    | true => exact he.trans (iteratedDeriv_n06ReferenceEndpointTaylor 4 r yR hk)
  · intro k hk
    have he := (hgerm side).2.fun_comp Real.log
    cases side with
    | false =>
        have he' : (fun x => Real.log (H x)) =ᶠ[𝓝 l]
            n06ReferenceEndpointTaylor 3 l (fun x => Real.log (hL x)) := by
          simpa only [Bool.false_eq_true, ite_false, ite_true, Function.comp_def,
            hL', Real.log_exp] using he
        exact (he'.iteratedDeriv k).eq_of_nhds.trans
          (iteratedDeriv_n06ReferenceEndpointTaylor 3 l (fun x => Real.log (hL x)) hk)
    | true =>
        have he' : (fun x => Real.log (H x)) =ᶠ[𝓝 r]
            n06ReferenceEndpointTaylor 3 r (fun x => Real.log (hR x)) := by
          simpa only [Bool.false_eq_true, ite_false, ite_true, Function.comp_def,
            hR', Real.log_exp] using he
        exact (he'.iteratedDeriv k).eq_of_nhds.trans
          (iteratedDeriv_n06ReferenceEndpointTaylor 3 r (fun x => Real.log (hR x)) hk)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- Classification by the original cut pairs fixes the lower canonical
endpoint of every actual negative reference piece. -/
private theorem n06_negativeReference_left_eq_zero
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) : K.left i = 0 := by
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have hC : controlGeometryConditions D S C := h.1.1.1.2.2.2.1
  obtain ⟨n, hni | hni⟩ := n06_negativePiece_is_cutHalf h04 hC hi
  · rw [hni]
    exact (h04.2.1.1.1 n).2.2.2.2.2.2.1
  · rw [hni]
    exact (h04.2.1.1.1 n).2.2.2.2.2.2.2.1

/-- At an actual root, the negative radial coordinate points into its
positive canonical interval.  Its right-end slope is negative and its
left-end slope positive. -/
theorem n06_reference_negative_root_deriv_sign
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) (upper : Bool)
    (hroot : deriv D.w (n06Endpoint (K.physicalLeft i) (K.physicalRight i) upper) = 0) :
    if upper then
      deriv (n06ReferenceNegativeY C K i) (K.physicalRight i) < 0
    else 0 < deriv (n06ReferenceNegativeY C K i) (K.physicalLeft i) := by
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h.1.1.1.2.1
  have hsref := n05_referenceState_sector h.1.1.1.2.2.1
  have he : n06Endpoint (K.physicalLeft i) (K.physicalRight i) upper ∈
      Icc (K.physicalLeft i) (K.physicalRight i) := by
    cases upper <;> simp only [n06Endpoint, Bool.false_eq_true, if_false, if_true,
      mem_Icc, le_refl, and_true, true_and, (h04.1.referenceBounds i).1.le]
  have hdata := n06_reference_negative_height_normalization hT hS h hi he
  have hmap : MapsTo (n06ReferenceNegativeY C K i)
      (Ioo (K.physicalLeft i) (K.physicalRight i)) (Ioo (K.left i) (K.right i)) := by
    intro r hr
    have hp : (r, (0 : ℝ)) ∈ physicalPieceOpen S K (C.referenceState, 0) i := by
      rw [h04.1.referenceDomain i]
      exact ⟨hr, mem_univ _⟩
    exact ((h04.1.charts (C.referenceState, 0) href hsref i).1 hp).1
  have hvalue : n06ReferenceNegativeY C K i
      (n06Endpoint (K.physicalLeft i) (K.physicalRight i) upper) =
        n06Endpoint (K.left i) (K.right i) false := by
    change n06ReferenceNegativeY C K i
      (n06Endpoint (K.physicalLeft i) (K.physicalRight i) upper) = K.left i
    rw [n06_negativeReference_left_eq_zero h hi]
    exact n05_negative_reference_root_image hT hS h hi
      (x := (n06Endpoint (K.physicalLeft i) (K.physicalRight i) upper, 0)) he hroot
  have hp := n06_hasDerivAt_endpoint_orientation upper false
    (h04.1.referenceBounds i).1 hmap hvalue
    (hdata.1.differentiableAt (by simp)).hasDerivAt hdata.2.2.2.1
  cases upper <;> simpa only [n06EndpointSign, n06Endpoint, Bool.false_eq_true,
    if_false, if_true, neg_one_mul, one_mul, neg_mul, neg_neg, neg_pos] using hp

/-- A positive reference piece with two actual negative neighbours admits
an explicitly constructed radial reference coordinate and height.  Every
endpoint datum comes from those negative charts.  The construction matches
the finite orders needed for cubic principal matching and fixes the height
on the full closed support of chi.  It does not claim that an arbitrary old
positive chart was radial, or provide a uniform material bound. -/
theorem n06_positiveReference_from_adjacent_negative
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m iL iR : ℕ} (hm : K.positive m = true)
    (hiL : K.positive iL = false) (hiR : K.positive iR = false)
    (hjoinL : K.physicalRight iL = K.physicalLeft m)
    (hjoinR : K.physicalRight m = K.physicalLeft iR)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, ∃ Y H : ℝ → ℝ,
      0 < δ ∧ δ < η ∧ 2 * δ < K.physicalRight m - K.physicalLeft m ∧
      Disjoint (Metric.ball (K.physicalLeft m) δ) (tsupport D.chi) ∧
      Disjoint (Metric.ball (K.physicalRight m) δ) (tsupport D.chi) ∧
      ContDiff ℝ ∞ Y ∧ (∀ x, 0 < deriv Y x) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ x, B ≤ deriv Y x) ∧
      Function.Bijective Y ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
      Y '' Ioo (K.physicalLeft m) (K.physicalRight m) = Ioo 0 1 ∧
      Y (K.physicalLeft m) = 0 ∧ Y (K.physicalRight m) = 1 ∧
      ContDiff ℝ ∞ H ∧ (∀ x, 0 < H x) ∧ (∀ x ∈ tsupport D.chi, H x = 1) ∧
      H (K.physicalLeft m) = n06ReferenceNegativeH C K iL (K.physicalLeft m) ∧
      H (K.physicalRight m) = n06ReferenceNegativeH C K iR (K.physicalRight m) ∧
      ∀ side : Bool,
        (∀ k : ℕ, k ≤ 4 →
          iteratedDeriv k Y (if side then K.physicalRight m else K.physicalLeft m) =
            iteratedDeriv k
              (if side then (fun x => 1 + n06ReferenceNegativeY C K iR x)
                else (fun x => -n06ReferenceNegativeY C K iL x))
              (if side then K.physicalRight m else K.physicalLeft m)) ∧
        (∀ k : ℕ, k ≤ 3 →
          iteratedDeriv k (fun x => Real.log (H x))
              (if side then K.physicalRight m else K.physicalLeft m) =
            iteratedDeriv k
              (fun x => Real.log (n06ReferenceNegativeH C K (if side then iR else iL) x))
              (if side then K.physicalRight m else K.physicalLeft m)) := by
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have hD : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  have hborder : RadialTrueBorder D := h.1.1.1.1.2.2.2.1
  have hdw : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2.continuous
  have hlneg : K.physicalLeft m ∈ Icc (K.physicalLeft iL) (K.physicalRight iL) := by
    rw [← hjoinL]
    exact ⟨(h04.1.referenceBounds iL).1.le, le_rfl⟩
  have hrneg : K.physicalRight m ∈ Icc (K.physicalLeft iR) (K.physicalRight iR) := by
    rw [hjoinR]
    exact ⟨le_rfl, (h04.1.referenceBounds iR).1.le⟩
  have hnonneg (r : ℝ) (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      0 ≤ deriv D.w r := by
    apply le_on_closure (fun x hx => (h04.1.referencePositive m hm x hx).le)
      continuousOn_const hdw.continuousOn
    simpa only [closure_Ioo (h04.1.referenceBounds m).1.ne] using hr
  have hnonpos (i : ℕ) (hi : K.positive i = false) (r : ℝ)
      (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) : deriv D.w r ≤ 0 := by
    apply le_on_closure (fun x hx => (h04.1.referenceNegative i hi x hx).le)
      hdw.continuousOn continuousOn_const
    simpa only [closure_Ioo (h04.1.referenceBounds i).1.ne] using hr
  have hrootL : deriv D.w (K.physicalLeft m) = 0 :=
    le_antisymm (hnonpos iL hiL _ hlneg)
      (hnonneg _ ⟨le_rfl, (h04.1.referenceBounds m).1.le⟩)
  have hrootR : deriv D.w (K.physicalRight m) = 0 :=
    le_antisymm (hnonpos iR hiR _ hrneg)
      (hnonneg _ ⟨(h04.1.referenceBounds m).1.le, le_rfl⟩)
  have havoidL : K.physicalLeft m ∉ tsupport D.chi := by
    intro hx
    have hp := (hborder.2.2.1 hx).2
    rw [hrootL] at hp
    exact lt_irrefl 0 hp
  have havoidR : K.physicalRight m ∉ tsupport D.chi := by
    intro hx
    have hp := (hborder.2.2.1 hx).2
    rw [hrootR] at hp
    exact lt_irrefl 0 hp
  have hL := n06_reference_negative_height_normalization hT hS h hiL hlneg
  have hR := n06_reference_negative_height_normalization hT hS h hiR hrneg
  have hvalL : n06ReferenceNegativeY C K iL (K.physicalLeft m) = 0 :=
    n05_negative_reference_root_image hT hS h hiL
      (x := (K.physicalLeft m, 0)) hlneg hrootL
  have hvalR : n06ReferenceNegativeY C K iR (K.physicalRight m) = 0 :=
    n05_negative_reference_root_image hT hS h hiR
      (x := (K.physicalRight m, 0)) hrneg hrootR
  have hslopeL : deriv (n06ReferenceNegativeY C K iL) (K.physicalLeft m) < 0 := by
    have he := n06_reference_negative_root_deriv_sign hT hS h hiL true
      (by simpa only [n06Endpoint, if_true, hjoinL] using hrootL)
    simpa only [if_true, hjoinL] using he
  have hslopeR : 0 < deriv (n06ReferenceNegativeY C K iR) (K.physicalRight m) := by
    have he := n06_reference_negative_root_deriv_sign hT hS h hiR false
      (by simpa only [n06Endpoint, Bool.false_eq_true, if_false, ← hjoinR] using hrootR)
    simpa only [Bool.false_eq_true, if_false, ← hjoinR] using he
  have hderivL : 0 < deriv (fun x => -n06ReferenceNegativeY C K iL x)
      (K.physicalLeft m) := by
    change 0 < deriv (-n06ReferenceNegativeY C K iL) (K.physicalLeft m)
    rw [((hL.1.differentiableAt (by simp)).hasDerivAt.neg).deriv]
    exact neg_pos.mpr hslopeL
  have hderivR : 0 < deriv (fun x => 1 + n06ReferenceNegativeY C K iR x)
      (K.physicalRight m) := by
    have he : deriv (fun x => 1 + n06ReferenceNegativeY C K iR x)
        (K.physicalRight m) =
          0 + deriv (n06ReferenceNegativeY C K iR) (K.physicalRight m) :=
      ((hasDerivAt_const (K.physicalRight m) (1 : ℝ)).add
        (hR.1.differentiableAt (by simp)).hasDerivAt).deriv
    rw [he, zero_add]
    exact hslopeR
  obtain ⟨δ, Y, H, hresult⟩ := n06_positiveReference_from_finite_endpoint_jets
    (isClosed_tsupport D.chi) havoidL havoidR (h04.1.referenceBounds m).1 hη
    (yL := fun x => -n06ReferenceNegativeY C K iL x)
    (yR := fun x => 1 + n06ReferenceNegativeY C K iR x)
    (hL := n06ReferenceNegativeH C K iL) (hR := n06ReferenceNegativeH C K iR)
    (by rw [hvalL, neg_zero]) (by rw [hvalR, add_zero])
    hderivL hderivR hL.2.2.1 hR.2.2.1
  rcases hresult with ⟨hδ, hδη, hgap, havoidL, havoidR, hY, hYpos,
    hfloor, hbij, hinv, himage, hYl, hYr, hH, hHpos, hHone, hHl, hHr, hjets⟩
  refine ⟨δ, Y, H, hδ, hδη, hgap, havoidL, havoidR, hY, hYpos,
    hfloor, hbij, hinv, himage, hYl, hYr, hH, hHpos, hHone, hHl, hHr, ?_⟩
  intro side
  have he := hjets side
  cases side <;> exact he

end ContinuousFlexibility.Statements
