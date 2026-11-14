module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05OpticalRootGeometry
public import ContinuousFlexibility.Analysis.N05ReferenceNegativeDensity
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# The first height identity for the actual negative reference chart

The generic root estimates use the height normalization. This file
differentiates that very normalization for the actual N04 slices, with
the absolute Jacobian retained throughout. Both physical orientations
therefore have the same logarithmic formula, also at the closed ends.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem n05_negative_reference_root_slices
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
    let H := fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)
    ContDiffAt ℝ ∞ ξ r ∧ ContDiffAt ℝ ∞ H r ∧
      0 < H r ∧ deriv ξ r ≠ 0 ∧ 0 < D.w r := by
  let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
  let H := fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)
  change ContDiffAt ℝ ∞ ξ r ∧ ContDiffAt ℝ ∞ H r ∧
    0 < H r ∧ deriv ξ r ≠ 0 ∧ 0 < D.w r
  have h01 := h.1.1.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have h04 := h.2.2.2.2.1
  have hclosed := n05_reference_closed_properties h04
  have hc := hclosed hmem hs i (r, θ) hr
  have hslice : ContDiffAt ℝ ∞ (fun t : ℝ => (t, θ)) r :=
    contDiffAt_id.prodMk contDiffAt_const
  have hd := n05_negative_reference_density_closed hT hS h hi hr θ
  have hq : deriv ξ r ≠ 0 := fun he => hc.2.2.1 (hd.1.trans he)
  have hn : H r ^ 2 * D.w r * |deriv ξ r| = 1 := hd.2.1
  refine ⟨ContDiffAt.fun_comp (f := fun t : ℝ => (t, θ))
    (g := fun p : ℝ × ℝ => (K.chart (C.referenceState, 0) i p).1)
    r hc.1.fst hslice,
    ContDiffAt.fun_comp (f := fun t : ℝ => (t, θ))
      (g := K.height (C.referenceState, 0) i) r hc.2.1 hslice,
    hc.2.2.2, hq, ?_⟩
  by_contra hnw
  have hwle : D.w r ≤ 0 := le_of_not_gt hnw
  have hbad : H r ^ 2 * D.w r * |deriv ξ r| ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hwle) (abs_nonneg _)
  rw [hn] at hbad
  norm_num at hbad

theorem n05_negative_reference_height_log_deriv_open
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
    let H := fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)
    deriv H r = -(H r / 2) *
      (deriv D.w r / D.w r + deriv (deriv ξ) r / deriv ξ r) := by
  let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
  let H := fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)
  change deriv H r = -(H r / 2) *
    (deriv D.w r / D.w r + deriv (deriv ξ) r / deriv ξ r)
  obtain ⟨hξ, hH, hHpos, hqne, hwpos⟩ :=
    n05_negative_reference_root_slices hT hS h hi (Ioo_subset_Icc_self hr) θ
  have hw : ContDiff ℝ ∞ D.w := h.1.1.1.1.1.choose_spec.1.2.2.1.1
  have hq : DifferentiableAt ℝ (deriv ξ) r :=
    (hξ.derivWithin (m := 1) (by simp)).differentiableAt (by norm_num)
  have hn : (fun t => H t ^ 2 * D.w t * |deriv ξ t|) =ᶠ[𝓝 r] fun _ => 1 := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact (n05_negative_reference_density_closed hT hS h hi (Ioo_subset_Icc_self ht) θ).2.1
  have hd := n05_optical_height_log_deriv_of_eventuallyEq
    (hH.differentiableAt (by simp)) (hw.differentiable (by simp) r)
    (hq.abs hqne) hHpos hwpos (abs_pos.mpr hqne) hn
  have habs : deriv (fun t => |deriv ξ t|) r / |deriv ξ r| =
      deriv (deriv ξ) r / deriv ξ r := by
    rcases lt_or_gt_of_ne hqne with hneg | hpos
    · have he : deriv (fun t => |deriv ξ t|) r = -deriv (deriv ξ) r := by
        simpa only [Function.comp_def, ξ, neg_one_mul] using
          ((hasDerivAt_abs_neg hneg).comp r hq.hasDerivAt).deriv
      rw [he, abs_of_neg hneg, neg_div_neg_eq]
    · have he : deriv (fun t => |deriv ξ t|) r = deriv (deriv ξ) r := by
        simpa only [Function.comp_def, ξ, one_mul] using
          ((hasDerivAt_abs_pos hpos).comp r hq.hasDerivAt).deriv
      rw [he, abs_of_pos hpos]
  simpa only [habs] using hd

/-- The same exact formula holds at both physical endpoints. It uses the
actual closed-chart regularity and does not assume a logarithmic bound. -/
theorem n05_negative_reference_height_log_deriv
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
    let H := fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)
    deriv H r = -(H r / 2) *
      (deriv D.w r / D.w r + deriv (deriv ξ) r / deriv ξ r) := by
  let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
  let H := fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)
  let I := Icc (K.physicalLeft i) (K.physicalRight i)
  have hslices (x : ℝ) (hx : x ∈ I) :=
    n05_negative_reference_root_slices hT hS h hi hx θ
  have hξC : ContinuousOn (deriv ξ) I := by
    intro x hx
    exact ((hslices x hx).1.derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hξdC : ContinuousOn (deriv (deriv ξ)) I := by
    intro x hx
    exact (((hslices x hx).1.derivWithin (m := 1) (by simp)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hHC : ContinuousOn H I := fun x hx =>
    (hslices x hx).2.1.continuousAt.continuousWithinAt
  have hHdC : ContinuousOn (deriv H) I := by
    intro x hx
    exact ((hslices x hx).2.1.derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hw : ContDiff ℝ ∞ D.w := h.1.1.1.1.1.choose_spec.1.2.2.1.1
  have hrightC : ContinuousOn (fun x => -(H x / 2) *
      (deriv D.w x / D.w x + deriv (deriv ξ) x / deriv ξ x)) I :=
    (hHC.div_const 2).neg.mul
      (((hw.continuous_deriv (by simp)).continuousOn.div hw.continuous.continuousOn
        (fun x hx => (hslices x hx).2.2.2.2.ne')).add
        (hξdC.div hξC (fun x hx => (hslices x hx).2.2.2.1)))
  have he : EqOn (deriv H) (fun x => -(H x / 2) *
      (deriv D.w x / D.w x + deriv (deriv ξ) x / deriv ξ x))
      (Ioo (K.physicalLeft i) (K.physicalRight i)) := by
    intro x hx
    exact n05_negative_reference_height_log_deriv_open hT hS h hi hx θ
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  apply he.of_subset_closure hHdC hrightC Ioo_subset_Icc_self _ hr
  simp only [closure_Ioo (hpieces i).1.ne]
  exact Subset.rfl

/-- The reference time is the genuine optical integral based at the
chosen physical root, with the inward orientation on the right half. -/
theorem n05_cut_reference_root_optical_time
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {r : ℝ}
    (hr : r ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let σ : ℝ := if right then -1 else 1
    n05TricomiTime (K.chart (C.referenceState, 0) i (r, θ)).1 =
      σ * opticalTravel D.w root r := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let σ : ℝ := if right then -1 else 1
  have ht := (n05_cut_reference_angle_and_time hT hS h m right hr θ).2
  change n05TricomiTime (K.chart (C.referenceState, 0) i (r, θ)).1 =
    σ * (opticalTravel D.w (K.physicalLeft i) r -
      opticalTravel D.w (K.physicalLeft i) root) at ht
  have hcore : Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D :=
    n05_cut_physical_closed_subset_core h.1.1.1.2.2.2.1 h.2.2.2.2.1 m right
  have hFC := (n05_opticalSpeed_continuousOn_core h.1.1.1.1.1).mono hcore
  have hint (x y : ℝ)
      (hx : x ∈ Icc (K.physicalLeft i) (K.physicalRight i))
      (hy : y ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      IntervalIntegrable (opticalSpeed D.w) volume x y := by
    apply ContinuousOn.intervalIntegrable
    apply hFC.mono
    intro t ht
    exact ⟨(le_min hx.1 hy.1).trans ht.1, ht.2.trans (max_le hx.2 hy.2)⟩
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hleft : K.physicalLeft i ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    ⟨le_rfl, (hpieces i).1.le⟩
  have hroot : root ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    n05_cut_physical_root_mem h.2.2.2.2.1 m right
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint _ _ hleft hroot) (hint _ _ hroot hr)
  have hdiff : opticalTravel D.w (K.physicalLeft i) r -
      opticalTravel D.w (K.physicalLeft i) root = opticalTravel D.w root r := by
    dsimp only [opticalTravel]
    linarith only [hadd]
  rw [hdiff] at ht
  exact ht

/-- This is precisely the time identity used by the generic root theorem
after the actual inward substitution `r = root + σ*x`. It holds for both
cut halves and uses the actual affine integral substitution. -/
theorem n05_cut_reference_inward_optical_time
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) (x θ : ℝ)
    (hr : (if right then C.right m else C.left m) +
      (if right then (-1 : ℝ) else 1) * x ∈ Icc
        (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let σ : ℝ := if right then -1 else 1
    let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (root + σ * t, θ)).1
    (∫ t in (0 : ℝ)..x,
      Real.sqrt (-deriv D.w (root + σ * t) /
        ((root + σ * t) * D.w (root + σ * t)))) =
      (2 / 3 : ℝ) * ξ x * Real.sqrt (ξ x) := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let σ : ℝ := if right then -1 else 1
  have hσne : σ ≠ 0 := by cases right <;> norm_num [σ]
  have hσinv : σ⁻¹ = σ := by cases right <;> norm_num [σ]
  have ht := n05_cut_reference_root_optical_time hT hS h m right hr θ
  change n05TricomiTime (K.chart (C.referenceState, 0) i (root + σ * x, θ)).1 =
    σ * opticalTravel D.w root (root + σ * x) at ht
  change (∫ t in (0 : ℝ)..x, opticalSpeed D.w (root + σ * t)) =
    n05TricomiTime (K.chart (C.referenceState, 0) i (root + σ * x, θ)).1
  rw [intervalIntegral.integral_comp_add_mul (opticalSpeed D.w) hσne root, hσinv]
  simp only [smul_eq_mul, mul_zero, add_zero]
  exact ht.symm

/-- The genuine chart derivative points inward on both halves. This
follows by differentiating the actual root-based optical time, using
the nonvanishing actual Jacobian; no sign of a separately chosen jet
is prescribed. -/
theorem n05_cut_reference_inward_deriv_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {r : ℝ}
    (hr : r ∈ Ioo
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let σ : ℝ := if right then -1 else 1
    let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
    0 < ξ r ∧ 0 < σ * deriv ξ r := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let σ : ℝ := if right then -1 else 1
  let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1
  change 0 < ξ r ∧ 0 < σ * deriv ξ r
  have h04 := h.2.2.2.2.1
  have hcharts := n05_reference_charts h04
  have hcuts := h04.2.1.1.1
  obtain ⟨hnegL, hnegR, _, _, _, _, hzeroL, hzeroR, _⟩ := hcuts m
  have hi : K.positive i = false := by
    cases right
    · exact hnegL
    · exact hnegR
  have hzero : K.left i = 0 := by
    cases right
    · exact hzeroL
    · exact hzeroR
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs := n05_referenceState_sector h.1.1.1.2.2.1
  have hmap := (hcharts hmem hs i).1
    (show (r, θ) ∈ referencePhysicalPieceOpen S K i from ⟨hr, mem_univ _⟩)
  have hξpos : 0 < ξ r := by simpa only [hzero] using hmap.1.1
  have hslices := n05_negative_reference_root_slices hT hS h hi (Ioo_subset_Icc_self hr) θ
  have hcore : Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D :=
    n05_cut_physical_closed_subset_core h.1.1.1.2.2.2.1 h.2.2.2.2.1 m right
  have hroot : root ∈ radialCore D :=
    hcore (n05_cut_physical_root_mem h.2.2.2.2.1 m right)
  have hchartDeriv := (n05TricomiTime_hasDerivAt hξpos).comp r
    (hslices.1.differentiableAt (by simp)).hasDerivAt
  have htravelDeriv := (n05_opticalTravel_hasDerivAt_core h.1.1.1.1.1 hroot
    (hcore (Ioo_subset_Icc_self hr))).const_mul σ
  have he : (fun t => n05TricomiTime (ξ t)) =ᶠ[𝓝 r]
      fun t => σ * opticalTravel D.w root t := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact n05_cut_reference_root_optical_time hT hS h m right (Ioo_subset_Icc_self ht) θ
  have hd := hchartDeriv.unique (htravelDeriv.congr_of_eventuallyEq he)
  change Real.sqrt (ξ r) * deriv ξ r = σ * opticalSpeed D.w r at hd
  have hσsq : σ ^ 2 = 1 := by cases right <;> norm_num [σ]
  have hσne : σ ≠ 0 := by cases right <;> norm_num [σ]
  have hm : Real.sqrt (ξ r) * (σ * deriv ξ r) = opticalSpeed D.w r := by
    calc
      _ = σ * (Real.sqrt (ξ r) * deriv ξ r) := by ring
      _ = σ * (σ * opticalSpeed D.w r) := by rw [hd]
      _ = opticalSpeed D.w r := by rw [← mul_assoc, ← pow_two, hσsq, one_mul]
  have hqnonneg : 0 ≤ σ * deriv ξ r := by
    apply (mul_nonneg_iff_of_pos_left (Real.sqrt_pos.mpr hξpos)).mp
    rw [hm]
    exact Real.sqrt_nonneg _
  exact ⟨hξpos, lt_of_le_of_ne hqnonneg
    (Ne.symm (mul_ne_zero hσne hslices.2.2.2.1))⟩

/-- The positivity hypotheses of the generic theorem are satisfied by
the actual inward radial slice, for either member of the cut pair. -/
theorem n05_cut_reference_inward_slice_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) (x θ : ℝ)
    (hr : (if right then C.right m else C.left m) +
      (if right then (-1 : ℝ) else 1) * x ∈ Ioo
        (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let root := if right then C.right m else C.left m
    let σ : ℝ := if right then -1 else 1
    let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (root + σ * t, θ)).1
    0 < ξ x ∧ 0 < deriv ξ x := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then C.right m else C.left m
  let σ : ℝ := if right then -1 else 1
  let ξ := fun t : ℝ => (K.chart (C.referenceState, 0) i (root + σ * t, θ)).1
  have hpos := n05_cut_reference_inward_deriv_pos hT hS h m right hr θ
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs := n05_referenceState_sector h.1.1.1.2.2.1
  have h04 := h.2.2.2.2.1
  have hclosed := n05_reference_closed_properties h04
  have hc := hclosed hmem hs i
    (root + σ * x, θ) (Ioo_subset_Icc_self hr)
  have hradial : ContDiffAt ℝ ∞
      (fun r : ℝ => (K.chart (C.referenceState, 0) i (r, θ)).1) (root + σ * x) :=
    ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
      (g := fun p : ℝ × ℝ => (K.chart (C.referenceState, 0) i p).1)
      (root + σ * x) hc.1.fst (contDiffAt_id.prodMk contDiffAt_const)
  have hline : HasDerivAt (fun t : ℝ => root + σ * t) σ x := by
    exact (hasDerivAt_const_mul σ).const_add root
  have hd := ((hradial.differentiableAt (by simp)).hasDerivAt.comp x hline).deriv
  change deriv ξ x =
    deriv (fun r : ℝ => (K.chart (C.referenceState, 0) i (r, θ)).1) (root + σ * x) * σ at hd
  change 0 < ξ x ∧ 0 < deriv ξ x
  refine ⟨hpos.1, ?_⟩
  rw [hd]
  simpa only [mul_comm] using hpos.2

end ContinuousFlexibility.Statements
