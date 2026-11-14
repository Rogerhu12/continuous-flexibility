module

public import ContinuousFlexibility.Analysis.N06ReferenceNegativeHeight
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Genuine endpoint inverses of the selected negative reference chart

The original inverse chart is specified only on the open canonical
piece.  This file constructs a scalar inverse from the smooth forward
chart on a slightly larger physical interval.  Rolle's theorem gives
injectivity there, and the local inverse theorem supplies the smooth
germs at every point of the closed image, including its endpoints.

The constructed inverse agrees with the original inverse on the open
piece.  No value of the totalized inverse at a boundary point is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n06_interval_margin_of_endpoint_nhds
    {P : ℝ → Prop} {a b : ℝ} (_hab : a ≤ b)
    (hP : ∀ x ∈ Icc a b, P x)
    (ha : ∀ᶠ x in 𝓝 a, P x) (hb : ∀ᶠ x in 𝓝 b, P x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ioo (a - δ) (b + δ), P x := by
  obtain ⟨δa, hδa, hnearA⟩ := Metric.mem_nhds_iff.mp ha
  obtain ⟨δb, hδb, hnearB⟩ := Metric.mem_nhds_iff.mp hb
  refine ⟨min δa δb, lt_min hδa hδb, fun x hx => ?_⟩
  by_cases hxa : x < a
  · apply hnearA
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hxa)]
    linarith [hx.1, min_le_left δa δb]
  by_cases hbx : b < x
  · apply hnearB
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hbx)]
    linarith [hx.2, min_le_right δa δb]
  exact hP x ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩

private theorem n06_scalar_injOn_of_deriv_ne
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (hne : ∀ x ∈ Ioo a b, deriv f x ≠ 0) : Set.InjOn f (Ioo a b) := by
  have hlt {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
      (hxy : x < y) (heq : f x = f y) : False := by
    have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
    obtain ⟨z, hz, hzero⟩ := exists_deriv_eq_zero hxy (hf.mono hsub) heq
    exact hne z (hsub ⟨hz.1.le, hz.2.le⟩) hzero
  intro x hx y hy heq
  rcases lt_trichotomy x y with hxy | he | hyx
  · exact (hlt hx hy hxy heq).elim
  · exact he
  · exact (hlt hy hx hyx heq.symm).elim

/-- A nondegenerate smooth scalar map on a closed interval has a single
inverse with actual smooth two-sided germs along its closed image. -/
theorem n06_exists_closed_radial_inverse
    {Y : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hY : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ Y x)
    (hne : ∀ x ∈ Icc a b, deriv Y x ≠ 0) :
    ∃ G : ℝ → ℝ, ∀ x ∈ Icc a b,
      G (Y x) = x ∧ ContDiffAt ℝ ∞ G (Y x) ∧
      HasDerivAt G (deriv Y x)⁻¹ (Y x) ∧
      (∀ᶠ t in 𝓝 x, G (Y t) = t) ∧
      (∀ᶠ y in 𝓝 (Y x), Y (G y) = y) := by
  let P : ℝ → Prop := fun x => ContDiffAt ℝ 1 Y x ∧ deriv Y x ≠ 0
  have hP (x : ℝ) (hx : x ∈ Icc a b) : P x :=
    ⟨(hY x hx).of_le (by simp), hne x hx⟩
  have hnear (x : ℝ) (hx : x ∈ Icc a b) : ∀ᶠ t in 𝓝 x, P t := by
    have hd : ContinuousAt (deriv Y) x :=
      ((hY x hx).derivWithin (m := 0) (by simp)).continuousAt
    exact ((hP x hx).1.eventually (by simp)).and (hd.eventually_ne (hne x hx))
  obtain ⟨δ, hδ, hmargin⟩ := n06_interval_margin_of_endpoint_nhds hab.le hP
    (hnear a ⟨le_rfl, hab.le⟩) (hnear b ⟨hab.le, le_rfl⟩)
  let J : Set ℝ := Ioo (a - δ) (b + δ)
  have hinside : Icc a b ⊆ J := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hinj : Set.InjOn Y J := n06_scalar_injOn_of_deriv_ne
    (fun x hx => (hmargin x hx).1.continuousAt.continuousWithinAt)
    (fun x hx => (hmargin x hx).2)
  let G : ℝ → ℝ := Function.invFunOn Y J
  have hleft (x : ℝ) (hx : x ∈ J) : G (Y x) = x :=
    hinj.leftInvOn_invFunOn hx
  refine ⟨G, fun x hx => ?_⟩
  have hleftNear : ∀ᶠ t in 𝓝 x, G (Y t) = t := by
    filter_upwards [isOpen_Ioo.mem_nhds (hinside hx)] with t ht
    exact hleft t ht
  let hd := ((hY x hx).hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv (hne x hx)
  let e := hd.toOpenPartialHomeomorph Y
  have he : e.symm (Y x) = x := hd.localInverse_apply_image
  have hderiv : HasDerivAt e (deriv Y x) (e.symm (Y x)) := by
    rw [he]
    exact ((hY x hx).differentiableAt (by simp)).hasDerivAt
  have hsmooth : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (Y x)) := by
    rw [he]
    exact hY x hx
  have hG : ContDiffAt ℝ ∞ G (Y x) :=
    (e.contDiffAt_symm_deriv (hne x hx) hd.image_mem_toOpenPartialHomeomorph_target
      hderiv hsmooth).congr_of_eventuallyEq (hd.localInverse_unique hleftNear)
  have hGderiv : HasDerivAt G (deriv Y x)⁻¹ (Y x) :=
    (((hY x hx).hasStrictDerivAt (by simp)).to_local_left_inverse
      (hne x hx) hleftNear).hasDerivAt
  have hrightNear : ∀ᶠ y in 𝓝 (Y x), Y (G y) = y := by
    filter_upwards [hd.localInverse_unique hleftNear, hd.eventually_right_inverse]
      with y hGy hright
    rw [hGy]
    exact hright
  exact ⟨hleft x (hinside hx), hG, hGderiv, hleftNear, hrightNear⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The scalar inverse is constructed from the selected forward chart.
Its compatibility with `inverseChart` is asserted only on the open piece. -/
structure N06ReferenceNegativeInverseData {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (i : ℕ) where
  inverse : ℝ → ℝ
  inverse_chart : ∀ p ∈ canonicalOpen S K i,
    K.inverseChart (C.referenceState, 0) i p = (inverse p.1, p.2)
  left_inverse : ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i),
    inverse (n06ReferenceNegativeY C K i r) = r
  mapsTo : MapsTo inverse (Icc (K.left i) (K.right i))
    (Icc (K.physicalLeft i) (K.physicalRight i))
  right_inverse : ∀ y ∈ Icc (K.left i) (K.right i),
    n06ReferenceNegativeY C K i (inverse y) = y
  smooth : ∀ y ∈ Icc (K.left i) (K.right i), ContDiffAt ℝ ∞ inverse y
  hasDerivAt : ∀ y ∈ Icc (K.left i) (K.right i),
    HasDerivAt inverse (deriv (n06ReferenceNegativeY C K i) (inverse y))⁻¹ y
  left_germ : ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i),
    ∀ᶠ s in 𝓝 r, inverse (n06ReferenceNegativeY C K i s) = s
  right_germ : ∀ y ∈ Icc (K.left i) (K.right i),
    ∀ᶠ t in 𝓝 y, n06ReferenceNegativeY C K i (inverse t) = t

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The original Through04 data supply the genuine closed inverse; no
endpoint convention for the original totalized inverse is needed. -/
theorem n06_referenceNegativeInverseData_nonempty
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) :
    Nonempty (N06ReferenceNegativeInverseData C K i) := by
  let Y : ℝ → ℝ := n06ReferenceNegativeY C K i
  let P : Set ℝ := Icc (K.physicalLeft i) (K.physicalRight i)
  have h01 := h.1.1.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hc := h.2.2.2.2.1.1.charts (C.referenceState, 0) hz hs i
  rw [h.2.2.2.2.1.1.referenceDomain i] at hc
  have hY (r : ℝ) (hr : r ∈ P) : ContDiffAt ℝ ∞ Y r :=
    (n06_reference_negative_height_normalization hT hS h hi hr).1
  have hne (r : ℝ) (hr : r ∈ P) : deriv Y r ≠ 0 :=
    (n06_reference_negative_height_normalization hT hS h hi hr).2.2.2.1
  obtain ⟨G, hG⟩ := n06_exists_closed_radial_inverse (hpieces i).1 hY hne
  have hpoint (p : PolarPoint) (hp : p ∈ canonicalOpen S K i) :
      let x := K.inverseChart (C.referenceState, 0) i p
      x.1 ∈ P ∧ Y x.1 = p.1 ∧ x.2 = p.2 := by
    let x := K.inverseChart (C.referenceState, 0) i p
    change x.1 ∈ P ∧ Y x.1 = p.1 ∧ x.2 = p.2
    have hx : x ∈ referencePhysicalPieceOpen S K i := hc.2.1 hp
    have hxp : x.1 ∈ P := ⟨hx.1.1.le, hx.1.2.le⟩
    have hshape := (n06_reference_negative_radial hT hS h hi x.1 hxp x.2).1
    have hinv := hc.2.2.2.1 p hp
    have he : (Y x.1, x.2) = p := hshape.symm.trans hinv
    have hfirst := congrArg (fun q : PolarPoint => q.1) he
    have hsecond := congrArg (fun q : PolarPoint => q.2) he
    exact ⟨hxp, hfirst, hsecond⟩
  have himage : Icc (K.left i) (K.right i) ⊆ Y '' P := by
    have hcompact : IsCompact P := isCompact_Icc
    have hcontinuous : ContinuousOn Y P :=
      fun r hr => (hY r hr).continuousAt.continuousWithinAt
    have hclosed : IsClosed (Y '' P) :=
      (hcompact.image_of_continuousOn hcontinuous).isClosed
    have hopen : Ioo (K.left i) (K.right i) ⊆ Y '' P := by
      intro y hy
      have hp := hpoint (y, 0) ⟨hy, mem_univ _⟩
      exact ⟨(K.inverseChart (C.referenceState, 0) i (y, 0)).1, hp.1, hp.2.1⟩
    simpa only [closure_Ioo (hpieces i).2.1.ne] using closure_minimal hopen hclosed
  have hclosed (y : ℝ) (hy : y ∈ Icc (K.left i) (K.right i)) :
      G y ∈ P ∧ Y (G y) = y ∧ ContDiffAt ℝ ∞ G y ∧
        HasDerivAt G (deriv Y (G y))⁻¹ y ∧
        (∀ᶠ t in 𝓝 y, Y (G t) = t) := by
    obtain ⟨r, hr, rfl⟩ := himage hy
    obtain ⟨hGr, hGs, hGd, _, hGright⟩ := hG r hr
    rw [hGr]
    exact ⟨hr, rfl, hGs, hGd, hGright⟩
  refine ⟨⟨G, ?_, (fun r hr => (hG r hr).1),
    (fun y hy => (hclosed y hy).1),
    (fun y hy => (hclosed y hy).2.1),
    (fun y hy => (hclosed y hy).2.2.1),
    (fun y hy => (hclosed y hy).2.2.2.1),
    (fun r hr => (hG r hr).2.2.2.1),
    (fun y hy => (hclosed y hy).2.2.2.2)⟩⟩
  intro p hp
  obtain ⟨hxp, hYx, htheta⟩ := hpoint p hp
  apply Prod.ext
  · change (K.inverseChart (C.referenceState, 0) i p).1 = G p.1
    rw [← hYx, (hG _ hxp).1]
  · exact htheta

def N06ReferenceNegativeInverseData.reciprocalHeight
    {i : ℕ} (P : N06ReferenceNegativeInverseData C K i) (y : ℝ) : ℝ :=
  (n06ReferenceNegativeH C K i (P.inverse y))⁻¹

theorem N06ReferenceNegativeInverseData.reciprocalHeight_regular
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {y : ℝ} (hy : y ∈ Icc (K.left i) (K.right i)) :
    ContDiffAt ℝ ∞ P.reciprocalHeight y ∧ 0 < P.reciprocalHeight y := by
  have hreg := n06_reference_negative_height_normalization hT hS h hi (P.mapsTo hy)
  change ContDiffAt ℝ ∞ (fun t =>
      (n06ReferenceNegativeH C K i (P.inverse t))⁻¹) y ∧
    0 < (n06ReferenceNegativeH C K i (P.inverse y))⁻¹
  exact ⟨(hreg.2.1.comp y (P.smooth y hy)).inv hreg.2.2.1.ne',
    inv_pos.mpr hreg.2.2.1⟩

theorem N06ReferenceNegativeInverseData.reciprocalHeight_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K i) :
    P.reciprocalHeight p.1 = canonicalHeight S K (C.referenceState, 0) i (fun _ => 1) p := by
  have hr : P.inverse p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    P.mapsTo ⟨hp.1.1.le, hp.1.2.le⟩
  have hheight := (n06_reference_negative_radial hT hS h hi (P.inverse p.1) hr p.2).2
  simp only [canonicalHeight, P.inverse_chart p hp, hheight, one_div,
    N06ReferenceNegativeInverseData.reciprocalHeight, n06ReferenceNegativeH]

end ContinuousFlexibility.Statements
