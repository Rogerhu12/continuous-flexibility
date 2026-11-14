module

public import ContinuousFlexibility.Analysis.N06FiniteAtlasBoundary
public import ContinuousFlexibility.Analysis.N06CurrentBoundaryTestSupport
public import ContinuousFlexibility.Analysis.N06CutSaturatedSupport

/-!
# Actual canonical endpoint rows on the finite physical atlas

Each canonical Green row is assigned to its reference index side. The
finite envelope contains both halves of every artificial cut, whose rows
are paired at the same canonical radius. Only a side without a neighbor
uses the physical test support; such a side cannot be an artificial cut.
Its actual closed inverse circle, rather than a reference middle radius,
supplies the physical endpoint used by the support argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

/-- A compact radial support admits a strictly larger closed window
inside the original annulus, including when that support is empty. -/
theorem n06_compact_openInterval_window {a b : ℝ} (hab : a < b)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Ioo a b) :
    ∃ l r : ℝ, l < r ∧ J ⊆ Ioo l r ∧ Icc l r ⊆ Ioo a b := by
  by_cases hne : J.Nonempty
  · obtain ⟨c, hc⟩ := hJ.exists_isLeast hne
    obtain ⟨d, hd⟩ := hJ.exists_isGreatest hne
    obtain ⟨l, hal, hlc⟩ := exists_between (hJsub hc.1).1
    obtain ⟨r, hdr, hrb⟩ := exists_between (hJsub hd.1).2
    exact ⟨l, r, (hlc.trans_le (hc.2 hd.1)).trans hdr,
      fun x hx => ⟨hlc.trans_le (hc.2 hx), (hd.2 hx).trans_lt hdr⟩,
      fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩⟩
  · obtain ⟨l, hal, hlb⟩ := exists_between hab
    obtain ⟨r, hlr, hrb⟩ := exists_between hlb
    exact ⟨l, r, hlr, fun x hx => (hne ⟨x, hx⟩).elim,
      fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩⟩

/-- The endpoint row indexed by a reference side. On negative halves
the reversal flag exchanges the root and cut canonical endpoints. -/
def n06OrientedCanonicalBoundary
    {S : PhysicalSpacesData} {K : CanonicalData S} {z : AnnularState S × ℝ}
    {m : ℕ} {φ : PolarPoint → ℝ}
    (Q : N06CurrentHeightTestTraces S K z m φ) (W : PolarPoint → ℝ)
    (a : ℝ → ℝ) (reverse physicalUpper : Bool) (θ : ℝ) : ℝ :=
  let y := if (if reverse then !physicalUpper else physicalUpper) then K.right m else K.left m
  (if reverse then (-1 : ℝ) else 1) * a y *
    (Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ))

/-- Reversing a chart exchanges the two canonical endpoints and reverses
both physical normal rows, leaving the same canonical Green difference. -/
theorem n06_orientedCanonicalBoundary_difference
    {S : PhysicalSpacesData} {K : CanonicalData S} {z : AnnularState S × ℝ}
    {m : ℕ} {φ W : PolarPoint → ℝ}
    (Q : N06CurrentHeightTestTraces S K z m φ) (a : ℝ → ℝ)
    (hW : ContDiff ℝ 1 W) (reverse : Bool) :
    ((∫ θ in (0 : ℝ)..Real.pi, n06OrientedCanonicalBoundary Q W a reverse true θ) -
      ∫ θ in (0 : ℝ)..Real.pi, n06OrientedCanonicalBoundary Q W a reverse false θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.right m) * (Q.value (K.right m, θ) * radialPartial W (K.right m, θ) -
          W (K.right m, θ) * Q.radial (K.right m, θ)) -
        a (K.left m) * (Q.value (K.left m, θ) * radialPartial W (K.left m, θ) -
          W (K.left m, θ) * Q.radial (K.left m, θ)) := by
  have hcont (y : ℝ) : Continuous (fun θ =>
      Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ)) := by
    have hline : Continuous (fun θ : ℝ => (y, θ)) := continuous_const.prodMk continuous_id
    have hd : Continuous (radialPartial W) :=
      (hW.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact ((Q.value_lipschitz.continuous.comp hline).mul (hd.comp hline)).sub
      ((hW.continuous.comp hline).mul (Q.radial_lipschitz.continuous.comp hline))
  have hright : IntervalIntegrable (fun θ => a (K.right m) *
      (Q.value (K.right m, θ) * radialPartial W (K.right m, θ) -
        W (K.right m, θ) * Q.radial (K.right m, θ))) volume 0 Real.pi :=
    ((hcont (K.right m)).const_mul _).intervalIntegrable _ _
  have hleft : IntervalIntegrable (fun θ => a (K.left m) *
      (Q.value (K.left m, θ) * radialPartial W (K.left m, θ) -
        W (K.left m, θ) * Q.radial (K.left m, θ))) volume 0 Real.pi :=
    ((hcont (K.left m)).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hright hleft]
  cases reverse <;>
    simp only [n06OrientedCanonicalBoundary, Bool.false_eq_true, if_false,
      if_true, Bool.not_false, Bool.not_true, one_mul, neg_one_mul, neg_mul,
      intervalIntegral.integral_neg]
  ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

/-- The original physical test itself supplies a compact support and an
interior window; no support window is an additional test requirement. -/
theorem n06_radialTest_supportWindow
    (hD : IsAccumulatingProfile D) (hφ : RadialTest D φ) :
    ∃ J : Set ℝ, ∃ l r : ℝ, IsCompact J ∧ l < r ∧ J ⊆ Ioo l r ∧
      Icc l r ⊆ radialCore D ∧ (∀ x, x ∉ J → ∀ θ, φ (x, θ) = 0) := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hφ.2.2
  obtain ⟨l, r, hlr, hsub, hwindow⟩ :=
    n06_compact_openInterval_window hD.choose_spec.1.2.1 hJ hJD
  exact ⟨J, l, r, hJ, hlr, hsub, hwindow, hzero⟩

/-- An artificial side is the upper reference side of the left half or
the lower reference side of the right half. It is an index designation,
not a claim about the location of the current physical curve. -/
def n06ArtificialCutSide (K : CanonicalData S) (m : ℕ) (upper : Bool) : Prop :=
  if upper then ∃ n, m = (K.cutPair n).1 else ∃ n, m = (K.cutPair n).2

/-- The actual inverse endpoint circle, together with the original test
support, removes the entire oriented boundary integral at a true endpoint. -/
theorem n06_orientedCanonicalBoundary_zero_off_support
    {m : ℕ} (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (W : PolarPoint → ℝ) (a : ℝ → ℝ) (reverse physicalUpper : Bool)
    (hend : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      (K.inverseChart z m
        ((if (if reverse then !physicalUpper else physicalUpper) then K.right m else K.left m),
          θ)).1 = if physicalUpper then K.physicalRight m else K.physicalLeft m)
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ x, x ∉ J → ∀ θ, φ (x, θ) = 0)
    (hout : (if physicalUpper then K.physicalRight m else K.physicalLeft m) ∉ J) :
    (∫ θ in (0 : ℝ)..Real.pi,
      n06OrientedCanonicalBoundary Q W a reverse physicalUpper θ) = 0 := by
  have hy : (if (if reverse then !physicalUpper else physicalUpper)
      then K.right m else K.left m) ∈ Icc (K.left m) (K.right m) := by
    have he (upper : Bool) :
        (if upper then K.right m else K.left m) ∈ Icc (K.left m) (K.right m) := by
      cases upper
      · exact ⟨le_rfl, (h04.1.referenceBounds m).2.1.le⟩
      · exact ⟨(h04.1.referenceBounds m).2.1.le, le_rfl⟩
    exact he (if reverse then !physicalUpper else physicalUpper)
  have hinverse : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      (K.inverseChart z m
        ((if (if reverse then !physicalUpper else physicalUpper) then K.right m else K.left m),
          θ)).1 ∉ J := by
    intro θ hθ
    rw [hend θ hθ]
    exact hout
  calc
    _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Icc (0 : ℝ) Real.pi :=
        by simpa only [uIcc_of_le Real.pi_pos.le] using hθ
      obtain ⟨hv, hd, _⟩ := Q.boundary_zero_off_support h04 hz hs hy hJ hzero hinverse hθ'
      simp only [n06OrientedCanonicalBoundary, hv, hd, zero_mul, mul_zero, sub_self]
    _ = 0 := by simp

/-- The real endpoint rows cancel on the same cut-saturated envelope.
Reference intervals supply only neighbors and their uniqueness. Missing
neighbors force true endpoints off support; artificial cuts always have
their paired index and are never assigned a false support-zero condition. -/
theorem n06_current_finiteAtlas_boundary_sum
    (hD : IsAccumulatingProfile D)
    (hC : controlGeometryConditions D S C)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ} (hJ : IsClosed J) {l r : ℝ}
    (hJwindow : J ⊆ Ioo l r) (hwindow : Icc l r ⊆ radialCore D)
    (hsupport : ∀ x, x ∉ J → ∀ θ, φ (x, θ) = 0)
    (Q : ∀ m, N06CurrentHeightTestTraces S K z m φ)
    (W : ℕ → PolarPoint → ℝ) (a : ℕ → ℝ → ℝ) (reverse : ℕ → Bool)
    (hends : ∀ m, ∀ side : Bool, ¬n06ArtificialCutSide K m side →
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        (K.inverseChart z m
          ((if (if reverse m then !side else side) then K.right m else K.left m), θ)).1 =
            if side then K.physicalRight m else K.physicalLeft m)
    (hmatch : ∀ i j, K.physicalRight i = K.physicalLeft j →
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        n06OrientedCanonicalBoundary (Q i) (W i) (a i) (reverse i) true θ =
          n06OrientedCanonicalBoundary (Q j) (W j) (a j) (reverse j) false θ) :
    ∃ hfinite : (n06CutSaturatedSupport C K (Icc l r)).Finite,
      (∑ m ∈ hfinite.toFinset,
        ((∫ θ in (0 : ℝ)..Real.pi,
          n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) true θ) -
        ∫ θ in (0 : ℝ)..Real.pi,
          n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) false θ)) = 0 := by
  classical
  have hfinite := n06_cutSaturatedSupport_finite hD hC hcoords isCompact_Icc hwindow
  let I : Finset ℕ := hfinite.toFinset
  let BL : ℕ → ℝ := fun m => ∫ θ in (0 : ℝ)..Real.pi,
    n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) false θ
  let BR : ℕ → ℝ := fun m => ∫ θ in (0 : ℝ)..Real.pi,
    n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) true θ
  have href := n06_controlledReferencePieces_finite_on_compact hD hcoords isCompact_Icc hwindow
  have hcover : ∀ᵐ t ∂volume, t ∈ Ioo l r → ∃ m ∈ I,
      t ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
    filter_upwards [n06_finitePhysicalWindow_cover_ae h04 hwindow href] with t ht hti
    obtain ⟨m, hm, htm⟩ := ht hti
    exact ⟨m, hfinite.mem_toFinset.mpr
      (n06_referenceSupportPieces_subset_cutSaturatedSupport (C := C) (K := K) (Icc l r)
        (href.mem_toFinset.mp hm)), htm⟩
  have hlr := fun m => (h04.1.referenceBounds m).1
  have hdisjoint := n06_physicalPiece_pairwiseDisjoint h04
  have hinjL := n06_disjoint_intervals_left_injective hlr hdisjoint
  have hinjR := n06_disjoint_intervals_right_injective hlr hdisjoint
  have hleftZero (m : ℕ) (hm : m ∈ I)
      (hmissing : ¬∃ j ∈ I, K.physicalRight j = K.physicalLeft m) : BL m = 0 := by
    have hnotcut : ¬n06ArtificialCutSide K m false := by
      rintro ⟨n, hmn⟩
      have hmright : (K.cutPair n).2 ∈ n06CutSaturatedSupport C K (Icc l r) := by
        rw [← hmn]
        exact hfinite.mem_toFinset.mp hm
      have hmleft := (n06_cutSaturatedSupport_pair_iff hC h04 (Icc l r) n).mpr hmright
      apply hmissing
      refine ⟨(K.cutPair n).1, hfinite.mem_toFinset.mpr hmleft, ?_⟩
      rw [hmn]
      exact (h04.2.1.1.1 n).2.2.2.2.1
    have hout : K.physicalLeft m ∉ Ioo l r := by
      intro ht
      obtain ⟨j, hj, _⟩ := n06_finite_intervals_left_neighbor I
        K.physicalLeft K.physicalRight hlr hdisjoint hcover m ht
      exact hmissing ⟨j, hj.1, hj.2⟩
    exact n06_orientedCanonicalBoundary_zero_off_support (Q m) h04 hz hs
      (W m) (a m) (reverse m) false (hends m false hnotcut) hJ hsupport
      (fun hmem => hout (hJwindow hmem))
  have hrightZero (m : ℕ) (hm : m ∈ I)
      (hmissing : ¬∃ j ∈ I, K.physicalLeft j = K.physicalRight m) : BR m = 0 := by
    have hnotcut : ¬n06ArtificialCutSide K m true := by
      rintro ⟨n, hmn⟩
      have hmleft : (K.cutPair n).1 ∈ n06CutSaturatedSupport C K (Icc l r) := by
        rw [← hmn]
        exact hfinite.mem_toFinset.mp hm
      have hmright := (n06_cutSaturatedSupport_pair_iff hC h04 (Icc l r) n).mp hmleft
      apply hmissing
      refine ⟨(K.cutPair n).2, hfinite.mem_toFinset.mpr hmright, ?_⟩
      rw [hmn]
      exact (h04.2.1.1.1 n).2.2.2.2.1.symm
    have hout : K.physicalRight m ∉ Ioo l r := by
      intro ht
      obtain ⟨j, hj, _⟩ := n06_finite_intervals_right_neighbor I
        K.physicalLeft K.physicalRight hlr hdisjoint hcover m ht
      exact hmissing ⟨j, hj.1, hj.2⟩
    exact n06_orientedCanonicalBoundary_zero_off_support (Q m) h04 hz hs
      (W m) (a m) (reverse m) true (hends m true hnotcut) hJ hsupport
      (fun hmem => hout (hJwindow hmem))
  let IR := I.filter (fun i => ∃ j ∈ I, K.physicalLeft j = K.physicalRight i)
  let IL := I.filter (fun j => ∃ i ∈ I, K.physicalRight i = K.physicalLeft j)
  have hnext : ∀ i ∈ IR, ∃ j ∈ IL, K.physicalLeft j = K.physicalRight i := by
    intro i hi
    obtain ⟨j, hj, he⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, i, (Finset.mem_filter.mp hi).1, he.symm⟩, he⟩
  choose neighbor hnext_mem hnext_eq using hnext
  have hbij : (∑ i ∈ IR, BR i) = ∑ j ∈ IL, BL j := by
    apply Finset.sum_bij neighbor hnext_mem
    · intro i hi j hj he
      exact hinjR ((hnext_eq i hi).symm.trans
        ((congrArg K.physicalLeft he).trans (hnext_eq j hj)))
    · intro j hj
      obtain ⟨i, hi, he⟩ := (Finset.mem_filter.mp hj).2
      have hiR : i ∈ IR := Finset.mem_filter.mpr
        ⟨hi, j, (Finset.mem_filter.mp hj).1, he.symm⟩
      exact ⟨i, hiR, hinjL ((hnext_eq i hiR).trans he)⟩
    · intro i hi
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact hmatch i (neighbor i hi) (hnext_eq i hi).symm θ
        (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
  have hsumR : (∑ i ∈ IR, BR i) = ∑ i ∈ I, BR i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    exact hrightZero i hi (fun h => hn (Finset.mem_filter.mpr ⟨hi, h⟩))
  have hsumL : (∑ i ∈ IL, BL i) = ∑ i ∈ I, BL i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    exact hleftZero i hi (fun h => hn (Finset.mem_filter.mpr ⟨hi, h⟩))
  refine ⟨hfinite, ?_⟩
  change (∑ i ∈ I, (BR i - BL i)) = 0
  rw [Finset.sum_sub_distrib, ← hsumR, ← hsumL, hbij, sub_self]

end ContinuousFlexibility.Statements
