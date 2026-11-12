import ContinuousFlexibility.Analysis.N06FiniteCurrentGreenAssembly
import ContinuousFlexibility.Analysis.N06PrimitiveFiniteSupport

/-!
# Finite current Green assembly on the retained primitive atlas

The reference jet data makes the actual cut-saturated support envelope
finite. Reference intervals are used only to pair indices; every current
integral uses its genuine moving domain and every missing-neighbor row
vanishes by the true inverse endpoint circle and physical test support.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

theorem n06_primitive_finiteAtlas_boundary_sum
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : CanonicalGeometry.ReferenceJets D T S C L K)
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
  have hfinite := n06_cutSaturatedSupport_finite_of_primitive hD hT hC h04 hjets isCompact_Icc hwindow
  let I : Finset ℕ := hfinite.toFinset
  let BL : ℕ → ℝ := fun m => ∫ θ in (0 : ℝ)..Real.pi,
    n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) false θ
  let BR : ℕ → ℝ := fun m => ∫ θ in (0 : ℝ)..Real.pi,
    n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) true θ
  have href : (n06ReferenceSupportPieces K (Icc l r)).Finite :=
    hfinite.subset (n06_referenceSupportPieces_subset_cutSaturatedSupport
      (C := C) (K := K) (Icc l r))
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

theorem n06_primitive_finiteGreen_assembly
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : CanonicalGeometry.ReferenceJets D T S C L K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K)
    (hφ : RadialTest D φ)
    (Q : ∀ m, N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ))
    (W : ℕ → PolarPoint → ℝ) (a : ℕ → ℝ → ℝ) (reverse : ℕ → Bool)
    (hW : ∀ m, ContDiff ℝ 1 (W m))
    (hvalue : ∀ m, (u.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] W m)
    (hends : ∀ m, ∀ side : Bool, ¬n06ArtificialCutSide K m side →
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        (K.inverseChart z m
          ((if (if reverse m then !side else side) then K.right m else K.left m), θ)).1 =
            if side then K.physicalRight m else K.physicalLeft m)
    (hgreen : ∀ m,
      (∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, W m p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a m (K.right m) * ((Q m).value (K.right m, θ) * radialPartial (W m) (K.right m, θ) -
          W m (K.right m, θ) * (Q m).radial (K.right m, θ)) -
        a m (K.left m) * ((Q m).value (K.left m, θ) * radialPartial (W m) (K.left m, θ) -
          W m (K.left m, θ) * (Q m).radial (K.left m, θ)))
    (hmatch : ∀ i j, K.physicalRight i = K.physicalLeft j →
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        n06OrientedCanonicalBoundary (Q i) (W i) (a i) (reverse i) true θ =
          n06OrientedCanonicalBoundary (Q j) (W j) (a j) (reverse j) false θ) :
    ((∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06PhysicalHeight K z (fun m => (u.1 m : PolarPoint → ℝ)) u.2.1 (r, θ) *
        divergenceOperator (L.coefficients z) φ (r, θ))) +
      u.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * φ (r, θ))) +
      u.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) -
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ)) (r, θ) * φ (r, θ)))) =
      u.2.1 * ((∫ r in D.a..D.b, radialAngularMean (fun θ =>
        S.chiLeft r * divergenceOperator (L.coefficients z) φ (r, θ))) -
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          n06CurrentLeftColumn S L z (r, θ) * φ (r, θ))) := by
  obtain ⟨J, l, r, hJ, _hlr, hJwindow, hwindow, hsupport⟩ :=
    n06_radialTest_supportWindow h01.1.1 hφ
  obtain ⟨hfinite, hboundary⟩ := n06_primitive_finiteAtlas_boundary_sum h01.1.1 hT h01.2.2.2.1 h04 hjets hz hs
    hJ.isClosed hJwindow hwindow (n06_average_radial_support hsupport) Q W a reverse hends hmatch
  have hzero : (∑ m ∈ hfinite.toFinset,
      ((∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      ∫ p, u.1 m p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m)) = 0 := by
    refine (Finset.sum_congr rfl (fun m _ =>
      n06_current_pieceGreen_of_representative u F m (Q m) (W m) (a m) (reverse m)
        (hW m) (hvalue m) (hgreen m))).trans hboundary
  have hsupportWindow : ∀ x, x ∉ Icc l r → ∀ θ, φ (x, θ) = 0 := by
    intro x hx θ
    exact hsupport x (fun hxJ => hx (Ioo_subset_Icc_self (hJwindow hxJ))) θ
  have hactual := n06_physicalSupportPieces_finite_of_primitive h01.1.1 hT h01.2.2.2.1
    h04 hjets hz hs isCompact_Icc hwindow
  have hsub : ∀ m ∈ n06PhysicalSupportPieces K z (Icc l r), m ∈ hfinite.toFinset := by
    intro m hm
    exact hfinite.mem_toFinset.mpr
      (n06_physicalSupportPieces_subset_cutSaturatedSupport h01.2.2.2.1 h04 hz hs
        (Icc l r) hm)
  have hLsupport : ∀ x, x ∉ Icc l r → ∀ θ,
      divergenceOperator (L.coefficients z) φ (x, θ) = 0 :=
    fun x hx θ => n06_divergenceOperator_zero_off_radial_support
      (L.coefficients z) isClosed_Icc hsupportWindow hx θ
  have hsumHeight := (n06_canonicalPairing_sums_eq_of_support_subset h04 hz hs
    hactual hfinite.toFinset hsub
    (fun m => n06CurrentRemainderSource D S C L K z u F m)
    (n06_average_radial_support hsupportWindow)).1
  have hsumSource := (n06_canonicalPairing_sums_eq_of_support_subset h04 hz hs
    hactual hfinite.toFinset hsub (fun m => (u.1 m : PolarPoint → ℝ))
    (n06_average_radial_support hLsupport)).2
  have hzeroActual : (∑ m ∈ hactual.toFinset,
      ((∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      ∫ p, u.1 m p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumHeight, hsumSource, ← Finset.sum_sub_distrib]
    exact hzero
  rw [n06_current_physicalResidual_eq_finiteGreen hT hS h01 h03 h04 hz hs u F
    isClosed_Icc hactual hφ hsupportWindow, hzeroActual, mul_zero, zero_add]

end ContinuousFlexibility.Statements
