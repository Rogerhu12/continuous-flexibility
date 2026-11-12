import ContinuousFlexibility.Analysis.N07aAngularPieceInterfaces
import ContinuousFlexibility.Analysis.N07aAngularReferenceSymmetry
import ContinuousFlexibility.Analysis.N07bReferenceTransport
import ContinuousFlexibility.Analysis.N07bReferencePieceRegularity
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# A genuine C¹ reference realization from the geometric transport

The transition fields in N07b are independent of the candidate. Their C³
regularity gives a common first jet across the reference interfaces. On
each reference piece the field is the actual current-chart pullback, whose
closed-piece smoothness follows from the stored boundary inverse germs.
The actual current pieces may have curved, state-dependent boundaries.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_exists_referenceTransport_C1
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (aL : ℝ) {η : PolarPoint → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηπ : Function.Periodic η (0, Real.pi)) (hηe : ∀ r θ, η (r, -θ) = η (r, θ)) :
    ∃ v : PolarPoint → ℝ,
      ContDiffOn ℝ 1 v (annularOpen D) ∧ Function.Periodic v (0, Real.pi) ∧
      (∀ r θ, v (r, -θ) = v (r, θ)) ∧
      (∀ m, EqOn v
        (n07aReferencePieceHeight C K (liftSectorParameter S C z)
          (K.inverseChart (liftSectorParameter S C z)) aL η m)
        (referencePhysicalPieceOpen S K m)) ∧
      (∀ m, EqOn
        (canonicalHeight S K (C.referenceState, 0) m (fun p => v p - aL * S.chiLeft p.1))
        (canonicalHeight S K (liftSectorParameter S C z) m (fun p => η p - aL * S.chiLeft p.1))
        (canonicalOpen S K m)) ∧
      (∀ p, p ∉ annularOpen D → v p = 0) ∧
      ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
        ContDiffAt ℝ ∞ u p ∧
        ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q := by
  classical
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  have hrefz := n07a_reference_mem_stateNeighborhood h01
  have hrefs := h01.2.2.1.stateSector
  let z' := liftSectorParameter S C z
  obtain ⟨τ, q, hτ, hq, hmap, hτπ, hqπ, hτe, hqe, hpiece, _⟩ :=
    hcanonical.transport z' hz' hs
  let F := n07bReferenceTransport S τ q aL η
  let v := (annularOpen D).indicator F
  let W := n07aReferencePieceHeight C K z' (K.inverseChart z') aL η
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hF : ContDiffOn ℝ 3 F (annularOpen D) :=
    n07bReferenceTransport_contDiffOn hτ hq hmap
      (hη.of_le (by simp)).contDiffOn (hS.2.2.1.1.of_le (by simp)) aL
  have hv : ContDiffOn ℝ 1 v (annularOpen D) :=
    (hF.of_le (by norm_num)).congr (fun p hp => indicator_of_mem hp F)
  have hτpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = K.inverseChart z' m (K.chart (C.referenceState, 0) m p) :=
    fun m p hp => (hpiece m p hp).1
  have hqpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      q p = K.height (C.referenceState, 0) m p / K.height z' m (τ p) :=
    fun m p hp => (hpiece m p hp).2
  have hvpiece (m : ℕ) : EqOn v (W m) (referencePhysicalPieceOpen S K m) := by
    intro p hp
    have hpD : p ∈ annularOpen D :=
      ⟨(h04.1.referenceBounds m).2.2 hp.1, mem_univ _⟩
    rw [show v p = F p from indicator_of_mem hpD F]
    dsimp only [F, W, n07bReferenceTransport, n07aReferencePieceHeight]
    rw [hqpiece m p hp, hτpiece m p hp]
    ring
  have hχ : ContDiff ℝ ∞ (fun p : PolarPoint => aL * S.chiLeft p.1) :=
    contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  have hWclosed (m : ℕ) (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ (W m) p := by
    have hpclosed : p ∈ physicalPieceClosed S K (C.referenceState, 0) m := by
      rw [physicalPieceClosed, h04.1.referenceDomain m, referencePhysicalPieceOpen,
        closure_prod_eq, closure_Ioo (h04.1.referenceBounds m).1.ne, closure_univ]
      exact ⟨hp, mem_univ _⟩
    have hR := n07bReferencePieceRemainder_contDiffAt_closed h04.1
      hrefz hrefs hz' hs m (hη.sub hχ) hpclosed
    have hformula : W m = fun p =>
        n07bReferencePieceRemainder C K z' m
          (fun x => η x - aL * S.chiLeft x.1) p + aL * S.chiLeft p.1 := by
      funext p
      rfl
    rw [hformula]
    exact hR.add hχ.contDiffAt
  have hvclosed (m : ℕ) (p : PolarPoint) (hpD : p ∈ annularOpen D)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      v p = W m p := by
    have hpcl : p ∈ closure (referencePhysicalPieceOpen S K m) := by
      rw [referencePhysicalPieceOpen, closure_prod_eq,
        closure_Ioo (h04.1.referenceBounds m).1.ne, closure_univ]
      exact ⟨hp, mem_univ _⟩
    haveI : NeBot (𝓝[referencePhysicalPieceOpen S K m] p) :=
      mem_closure_iff_nhdsWithin_neBot.mp hpcl
    exact tendsto_nhds_unique_of_eventuallyEq
      ((hv.contDiffAt (hU.mem_nhds hpD)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hWclosed m p hp).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (self_mem_nhdsWithin.mono fun x hx => hvpiece m hx)
  have hFπ : Function.Periodic F (0, Real.pi) :=
    n07bReferenceTransport_periodic hτπ hqπ hηπ aL
  have hvπ : Function.Periodic v (0, Real.pi) := by
    intro p
    by_cases hp : p ∈ annularOpen D
    · have hpπ : p + (0, Real.pi) ∈ annularOpen D :=
        ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
      exact (indicator_of_mem hpπ F).trans ((hFπ p).trans (indicator_of_mem hp F).symm)
    · have hpπ : p + (0, Real.pi) ∉ annularOpen D := by
        intro h
        exact hp ⟨by simpa only [Prod.fst_add, add_zero] using h.1, mem_univ _⟩
      exact (indicator_of_notMem hpπ F).trans (indicator_of_notMem hp F).symm
  have hFe := n07bReferenceTransport_even hτe hqe hηe aL
  have hve : ∀ r θ, v (r, -θ) = v (r, θ) := by
    intro r θ
    by_cases hr : r ∈ radialCore D
    · exact (indicator_of_mem (show (r, -θ) ∈ annularOpen D from ⟨hr, mem_univ _⟩) F).trans
        ((hFe r θ).trans
          (indicator_of_mem (show (r, θ) ∈ annularOpen D from ⟨hr, mem_univ _⟩) F).symm)
    · exact (indicator_of_notMem (show (r, -θ) ∉ annularOpen D from fun hp => hr hp.1) F).trans
        (indicator_of_notMem (show (r, θ) ∉ annularOpen D from fun hp => hr hp.1) F).symm
  refine ⟨v, hv, hvπ, hve, hvpiece, ?_,
    (fun p hp => indicator_of_notMem hp F), ?_⟩
  · intro m
    exact n07aReferencePieceHeight_canonical h01 h04 (fun _ _ _ => rfl)
      aL η m (hvpiece m)
  · intro p hp
    by_cases hinterior : ∃ m, p ∈ referencePhysicalPieceOpen S K m
    · obtain ⟨m, hm⟩ := hinterior
      refine ⟨W m, hWclosed m p (Ioo_subset_Icc_self hm.1), ?_⟩
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hm] with x hx _
      exact hvpiece m hx
    · have hnot (m : ℕ) : p.1 ∉ Ioo (K.physicalLeft m) (K.physicalRight m) :=
        fun hm => hinterior ⟨m, hm, mem_univ _⟩
      obtain ⟨i, j, _, _, hj⟩ :=
        n07a_physicalPieces_adjacent_at_boundary hD hT h04 href hp.1 hnot
      have hright : p.1 < K.physicalRight j := by
        simpa only [hj] using (h04.1.referenceBounds j).1
      refine ⟨W j, hWclosed j p ⟨by rw [hj], hright.le⟩, ?_⟩
      filter_upwards [hU.mem_nhds hp,
        (isOpen_lt continuous_fst continuous_const).mem_nhds hright] with x hxD hxr hpx
      exact hvclosed j x hxD ⟨by simpa only [hj] using hpx, hxr.le⟩

end ContinuousFlexibility.Analysis
