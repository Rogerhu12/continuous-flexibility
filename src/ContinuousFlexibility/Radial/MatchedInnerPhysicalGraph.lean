module

public import ContinuousFlexibility.Radial.MatchedInnerFiniteEquation
public import ContinuousFlexibility.Radial.MatchedInnerH1Traces
public import ContinuousFlexibility.Radial.InnerRadialPhysicalSchur
public import ContinuousFlexibility.Radial.MatchingGraphRepresentatives

/-!
# The actual finite Hilbert graph satisfies the frozen inner graph

The existing supported Hilbert realization is used without changing its
source or operator. Its finite weak equation gives the true modal equation;
regularity supplies a C¹ representative, and the actual H¹ traces prove
both Dirichlet endpoint values. The single scalar is retained at j = 2.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace BigOperators
open ContinuousFlexibility.Statements

theorem matchedInner_ae_restrict_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {s : Set ℝ}
    (hs : MeasurableSet s) (hcore : s ⊆ radialCore D) {f g : ℝ → ℝ} :
    f =ᵐ[(radialHilbertMeasure D).restrict s] g ↔
      f =ᵐ[volume.restrict s] g := by
  constructor
  · intro h
    have hv := (radialHilbertMeasure_ae_iff hD).mp (ae_imp_of_ae_restrict h)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hcore hv, ae_restrict_mem hs]
      with r hr hrs
    exact hr hrs
  · intro h
    have hμ := (radialHilbertMeasure_ae_iff hD).mpr
      (ae_restrict_of_ae (ae_imp_of_ae_restrict h))
    filter_upwards [ae_restrict_of_ae hμ, ae_restrict_mem hs] with r hr hrs
    exact hr hrs

theorem matchedInnerChain_piece_Icc_subset {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (p : Fin (n + 1)) :
    Icc (G.left p) (G.right p) ⊆ Icc (G.left 0) (G.right (Fin.last n)) := by
  intro r hr
  exact ⟨(G.increasing.monotone (show (0 : Fin (n + 1)).castSucc ≤ p.castSucc by
      change (0 : ℕ) ≤ p.val
      exact Nat.zero_le _)).trans hr.1,
    hr.2.trans (G.increasing.monotone (show p.succ ≤ (Fin.last n).succ by
      change p.val + 1 ≤ n + 1
      omega))⟩

theorem matchedInnerChain_piece_Ioo_subset {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (p : Fin (n + 1)) :
    Ioo (G.left p) (G.right p) ⊆ Ioo (G.left 0) (G.right (Fin.last n)) := by
  intro r hr
  exact ⟨(G.increasing.monotone (show (0 : Fin (n + 1)).castSucc ≤ p.castSucc by
      change (0 : ℕ) ≤ p.val
      exact Nat.zero_le _)).trans_lt hr.1,
    hr.2.trans_le (G.increasing.monotone (show p.succ ≤ (Fin.last n).succ by
      change p.val + 1 ≤ n + 1
      omega))⟩

theorem matchedInnerPhysicalSource_supported (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ innerRadialChainRegion D G → F.val.fst r = 0 := by
  have hfix := ((mem_innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) bordered F.val).mp F.property).2
  have h := innerL2PieceProjection_supported (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) F.val.fst
  rwa [hfix] at h

theorem matchedInnerPhysicalForcing_sum (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) :
    (∑ p, innerRadialPhysicalForcing D G bordered F p) = F.val.fst := by
  simp only [innerRadialPhysicalForcing_apply]
  exact innerL2PieceProjections_sum_eq (radialHilbertMeasure D)
    (fun p => Ioo (G.left p) (G.right p)) (fun _ => measurableSet_Ioo)
    (innerRadialChainPieces_disjoint D G) F.val.fst
    (matchedInnerPhysicalSource_supported D G bordered F)

theorem matchedInnerChain_sum_ae_piece {D : ReferenceData} {n : ℕ}
    (hw : Continuous D.w) (G : InnerRadialChainGeometry D n)
    {q : Fin (n + 1) → InnerRadialH1Pair D}
    (hq : q ∈ innerRadialChainDomain D hw G) (p : Fin (n + 1)) :
    (((∑ k, (q k).1) : RadialModeL2 D) : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict (Ioo (G.left p) (G.right p))] (q p).1 := by
  classical
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G q).mp hq
  have hz (k : Fin (n + 1)) :
      ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (G.left k) (G.right k) → (q k).1 r = 0 :=
    innerRadialH1Domain_supported D hw (G.left_pos k) (G.in_core k)
      (G.weight_pos k) (hξ k).1
  filter_upwards [ae_restrict_of_ae
      (Lp.coeFn_fun_finsetSum Finset.univ (fun k => (q k).1)),
    ae_restrict_of_ae (ae_all_iff.mpr hz), ae_restrict_mem measurableSet_Ioo]
      with r hsum hr hrp
  rw [hsum]
  apply Finset.sum_eq_single p
  · intro k _ hkp
    exact hr k (fun hrk =>
      Set.disjoint_left.mp (innerRadialChainPieces_disjoint D G hkp) hrk hrp)
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

/-- The actual physical H¹ graph implies the unchanged frozen Dirichlet
graph. The assumptions identify only the original geometry and column. -/
theorem matchedInnerPhysicalWeakGraph_to_modeGraph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (M : RadialMatchingData D)
    (hleft : M.innerLeft = G.left 0) (hright : M.innerRight = G.right (Fin.last n))
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hcolumn : column = matchingBorderVector D hD hB)
    (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left central) (G.right central)) column = column)
    {U F : InnerRadialPhysicalSource D G (decide (M.frequency = 2))}
    (hgraph : InnerRadialPhysicalWeakGraph D hw.continuous G
      (decide (M.frequency = 2)) (M.frequency : ℝ) central column U F) :
    ModeInnerDirichletGraph D M (U.val.fst, U.val.snd) (F.val.fst, F.val.snd) := by
  classical
  let bordered := decide (M.frequency = 2)
  let f := innerRadialPhysicalForcing D G bordered F
  obtain ⟨q, v, scalar, hU, hq⟩ :=
    (innerRadialPhysicalWeakGraph_iff D hw.continuous G bordered (M.frequency : ℝ)
      central column U F).mp hgraph
  have hUval : U.val.fst = ∑ p, (q p).1 := by
    simpa only [WithLp.toLp_fst] using congrArg (fun z : InnerBorderL2 (radialHilbertMeasure D) => z.fst) hU
  have hUscalar : U.val.snd = scalar := by
    simpa only [WithLp.toLp_snd] using congrArg (fun z : InnerBorderL2 (radialHilbertMeasure D) => z.snd) hU
  have hfsum : (∑ p, f p) = F.val.fst := matchedInnerPhysicalForcing_sum D G bordered F
  have hffix (p : Fin (n + 1)) :
      innerL2PieceProjection (radialHilbertMeasure D)
        (Ioo (G.left p) (G.right p)) (f p) = f p := by
    change innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left p) (G.right p))
      (innerL2PieceProjection (radialHilbertMeasure D)
        (Ioo (G.left p) (G.right p)) F.val.fst) = _
    apply innerL2PieceProjection_eq_self _ _ measurableSet_Ioo
    exact innerL2PieceProjection_supported _ _ measurableSet_Ioo _
  have hEq₀ := matchedInnerChainWeakGraph_equation hD hB hw G bordered M.frequency
    central column hcolumn hcolfix hffix hq
  change ModeLocalEquation D M.frequency (Ioo (G.left 0) (G.right (Fin.last n)))
    (∑ p, (q p).1, scalar) (∑ p, f p, F.val.snd) at hEq₀
  rw [hfsum, ← hUval, ← hUscalar] at hEq₀
  have hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
      (U.val.fst, U.val.snd) (F.val.fst, F.val.snd) := by
    simpa only [hleft, hright] using hEq₀
  have hrow₀ := matchedInnerChainWeakGraph_row hD hB hw.continuous G
    (innerRadialChainPieces_disjoint D G) M.frequency central column hcolumn hcolfix hq
  have hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.val.fst r) = F.val.snd
      else U.val.snd = 0 ∧ F.val.snd = 0 := by
    change (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r *
        (((∑ p, (q p).1) : RadialModeL2 D) : ℝ → ℝ) r) = F.val.snd
      else scalar = 0 ∧ F.val.snd = 0) at hrow₀
    simpa only [← hUval, ← hUscalar] using hrow₀
  have hm : M.innerLeft < M.innerRight := by
    rw [hleft, hright]
    exact G.increasing (show (0 : Fin (n + 1)).castSucc < (Fin.last n).succ by
      change (0 : ℕ) < n + 1
      exact Nat.zero_lt_succ n)
  obtain ⟨u, c, hu, hrep, _, _, _⟩ :=
    modeLocalEquation_contDiff_representative_on_compact hD hB hEq hm hsub (fun _ hr => hr)
  have hrep' : (((∑ p, (q p).1) : RadialModeL2 D) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo M.innerLeft M.innerRight)] u := by
    simpa only [hUval] using hrep
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw.continuous G q).mp hq.1
  have hpcore (p : Fin (n + 1)) : Icc (G.left p) (G.right p) ⊆ radialCore D := by
    have h := (matchedInnerChain_piece_Icc_subset G p).trans
      (show Icc (G.left 0) (G.right (Fin.last n)) ⊆ radialCore D by
        simpa only [hleft, hright] using hsub)
    exact h
  have hptrace (p : Fin (n + 1)) :
      u (G.left p) = innerChainBoundaryRestriction n p ξ 0 ∧
        u (G.right p) = innerChainBoundaryRestriction n p ξ 1 := by
    have hpopen : Ioo (G.left p) (G.right p) ⊆ Ioo M.innerLeft M.innerRight := by
      simpa only [hleft, hright] using matchedInnerChain_piece_Ioo_subset G p
    have hsum := (matchedInner_ae_restrict_iff hD measurableSet_Ioo (G.in_core p)).mp
      (matchedInnerChain_sum_ae_piece hw.continuous G hq.1 p)
    have hrepP : ((q p).1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (G.left p) (G.right p))] u :=
      hsum.symm.trans (ae_restrict_of_ae_restrict_of_subset hpopen hrep')
    have h := matchedInnerH1Domain_trace_of_representative hD hw.continuous
      (G.left_lt_right p) (G.left_pos p) (hpcore p) (G.weight_pos p)
      (hξ p).1 hu.continuous.continuousOn hrepP
    exact ⟨h.1.trans (congrFun (hξ p).2 0), h.2.trans (congrFun (hξ p).2 1)⟩
  have hua : u M.innerLeft = 0 := by
    rw [hleft, (hptrace 0).1, (innerChainBoundaryRestriction_outer n ξ).1]
  have hub : u M.innerRight = 0 := by
    rw [hright, (hptrace (Fin.last n)).2, (innerChainBoundaryRestriction_outer n ξ).2]
  have hrepμ : (U.val.fst : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] u :=
    (matchedInner_ae_restrict_iff hD measurableSet_Ioo
      (Ioo_subset_Icc_self.trans hsub)).mpr hrep
  have hout : (U.val.fst : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict (matchingOuterRegion D M)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae (matchedInnerPhysicalSource_supported D G bordered U),
      ae_restrict_mem (show MeasurableSet (matchingOuterRegion D M) from
        measurableSet_Ioo.union measurableSet_Ioo)] with r hr hrout
    apply hr
    intro hrin
    change r ∈ ⋃ p, Ioo (G.left p) (G.right p) at hrin
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hrin
    have hp' : r ∈ Ioo M.innerLeft M.innerRight := by
      rw [hleft, hright]
      exact matchedInnerChain_piece_Ioo_subset G p hp
    exact matchingOuterRegion_not_mem_inner hrout hp'
  exact matching_innerGraph_of_representative hD hm hEq hrow hrepμ hout
    hu.contDiffOn hua hub

end ContinuousFlexibility.Radial
