import ContinuousFlexibility.Analysis.N05CanonicalAngularTransport
import ContinuousFlexibility.Analysis.N05CanonicalSmoothJets

/-!
# Unsigned actual representatives for canonical angular jets

Every coordinate is periodically extended without reflection averaging.
The actual radial chart and source multiplier then assemble its physical
representative. This preserves odd angular jets and identifies smooth
single-coordinate jets with their genuine transported derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05CanonicalAngularLift (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (F : CanonicalSequence S K) : PolarPoint → ℝ := by
  classical
  exact fun p => if ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m) then
    n05CanonicalAngularTransport S C K (n05PhysicalPieceIndex S K p.1)
      (n05CanonicalPeriodicRepresentative S K (n05PhysicalPieceIndex S K p.1)
        (F (n05PhysicalPieceIndex S K p.1))) p
    else 0

theorem n05CanonicalAngularLift_periodic (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (F : CanonicalSequence S K) :
    Function.Periodic (n05CanonicalAngularLift S C K F) (0, Real.pi) := by
  classical
  rintro ⟨r, θ⟩
  change n05CanonicalAngularLift S C K F (r + 0, θ + Real.pi) =
    n05CanonicalAngularLift S C K F (r, θ)
  rw [add_zero]
  unfold n05CanonicalAngularLift
  split_ifs
  · simpa only [Prod.mk_add_mk, add_zero] using
      (n05CanonicalAngularTransport_periodic S C K (n05PhysicalPieceIndex S K r)
        (n05CanonicalPeriodicRepresentative_periodic S K (n05PhysicalPieceIndex S K r)
          (F (n05PhysicalPieceIndex S K r))) (r, θ))
  · rfl

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
theorem n05CanonicalAngularTransport_canonicalSource (m k : ℕ) (φ : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K k) :
    canonicalSource S K (C.referenceState, 0) k
      (n05CanonicalAngularTransport S C K m φ) p = if k = m then φ p else 0 := by
  classical
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, hΨ, _, hright, _, _, _, hn⟩ := hcharts (C.referenceState, 0) hz hs k
  have hx := hΨ hp
  by_cases hkm : k = m
  · subst k
    rw [if_pos rfl]
    change K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) *
      n05CanonicalAngularTransport S C K m φ (K.inverseChart (C.referenceState, 0) m p) /
        |planeJacobian (K.chart (C.referenceState, 0) m)
          (K.inverseChart (C.referenceState, 0) m p)| = _
    rw [n05CanonicalAngularTransport_eq_actual h hcoordinates m φ hx, hright p hp]
    field_simp [(hn _ hx).1.ne', abs_ne_zero.mpr (hn _ hx).2.1] <;> ring
  · have hnot : (K.inverseChart (C.referenceState, 0) k p).1 ∉
        Ioo (K.physicalLeft m) (K.physicalRight m) := by
      intro hm
      exact Set.disjoint_left.mp (n05_physicalPieces_pairwise_disjoint h.2.2.2.2 hkm)
        hx.1 hm
    simp only [canonicalSource, n05CanonicalAngularTransport, if_neg hnot,
      if_neg hkm, mul_zero, zero_div]

include h in
theorem n05CanonicalAngularLift_eq_piece (F : CanonicalSequence S K) (m : ℕ)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n05CanonicalAngularLift S C K F p = n05CanonicalAngularTransport S C K m
      (n05CanonicalPeriodicRepresentative S K m (F m)) p := by
  classical
  have hi : n05PhysicalPieceIndex S K p.1 = m :=
    n05PhysicalPieceIndex_eq h.2.2.2.2 hp.1
  simp only [n05CanonicalAngularLift, if_pos (show ∃ k,
    p.1 ∈ Ioo (K.physicalLeft k) (K.physicalRight k) from ⟨m, hp.1⟩)]
  rw [hi]

include h hcoordinates in
/-- Every input class is recovered, including an odd derivative class. -/
theorem n05CanonicalAngularLift_source_ae (F : CanonicalSequence S K) (m : ℕ) :
    (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m (n05CanonicalAngularLift S C K F) := by
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  have hΨ := (hcharts (C.referenceState, 0) hz hs m).2.1
  filter_upwards [n05CanonicalPeriodicRepresentative_ae S K m (F m),
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
  have hpo : p ∈ canonicalOpen S K m := ⟨hpm.1, mem_univ _⟩
  have he := n05CanonicalAngularTransport_canonicalSource h hcoordinates m m
    (n05CanonicalPeriodicRepresentative S K m (F m)) hpo
  rw [if_pos rfl] at he
  refine hp.symm.trans (he.symm.trans ?_)
  simp only [canonicalSource, n05CanonicalAngularLift_eq_piece h F m (hΨ hpo)]

include h hcoordinates in
/-- The zero-order representative agrees with the already fixed source
selection on its actual reflection-fixed domain. -/
theorem n05CanonicalAngularLift_eq_sourceLift_ae (F : CanonicalSequence S K)
    (hF : ∀ m, (fun p : PolarPoint => F m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (F m : PolarPoint → ℝ)) :
    n05CanonicalAngularLift S C K F =ᵐ[radialPhysicalMeasure D]
      n05CanonicalSourceLift S C K F := by
  apply n05_referenceCanonicalSource_ae_physical h hcoordinates
    (n05CanonicalAngularLift_periodic S C K F) (n05CanonicalSourceLift_periodic S C K F)
  intro m
  exact (n05CanonicalAngularLift_source_ae h hcoordinates F m).symm.trans
    (n05CanonicalSourceLift_source_ae h hcoordinates F hF m)

include h hcoordinates in
theorem n05CanonicalAngularLift_linear_combination_ae
    (F H : CanonicalSequence S K) (c d : ℝ) :
    n05CanonicalAngularLift S C K (c • F + d • H) =ᵐ[radialPhysicalMeasure D]
      (fun p => c * n05CanonicalAngularLift S C K F p +
        d * n05CanonicalAngularLift S C K H p) := by
  refine n05_referenceCanonicalSource_ae_physical h hcoordinates
    (n05CanonicalAngularLift_periodic S C K _) ?_ ?_
  · intro p
    change c * n05CanonicalAngularLift S C K F (p + (0, Real.pi)) +
      d * n05CanonicalAngularLift S C K H (p + (0, Real.pi)) =
        c * n05CanonicalAngularLift S C K F p + d * n05CanonicalAngularLift S C K H p
    rw [n05CanonicalAngularLift_periodic S C K F p,
      n05CanonicalAngularLift_periodic S C K H p]
  · intro m
    filter_upwards [n05CanonicalAngularLift_source_ae h hcoordinates (c • F + d • H) m,
      n05CanonicalAngularLift_source_ae h hcoordinates F m,
      n05CanonicalAngularLift_source_ae h hcoordinates H m,
      Lp.coeFn_add (c • F m) (d • H m), Lp.coeFn_smul c (F m), Lp.coeFn_smul d (H m)]
      with p hsum hf hg ha hc hd
    rw [← hsum]
    change (c • F m + d • H m) p = _
    rw [ha]
    simp only [Pi.add_apply, hc, hd, Pi.smul_apply, smul_eq_mul]
    rw [hf, hg]
    simp only [canonicalSource]
    ring

include h hcoordinates in
theorem n05CanonicalAngularLift_sub_ae (F H : CanonicalSequence S K) :
    n05CanonicalAngularLift S C K (F - H) =ᵐ[radialPhysicalMeasure D]
      (fun p => n05CanonicalAngularLift S C K F p - n05CanonicalAngularLift S C K H p) := by
  simpa only [one_smul, neg_one_smul, sub_eq_add_neg, one_mul, neg_one_mul] using
    n05CanonicalAngularLift_linear_combination_ae h hcoordinates F H 1 (-1)

include h hcoordinates in
/-- A single actual periodic coordinate agrees with its smooth physical
transport; the statement has no evenness requirement. -/
theorem n05CanonicalAngularLift_single_ae (m : ℕ) (u : CanonicalL2 S K m)
    (φ : PolarPoint → ℝ) (hφ : Function.Periodic φ (0, Real.pi))
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] φ) :
    n05CanonicalAngularLift S C K (Pi.single m u) =ᵐ[radialPhysicalMeasure D]
      n05CanonicalAngularTransport S C K m φ := by
  classical
  apply n05_referenceCanonicalSource_ae_physical h hcoordinates
    (n05CanonicalAngularLift_periodic S C K _) (n05CanonicalAngularTransport_periodic S C K m hφ)
  intro k
  refine (n05CanonicalAngularLift_source_ae h hcoordinates (Pi.single m u) k).symm.trans ?_
  by_cases hkm : k = m
  · subst k
    simp only [Pi.single_eq_same]
    filter_upwards [hu, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have he := n05CanonicalAngularTransport_canonicalSource h hcoordinates m m φ
      (show p ∈ canonicalOpen S K m from ⟨hpm.1, mem_univ _⟩)
    rw [if_pos rfl] at he
    exact hp.trans he.symm
  · have hz : ((Pi.single m u : CanonicalSequence S K) k : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K k] (fun _ => 0) := by
      rw [Pi.single_eq_of_ne hkm]
      exact Lp.coeFn_zero ℝ 2 (canonicalMeasure S K k)
    filter_upwards [hz, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have he := n05CanonicalAngularTransport_canonicalSource h hcoordinates m k φ
      (show p ∈ canonicalOpen S K k from ⟨hpm.1, mem_univ _⟩)
    rw [if_neg hkm] at he
    exact hp.trans he.symm

include h hcoordinates in
theorem n05CanonicalAngularLift_smooth_single_ae (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : Function.Periodic φ (0, Real.pi)) (j : ℕ) :
    n05CanonicalAngularLift S C K (Pi.single m (n05CanonicalSmoothJet S K m hφ j))
      =ᵐ[radialPhysicalMeasure D]
        n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ) := by
  apply n05CanonicalAngularLift_single_ae h hcoordinates m _ _ ?_
    (n05CanonicalSmoothJet_ae S K m hφ j)
  have hper (r : ℝ) : Function.Periodic (fun θ => φ (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hp (r, θ)
  rintro ⟨r, θ⟩
  simpa only [Prod.mk_add_mk, add_zero] using
    mixedDerivative_angular_periodic hper 0 j r θ

end ContinuousFlexibility.Statements
