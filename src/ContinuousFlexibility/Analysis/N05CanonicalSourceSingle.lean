import ContinuousFlexibility.Analysis.N05CanonicalSourceBlock
import ContinuousFlexibility.Radial.ReferenceCellL2

/-!
# The actual single-coordinate source of the fixed lift

The radial source block represents exactly the single even canonical
coordinate. Its identification with the fixed global lift is an equality
of physical almost-everywhere classes, not an assertion about pointwise
linearity of chosen L² representatives. The same endpoint estimate then
holds for that literal global lift, without a volume-membership premise.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- For an arbitrary canonical coordinate the fixed lift represents its
actual even projection. No symmetry is assumed on the input class. -/
theorem n05CanonicalSourceLift_projected_source_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (F : CanonicalSequence S K) (k : ℕ) :
    (n05CanonicalEvenProjection S K k (F k) : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K k]
        canonicalSource S K (C.referenceState, 0) k
          (n05CanonicalSourceLift S C K F) := by
  have he := (n05CanonicalEvenProjection_ae S K k (F k)).trans
    (n05CanonicalEvenPeriodicRepresentative_ae_average S K k (F k)).symm
  filter_upwards [he, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
    with p hp hpm
  exact hp.trans (n05CanonicalSourceLift_canonicalSource h hcoordinates F k
    ⟨hpm.1, mem_univ _⟩).symm

/-- The true inverse chart sees the chosen source block on its own piece
and zero on every other piece, by actual physical disjointness. -/
theorem n05CanonicalSourceBlock_canonicalSource
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m k : ℕ) (u : CanonicalL2 S K m) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K k) :
    canonicalSource S K (C.referenceState, 0) k
        (n05CanonicalSourceBlock S C K m u) p =
      if k = m then n05CanonicalEvenPeriodicRepresentative S K m u p else 0 := by
  classical
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, hΨ, _, hright, _, _, _, hnonzero⟩ :=
    hcharts (C.referenceState, 0) hz hs k
  have hx := hΨ hp
  by_cases hkm : k = m
  · subst k
    rw [ite_eq_left rfl]
    have hn := hnonzero _ hx
    change K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) *
        n05CanonicalSourceBlock S C K m u (K.inverseChart (C.referenceState, 0) m p) /
          |planeJacobian (K.chart (C.referenceState, 0) m)
            (K.inverseChart (C.referenceState, 0) m p)| = _
    rw [n05CanonicalSourceBlock, ite_eq_left hx.1,
      n05CanonicalSourcePieceLift_eq_actual h hcoordinates m u hx, hright p hp]
    field_simp [hn.1.ne', abs_ne_zero.mpr hn.2.1] <;> ring
  · have hnot : (K.inverseChart (C.referenceState, 0) k p).1 ∉
        Ioo (K.physicalLeft m) (K.physicalRight m) := by
      intro hm
      exact Set.disjoint_left.mp (n05_physicalPieces_pairwise_disjoint h.2.2.2.2 hkm)
        hx.1 hm
    simp only [canonicalSource, n05CanonicalSourceBlock, ite_eq_right hnot,
      ite_eq_right hkm, mul_zero, zero_div]

/-- The block has precisely one nonzero canonical L² class. The zero
classes on the other pieces are handled almost everywhere. -/
theorem n05CanonicalSourceBlock_source_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (u : CanonicalL2 S K m) (k : ℕ) :
    ((Pi.single m (n05CanonicalEvenProjection S K m u) : CanonicalSequence S K) k :
      PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K k]
        canonicalSource S K (C.referenceState, 0) k
          (n05CanonicalSourceBlock S C K m u) := by
  classical
  by_cases hkm : k = m
  · subst k
    simp only [Pi.single_eq_same]
    have he := (n05CanonicalEvenProjection_ae S K m u).trans
      (n05CanonicalEvenPeriodicRepresentative_ae_average S K m u).symm
    filter_upwards [he, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
      with p hp hpm
    have hc := n05CanonicalSourceBlock_canonicalSource h hcoordinates m m u
      (show p ∈ canonicalOpen S K m from ⟨hpm.1, mem_univ _⟩)
    rw [ite_eq_left rfl] at hc
    exact hp.trans hc.symm
  · have hz : ((Pi.single m (n05CanonicalEvenProjection S K m u) :
          CanonicalSequence S K) k : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K k] (fun _ => 0) := by
      rw [Pi.single_eq_of_ne hkm]
      exact Lp.coeFn_zero ℝ 2 (canonicalMeasure S K k)
    filter_upwards [hz, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
      with p hp hpm
    have hc := n05CanonicalSourceBlock_canonicalSource h hcoordinates m k u
      (show p ∈ canonicalOpen S K k from ⟨hpm.1, mem_univ _⟩)
    rw [ite_eq_right hkm] at hc
    exact hp.trans hc.symm

/-- The global choice on a single raw canonical coordinate is the actual
localized source block in the frozen full-period physical measure. -/
theorem n05CanonicalSourceLift_single_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalSourceLift S C K (Pi.single m u)
      =ᵐ[radialPhysicalMeasure D] n05CanonicalSourceBlock S C K m u := by
  classical
  apply n05_referenceCanonicalSource_ae_physical h hcoordinates
    (n05CanonicalSourceLift_periodic S C K (Pi.single m u))
    (n05CanonicalSourceBlock_periodic S C K m u)
  intro k
  have hproject : n05CanonicalEvenProjection S K k
        ((Pi.single m u : CanonicalSequence S K) k) =
      (Pi.single m (n05CanonicalEvenProjection S K m u) : CanonicalSequence S K) k := by
    by_cases hkm : k = m
    · subst k
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hkm, map_zero]
  have hlift := n05CanonicalSourceLift_projected_source_ae h hcoordinates (Pi.single m u) k
  rw [hproject] at hlift
  exact hlift.symm.trans (n05CanonicalSourceBlock_source_ae h hcoordinates m u k)

/-- The literal single-coordinate global lift inherits the source block's
same endpoint exponent and the same fixed material exponent. The constants
precede the piece and arbitrary L² input; no volume membership is used. -/
theorem n05_canonicalSourceLift_single_reference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ m (u : CanonicalL2 S K m),
      SourceDerivativeMember D γ M
        (n05CanonicalSourceLift S C K (Pi.single m u)) ∧
      sourceNormSquare D γ M
        (n05CanonicalSourceLift S C K (Pi.single m u), 0) ≤
          C0 * radialE (D.cellIndex (K.cell m)) ^ A *
            Real.exp (2 * γ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨C0, A, hC0, hA, hblock⟩ :=
    n05_canonicalSourceBlock_reference_bound hD hT h hcoordinates hγ M
  refine ⟨C0, A, hC0, hA, fun m u => ?_⟩
  obtain ⟨hb, hbound⟩ := hblock m u
  have hae := n05CanonicalSourceLift_single_ae h hcoordinates m u
  have hc : RadialCellIntegrable D (n05CanonicalSourceLift S C K (Pi.single m u)) :=
    RadialCellIntegrable.congr_ae hb.1 hae.symm
  have hsq (j : ℕ) :
      sourceCellSquare D γ M (n05CanonicalSourceLift S C K (Pi.single m u)) j =
        sourceCellSquare D γ M (n05CanonicalSourceBlock S C K m u) j := by
    unfold sourceCellSquare
    rw [referenceCellSquare_congr_ae hD.choose_spec.1.2.1.le j hc hae]
  have hsum : Summable
      (sourceCellSquare D γ M (n05CanonicalSourceLift S C K (Pi.single m u))) :=
    hb.2.congr (fun j => (hsq j).symm)
  refine ⟨⟨hc, hsum⟩, ?_⟩
  have hnorm : sourceNormSquare D γ M
        (n05CanonicalSourceLift S C K (Pi.single m u), 0) =
      sourceNormSquare D γ M (n05CanonicalSourceBlock S C K m u, 0) := by
    unfold sourceNormSquare
    rw [tsum_congr hsq]
  exact hnorm.le.trans hbound

end ContinuousFlexibility.Statements
