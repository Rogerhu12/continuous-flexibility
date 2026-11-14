module

public import ContinuousFlexibility.Analysis.N06PhysicalRepresentativeUniqueness
public import ContinuousFlexibility.Analysis.N06ControlledPieceFiniteness
public import ContinuousFlexibility.Analysis.N06NegativePieceFiniteness
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual finite partition of a compact physical test

The almost-everywhere cover and disjoint physical pieces are those of N04.
A compact radial support meets only finitely many current pieces: the
positive pieces retain their reference domains, and the two negative
halves stay in their original negative component. Piecewise integrability gives both
integrability on the physical test rectangle and its exact finite sum of
piece integrals. The angular set is arbitrary, so the same result covers
the measured half-period and the original full-period physical tests.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The actual state-dependent pieces meeting a physical radial support. -/
def n06PhysicalSupportPieces (K : CanonicalData S) (z : AnnularState S × ℝ)
    (J : Set ℝ) : Set ℕ :=
  {m | (physicalPieceOpen S K z m ∩ (J ×ˢ (univ : Set ℝ))).Nonempty}

/-- Positive pieces are fixed, while each moving negative half is
contained in its original component. These actual geometric facts imply
compact finiteness without imposing a radial shape on current cuts. -/
theorem n06_currentPieces_finite_on_compact
    (hD : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    (n06PhysicalSupportPieces K z J).Finite := by
  have hreference := n06_controlledReferencePieces_finite_on_compact hD hcoords hJ hJD
  have hnegative := n06_currentNegativePieces_finite_on_compact
    hD.choose_spec.1 hC h04 hz hs hJ hJD
  apply (hreference.union hnegative).subset
  intro m hm
  obtain ⟨p, hpm, hpJ⟩ := hm
  cases hpos : K.positive m with
  | false =>
      exact Or.inr ⟨hpos, p, subset_closure hpm, hpJ⟩
  | true =>
      have hdomain := (h04.1.domains z hz hs m).2.2.2.2.2.1 hpos
      rw [hdomain] at hpm
      exact Or.inl ⟨p.1, hpm.1, hpJ.1⟩

/-- The finite collection consists of exactly the actual physical
pieces meeting the stated radial support. No new partition is chosen. -/
theorem n06_finitePhysicalPartition_integral
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {J Q : Set ℝ} (hQ : MeasurableSet Q)
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {g : PolarPoint → ℝ}
    (hsupport : ∀ r, r ∉ J → ∀ θ, g (r, θ) = 0)
    (hint : ∀ m ∈ hfinite.toFinset,
      IntegrableOn g (physicalPieceOpen S K z m ∩ (univ ×ˢ Q))) :
    IntegrableOn g (radialCore D ×ˢ Q) ∧
      (∫ p in radialCore D ×ˢ Q, g p) =
        ∑ m ∈ hfinite.toFinset,
          ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Q), g p := by
  classical
  let I : Finset ℕ := hfinite.toFinset
  let P : ℕ → Set PolarPoint := fun m =>
    physicalPieceOpen S K z m ∩ (univ ×ˢ Q)
  let U : Set PolarPoint := ⋃ m ∈ I, P m
  let A : Set PolarPoint := radialCore D ×ˢ Q
  have hA : MeasurableSet A := measurableSet_Ioo.prod hQ
  have hP (m : ℕ) : MeasurableSet (P m) :=
    (h04.1.domains z hz hs m).1.measurableSet.inter (MeasurableSet.univ.prod hQ)
  have hsub : U ⊆ A := by
    intro p hp
    obtain ⟨m, _, hm⟩ := mem_iUnion₂.mp hp
    exact ⟨((h04.1.domains z hz hs m).2.2.1 hm.1).1, hm.2.2⟩
  have hAannular : A ⊆ annularOpen D := fun _ hp => ⟨hp.1, mem_univ _⟩
  have hcover : ∀ᵐ p ∂volume, p ∈ A → ∃ m, p ∈ physicalPieceOpen S K z m := by
    apply (ae_restrict_iff' hA).mp
    exact ae_restrict_of_ae_restrict_of_subset hAannular
      (n06_physical_piece_cover_ae h04 hz hs)
  have hzero : ∀ᵐ p ∂volume, p ∈ A \ U → g p = 0 := by
    filter_upwards [hcover] with p hp hdiff
    by_cases hr : p.1 ∈ J
    · obtain ⟨m, hm⟩ := hp hdiff.1
      have hmI : m ∈ I := hfinite.mem_toFinset.mpr ⟨p, hm, hr, mem_univ _⟩
      exact False.elim (hdiff.2 (mem_iUnion₂.mpr ⟨m, hmI, hm, mem_univ _, hdiff.1.2⟩))
    · exact hsupport p.1 hr p.2
  have hIU : IntegrableOn g U := integrableOn_finset_iUnion.mpr hint
  have hdisjoint : Set.Pairwise (↑I) (fun m n => Disjoint (P m) (P n)) := by
    intro m _ n _ hmn
    apply Set.disjoint_left.mpr
    intro p hpm hpn
    exact Set.disjoint_left.mp
      (n06_currentPhysicalPiece_pairwiseDisjoint h04 hz hs hmn) hpm.1 hpn.1
  refine ⟨hIU.of_ae_sdiff_eq_zero hA.nullMeasurableSet hzero, ?_⟩
  calc
    (∫ p in A, g p) = ∫ p in U, g p :=
      setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hA.nullMeasurableSet hsub hzero
    _ = _ := integral_biUnion_finset I (fun m _ => hP m) hdisjoint hint

/-- The original accumulating profile and controlled atlas supply the
finite set for every actual compact radial support. -/
theorem n06_controlledPhysicalPartition_integral
    (hD : IsAccumulatingProfile D)
    (hC : controlGeometryConditions D S C)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {J Q : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D)
    (hQ : MeasurableSet Q) {g : PolarPoint → ℝ}
    (hsupport : ∀ r, r ∉ J → ∀ θ, g (r, θ) = 0)
    (hint : ∀ m, IntegrableOn g
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Q))) :
    IntegrableOn g (radialCore D ×ˢ Q) ∧
      ∃ I : Finset ℕ,
        (∀ m, m ∈ I ↔ m ∈ n06PhysicalSupportPieces K z J) ∧
        (∫ p in radialCore D ×ˢ Q, g p) =
          ∑ m ∈ I, ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Q), g p := by
  classical
  have hfinite := n06_currentPieces_finite_on_compact hD hC hcoords h04 hz hs hJ hJD
  have h := n06_finitePhysicalPartition_integral h04 hz hs hQ hfinite hsupport
    (fun m _ => hint m)
  exact ⟨h.1, hfinite.toFinset, fun _ => hfinite.mem_toFinset, h.2⟩

end ContinuousFlexibility.Statements
