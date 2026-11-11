import ContinuousFlexibility.Analysis.N05CanonicalPeriodicRepresentative
import ContinuousFlexibility.Analysis.N05PhysicalPieces
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange

/-!
# The actual physical lift of a canonical source

The same fixed representative is pulled back by the true reference chart
and multiplied by its genuine source-conversion factor. Disjoint physical
pieces give a single function, defined independently of the source weight
or angular order. Its angular symmetries hold pointwise, and its canonical
source transform recovers every source in an actual volume level.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

/-- The local source formula uses only radial chart and height data; hence
its angular symmetries hold at every point, without a smooth representative. -/
def n05CanonicalSourcePieceLift (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (u : CanonicalL2 S K m) (p : PolarPoint) : ℝ :=
  |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1| /
      K.height (C.referenceState, 0) m (p.1, 0) *
    n05CanonicalEvenPeriodicRepresentative S K m u
      ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2)

theorem n05CanonicalSourcePieceLift_periodic (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (u : CanonicalL2 S K m) :
    Function.Periodic (n05CanonicalSourcePieceLift S C K m u) (0, Real.pi) := by
  intro p
  have hp := n05CanonicalEvenPeriodicRepresentative_periodic S K m u
    ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2)
  simp only [Prod.mk_add_mk, add_zero] at hp
  simp only [n05CanonicalSourcePieceLift, Prod.fst_add, Prod.snd_add, add_zero, hp]

theorem n05CanonicalSourcePieceLift_even (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (u : CanonicalL2 S K m) (r : ℝ) :
    Function.Even (fun θ => n05CanonicalSourcePieceLift S C K m u (r, θ)) := by
  intro θ
  dsimp only [n05CanonicalSourcePieceLift]
  exact congrArg (fun x : ℝ =>
    |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) r| /
      K.height (C.referenceState, 0) m (r, 0) * x)
    (n05CanonicalEvenPeriodicRepresentative_even S K m u
      ((K.chart (C.referenceState, 0) m (r, 0)).1) θ)

/-- A single physical source selection on all canonical sequences. Its
definition is independent of the volume level witnessing membership. -/
def n05CanonicalSourceLift (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (F : CanonicalSequence S K) : PolarPoint → ℝ := by
  classical
  exact fun p =>
    if ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m) then
      n05CanonicalSourcePieceLift S C K (n05PhysicalPieceIndex S K p.1)
        (F (n05PhysicalPieceIndex S K p.1)) p
    else 0

theorem n05CanonicalSourceLift_periodic (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (F : CanonicalSequence S K) :
    Function.Periodic (n05CanonicalSourceLift S C K F) (0, Real.pi) := by
  classical
  rintro ⟨r, θ⟩
  simp only [Prod.mk_add_mk, add_zero, n05CanonicalSourceLift]
  split_ifs
  · simpa only [Prod.mk_add_mk, add_zero] using
      (n05CanonicalSourcePieceLift_periodic S C K (n05PhysicalPieceIndex S K r)
        (F (n05PhysicalPieceIndex S K r)) (r, θ))
  · rfl

theorem n05CanonicalSourceLift_even (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (F : CanonicalSequence S K)
    (r : ℝ) : Function.Even (fun θ => n05CanonicalSourceLift S C K F (r, θ)) := by
  classical
  intro θ
  simp only [n05CanonicalSourceLift]
  split_ifs
  · exact n05CanonicalSourcePieceLift_even S C K _ _ r θ
  · rfl

theorem n05CanonicalSourceLift_eq_piece
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) (F : CanonicalSequence S K)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n05CanonicalSourceLift S C K F p = n05CanonicalSourcePieceLift S C K m (F m) p := by
  classical
  have hi : n05PhysicalPieceIndex S K p.1 = m := n05PhysicalPieceIndex_eq h04 hp.1
  simp only [n05CanonicalSourceLift, if_pos (show ∃ n,
    p.1 ∈ Ioo (K.physicalLeft n) (K.physicalRight n) from ⟨m, hp.1⟩)]
  rw [hi]

/-- The local selection is exactly the inverse of the frozen source
multiplier, using the actual Jacobian of the actual controlled chart. -/
theorem n05CanonicalSourcePieceLift_eq_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (u : CanonicalL2 S K m) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n05CanonicalSourcePieceLift S C K m u p =
      |planeJacobian (K.chart (C.referenceState, 0) m) p| *
        n05CanonicalEvenPeriodicRepresentative S K m u
          (K.chart (C.referenceState, 0) m p) /
        K.height (C.referenceState, 0) m p := by
  rw [n05CanonicalSourcePieceLift,
    n05_reference_planeJacobian_radial h hcoordinates m hp,
    (hcoordinates.1 m p hp).1, (hcoordinates.1 m p hp).2]
  ring

/-- On the canonical open rectangle the source transform recovers the
fixed representative pointwise; only its identification with an L² class
uses an almost-everywhere statement. -/
theorem n05CanonicalSourceLift_canonicalSource
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (F : CanonicalSequence S K) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K (C.referenceState, 0) m (n05CanonicalSourceLift S C K F) p =
      n05CanonicalEvenPeriodicRepresentative S K m (F m) p := by
  have h01 := h.1.1.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs : stateSector S C.referenceState :=
    n05_referenceState_sector h01.2.2.1
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, hΨ, _, hright, _, _, _, hnonzero⟩ :=
    hcharts (C.referenceState, 0) hz hs m
  have hx := hΨ hp
  have hn := hnonzero _ hx
  change K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) *
      n05CanonicalSourceLift S C K F (K.inverseChart (C.referenceState, 0) m p) /
        |planeJacobian (K.chart (C.referenceState, 0) m)
          (K.inverseChart (C.referenceState, 0) m p)| = _
  rw [n05CanonicalSourceLift_eq_piece h.2.2.2.2 F m hx,
    n05CanonicalSourcePieceLift_eq_actual h hcoordinates m (F m) hx, hright p hp]
  field_simp [hn.1.ne', abs_ne_zero.mpr hn.2.1] <;> ring

/-- The actual physical lift represents the given canonical sequence,
provided precisely the zero-order symmetry of the frozen volume graph. -/
theorem n05CanonicalSourceLift_source_ae
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (F : CanonicalSequence S K)
    (hF : ∀ m, (fun p : PolarPoint => F m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (F m : PolarPoint → ℝ)) (m : ℕ) :
    (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m (n05CanonicalSourceLift S C K F) := by
  filter_upwards [n05CanonicalEvenPeriodicRepresentative_ae (F m) (hF m),
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
  exact hp.symm.trans (n05CanonicalSourceLift_canonicalSource h hcoordinates F m
    ⟨hpm.1, mem_univ _⟩).symm

/-- Every actual source level uses this one lift. There is no independently
assumed existence of a physical representative. -/
theorem n05_volumeMember_physicalSourceLift
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss : ℕ} {ε γ t : ℝ} {s : ℕ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) {F : CanonicalSequence S K}
    (hF : VolumeMember S K V γ t s F) :
    Function.Periodic (n05CanonicalSourceLift S C K F) (0, Real.pi) ∧
      (∀ r θ, n05CanonicalSourceLift S C K F (r, -θ) =
        n05CanonicalSourceLift S C K F (r, θ)) ∧
      ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n05CanonicalSourceLift S C K F) :=
  ⟨n05CanonicalSourceLift_periodic S C K F,
    fun r θ => n05CanonicalSourceLift_even S C K F r θ,
    n05CanonicalSourceLift_source_ae h hcoordinates F
      (n05_volumeMember_reflection hV hF)⟩

end ContinuousFlexibility.Statements
