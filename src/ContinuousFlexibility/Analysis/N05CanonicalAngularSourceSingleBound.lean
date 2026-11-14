module

public import ContinuousFlexibility.Analysis.N05CanonicalAngularSourceBlock
public import ContinuousFlexibility.Analysis.N05CanonicalSourceSingle

/-!
# Same-endpoint bounds for the fixed unsigned single-coordinate lift

The fixed global angular lift agrees almost everywhere with its actual
local periodic transport. Cell integrals transfer that identity to the
original reference source norm, without an angular parity assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory

theorem n05_canonicalAngularLift_single_reference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ m (u : CanonicalL2 S K m),
      SourceDerivativeMember D γ M
        (n05CanonicalAngularLift S C K (Pi.single m u)) ∧
      sourceNormSquare D γ M
        (n05CanonicalAngularLift S C K (Pi.single m u), 0) ≤
          C0 * radialE (D.cellIndex (K.cell m)) ^ A *
            Real.exp (2 * γ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨C0, A, hC0, hA, hblock⟩ :=
    n05_canonicalAngularSourceBlock_reference_bound hD hT h hcoordinates hγ M
  refine ⟨C0, A, hC0, hA, fun m u => ?_⟩
  obtain ⟨hb, hbound⟩ := hblock m u
  have hae := n05CanonicalAngularLift_single_ae h hcoordinates m u
    (n05CanonicalPeriodicRepresentative S K m u)
    (n05CanonicalPeriodicRepresentative_periodic S K m u)
    (n05CanonicalPeriodicRepresentative_ae S K m u).symm
  have hc : RadialCellIntegrable D (n05CanonicalAngularLift S C K (Pi.single m u)) :=
    RadialCellIntegrable.congr_ae hb.1 hae.symm
  have hsq (j : ℕ) :
      sourceCellSquare D γ M (n05CanonicalAngularLift S C K (Pi.single m u)) j =
        sourceCellSquare D γ M (n05CanonicalAngularTransport S C K m
          (n05CanonicalPeriodicRepresentative S K m u)) j := by
    unfold sourceCellSquare
    rw [referenceCellSquare_congr_ae hD.choose_spec.1.2.1.le j hc hae]
  have hsum : Summable
      (sourceCellSquare D γ M (n05CanonicalAngularLift S C K (Pi.single m u))) :=
    hb.2.congr (fun j => (hsq j).symm)
  refine ⟨⟨hc, hsum⟩, ?_⟩
  have hnorm : sourceNormSquare D γ M
        (n05CanonicalAngularLift S C K (Pi.single m u), 0) =
      sourceNormSquare D γ M (n05CanonicalAngularTransport S C K m
        (n05CanonicalPeriodicRepresentative S K m u), 0) := by
    unfold sourceNormSquare
    rw [tsum_congr hsq]
  exact hnorm.le.trans hbound

end ContinuousFlexibility.Statements
