module

public import ContinuousFlexibility.Analysis.N04PulledFieldsSpatial
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeMaterialSamples

/-!
# The actual sample and moving inverse point belong to the same piece

The existing material comparison is instantiated on the original gauge
before any auxiliary-column replacement. Replacement preserves the
physical domains, stored cells and sample points. Its one constant thus
works for every auxiliary column and every actual pulled point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- The actual inverse chart returns to the same physical piece, before
forgetting the piece label and passing to the whole annulus. -/
theorem n04PulledFields_pulledPoint_mem_physicalPiece
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    (m : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.pulledPoint η (G.lift η z) m q ∈
      physicalPieceOpen (G.S η) (G.V η) (G.lift η z) m := by
  have hg := n04PulledFields_admissible_geometry G η hadm
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := G.C η) hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  exact (hg.charts _ hzstate hs m).2.1
    (n04PulledFields_unitPoint_mapsTo G η hadm m hq)

/-- The original gauge's one-sided sample displacement remains uniform
before all auxiliary columns, states, pieces and physical points. -/
theorem n04PulledFields_sample_endpointX (G : N04RealizationGauge) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      ∀ w : AnnularState (G.S η) × ℝ, ∀ m p,
      p ∈ physicalPieceOpen (G.S η) (G.V η) w m →
        p.1 ∈ Ioo G.W.D.a G.W.D.b ∧
        endpointX 1 (Statements.endpointDistance G.W.D
          (G.W.U.sample ((G.V η).cell m))) ≤
          endpointX 1 (Statements.endpointDistance G.W.D p.1) + A := by
  have h := n04WholeReferenceGauge_sample_endpointX (e₀ := G.X.e₀) (e := G.e)
    (τ := G.τ) (σ := G.σ) (Q := G.Q) (N := G.N)
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.cell G.X.cell_mem
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i)) (fun i p => G.H i p.1)
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  intro η w m p hp
  exact h.choose_spec.2 w m p hp

/-- The one constant selected for the original gauge controls each
actual inverse point in its actual piece, uniformly before `η`. -/
theorem n04PulledFields_pulledPoint_sample_endpointX
    (G : N04RealizationGauge) {base : ℕ} {ε : ℝ}
    (hadm : G.Admissible base ε) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      ∀ z ∈ sectorNeighborhood (G.S η) base ε ε, ∀ m q, q ∈ unitStrip →
        (G.pulledPoint η (G.lift η z) m q).1 ∈ Ioo G.W.D.a G.W.D.b ∧
        endpointX 1 (Statements.endpointDistance G.W.D
          (G.W.U.sample ((G.V η).cell m))) ≤
          endpointX 1 (Statements.endpointDistance G.W.D
            (G.pulledPoint η (G.lift η z) m q).1) + A := by
  have h := n04PulledFields_sample_endpointX G
  refine ⟨h.choose, h.choose_spec.1, fun η z hz m q hq => ?_⟩
  exact h.choose_spec.2 η (G.lift η z) m (G.pulledPoint η (G.lift η z) m q)
    (n04PulledFields_pulledPoint_mem_physicalPiece G η hadm hz m hq)

end ContinuousFlexibility.Analysis
