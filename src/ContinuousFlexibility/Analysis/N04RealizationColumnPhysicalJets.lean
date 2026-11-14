module

public import ContinuousFlexibility.Analysis.N04RealizationLeftColumnTower
public import ContinuousFlexibility.Analysis.N04RealizationNuColumnTower
public import ContinuousFlexibility.Analysis.N04RealizationHeightFieldJets

/-!
# One neighborhood for both actual physical columns

The left and distinguished columns are the actual fields of the same
supplied nonlinear witness. Their two uniform height towers are
restricted once to a common sector neighborhood and weakened to common
fixed orders. The choice precedes every spatial and parameter order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

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

/-- Combine two decoded uniform families over abstract graded spaces.
The common indices and radius are chosen before any derivative order. -/
private theorem n04Realization_uniformDecodedPair
    {X Y P : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (hp : Monotone p)
    (V : ℕ → ℝ → Set X) (hopen : ∀ b η, IsOpen (V b η))
    (hmono : ∀ b₀ b₁ η₀ η₁, b₀ ≤ b₁ → η₁ ≤ η₀ → V b₁ η₁ ⊆ V b₀ η₀)
    (base : ℕ) (ε : ℝ) (decode : Y → P → ℝ) (f g : X → P → ℝ)
    (hleft : ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ N : X → Y, FixedNeighborhoodSmoothTame p q (V b η) b ell N ∧
        ∀ x ∈ V b η, ∀ u, decode (N x) u = f x u)
    (hnu : ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ N : X → Y, FixedNeighborhoodSmoothTame p q (V b η) b ell N ∧
        ∀ x ∈ V b η, ∀ u, decode (N x) u = g x u) :
    ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ Nleft Nnu : X → Y,
        FixedNeighborhoodSmoothTame p q (V b η) b ell Nleft ∧
        FixedNeighborhoodSmoothTame p q (V b η) b ell Nnu ∧
        (∀ x ∈ V b η, decode (Nleft x) = f x) ∧
        (∀ x ∈ V b η, decode (Nnu x) = g x) := by
  obtain ⟨bL, ellL, ηL, hbL, hηL, hηLε, NL, hNL, hdecodeL⟩ := hleft
  obtain ⟨bN, ellN, ηN, _hbN, hηN, _hηNε, NN, hNN, hdecodeN⟩ := hnu
  let b : ℕ := max bL bN
  let ell : ℕ := max ellL ellN
  let η : ℝ := min ηL ηN
  have hUL : V b η ⊆ V bL ηL :=
    hmono _ _ _ _ (le_max_left _ _) (min_le_left _ _)
  have hUN : V b η ⊆ V bN ηN :=
    hmono _ _ _ _ (le_max_right _ _) (min_le_right _ _)
  refine ⟨b, ell, η, hbL.trans (le_max_left _ _), lt_min hηL hηN,
    (min_le_left _ _).trans hηLε, NL, NN, ?_, ?_, ?_, ?_⟩
  · exact (hNL.restrict (hopen b η) hUL).weaken hp (le_max_left _ _) (le_max_left _ _)
  · exact (hNN.restrict (hopen b η) hUN).weaken hp (le_max_right _ _) (le_max_right _ _)
  · intro x hx
    exact funext (hdecodeL x (hUL hx))
  · intro x hx
    exact funext (hdecodeN x (hUN hx))

/-- Both actual columns have uniform height towers on the same sector
neighborhood. Their decoded equalities hold on the entire physical
plane, so all physical mixed jets are retained as well. -/
theorem n04Realization_exists_uniformPhysicalColumns
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ Nleft Nnu : (StateDirections S × ℝ) → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b η η) b ell Nleft ∧
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b η η) b ell Nnu ∧
        (∀ z ∈ sectorNeighborhood S b η η,
          (S.height scalarBeta).decode (Nleft z) =
            n06CurrentLeftColumn S L (liftSectorParameter S C z)) ∧
        (∀ z ∈ sectorNeighborhood S b η η,
          (S.height scalarBeta).decode (Nnu z) =
            nuColumnField D S C (liftSectorParameter S C z)) := by
  exact n04Realization_uniformDecodedPair
    (X := StateDirections S × ℝ) (Y := ScalarHeightSpace S) (P := PolarPoint)
    (n07aParameterGrading S) (scalarHeightGrading S) (n07aParameterGrading_monotone S)
    (fun b η => sectorNeighborhood S b η η)
    (fun b η => isOpen_sectorNeighborhood S b η η)
    (fun _ _ _ _ hb hη => sectorNeighborhood_mono S hb hη hη)
    base ε (S.height scalarBeta).decode
    (fun z => n06CurrentLeftColumn S L (liftSectorParameter S C z))
    (fun z => nuColumnField D S C (liftSectorParameter S C z))
    (n04Realization_exists_uniformLeftColumn hS hT h01 h03)
    (n04Realization_exists_uniformNuColumn hS hT h01)

end ContinuousFlexibility.Analysis
