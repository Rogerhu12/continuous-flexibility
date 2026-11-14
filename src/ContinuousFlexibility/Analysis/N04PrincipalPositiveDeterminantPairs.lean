module

public import ContinuousFlexibility.Analysis.N04PrincipalPositivePairInputs
public import ContinuousFlexibility.Analysis.N04PrincipalPositiveFormula
public import ContinuousFlexibility.Analysis.N04PrincipalPositiveReferenceDeterminant
public import ContinuousFlexibility.Analysis.N04PrincipalPairNeighborhood

/-!
# The positive inverse determinant as a paired family

Its full and difference towers are finite products of the two inverse
atoms' first spatial derivatives and the same fixed physical width.
The reference reciprocal bound then selects one smaller neighborhood
before any reciprocal derivative order is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalPositive_inverseJacobian_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (G.Pos η) b ε) :
    G.n04PrincipalPositivePair η b ε
      (fun z m q => planeJacobian ((G.V η).inverseChart (G.lift η z) m) q)
      (fun m q => planeJacobian ((G.V η).inverseChart (G.ref η) m) q) := by
  have hp := n07aParameterGrading_monotone (G.S η)
  have hI := G.n04PrincipalPositive_parameter_interpolation η
  have hU := isOpen_sectorNeighborhood (G.S η) b ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hUne : (sectorNeighborhood (G.S η) b ε ε).Nonempty :=
    ⟨0, G.n04PrincipalPositive_sector_zero η b h.2.1⟩
  have hE (m : {m : ℕ // G.Pos η m}) :
      1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)) := (G.cost_nonneg η).2.2 m.val
  have hW (m : {m : ℕ // G.Pos η m}) :
      0 < G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (G.n04PrincipalPositive_sample_height_pos η m.val) _
  have hR := G.n04PrincipalPositive_atom_pairBounds η href hg .inverseRadial trivial
  have hT := G.n04PrincipalPositive_atom_pairBounds η href hg .inverseAngleDefect trivial
  have hw := G.n04PrincipalPositive_width_pairBounds (b := b) (ε := ε) η href
  have h1 := G.n04PrincipalPositive_const_pairBounds (b := b) (ε := ε) η 1
  have hRr := hw.mul (hR.firstMixed hΩ hUne true) hp hI hU hΩ hE hW
  have hRt := hw.mul (hR.firstMixed hΩ hUne false) hp hI hU hΩ hE hW
  have hTr := hT.firstMixed hΩ hUne true
  have hTt := h1.add (hT.firstMixed hΩ hUne false) hp hU hΩ hE (fun m => (hW m).le)
  have hJ := (hRr.mul hTt hp hI hU hΩ hE hW).sub
    (hTr.mul hRt hp hI hU hΩ hE hW) hp hU hΩ hE (fun m => (hW m).le)
  apply hJ.congr hΩ
  · intro m z hz q hq
    have hz' : G.lift η z ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
      liftSectorParameter_mem_stateNeighborhood hz le_rfl
    have hs : stateSector (G.S η) (G.lift η z).1 :=
      G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
    exact (G.n04PrincipalPositive_inverseJacobian_formula h η hz' hs m.property q).symm
  · intro m q hq
    have hz' : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
      reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
    have hs : stateSector (G.S η) (G.C η).referenceState :=
      G.W.through03.1.1.2.2.1.stateSector
    exact (G.n04PrincipalPositive_inverseJacobian_formula h η hz' hs m.property q).symm

/-- One neighborhood makes the signed determinant reciprocal available
as a paired factor on every positive piece. -/
theorem n04PrincipalPositive_inverseJacobianInverse_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (G.Pos η) b ε) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      G.n04PrincipalPositivePair η b' ε'
        (fun z m q => (planeJacobian ((G.V η).inverseChart (G.lift η z) m) q)⁻¹)
        (fun m q => (planeJacobian ((G.V η).inverseChart (G.ref η) m) q)⁻¹) := by
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hU : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  apply (G.n04PrincipalPositive_inverseJacobian_pairBounds h η href hg).inverse_neighborhood
    hD hU h.2.1 (G.n04PrincipalPositive_parameter_interpolation η)
    (fun m => (G.cost_nonneg η).2.2 m.val)
  · intro m q hq
    exact congrArg (fun w => planeJacobian ((G.V η).inverseChart w m.val) q)
      (G.n04PrincipalPositive_lift_zero η)
  · have hb := G.n04PrincipalPositive_reference_inverseJacobian_bounds h η href
    refine ⟨hb.choose, hb.choose_spec.1, fun m q hq => ?_⟩
    have hz' : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
      reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
    have hs : stateSector (G.S η) (G.C η).referenceState :=
      G.W.through03.1.1.2.2.1.stateSector
    have hpos := G.n04PrincipalPositive_inverseJacobian_pos h η hz' hs m.property q
    have hend := G.n04PrincipalDivided_positive_endpoints η m.property
    have hqK : q ∈ canonicalOpen (G.S η) (G.V η) m.val := by
      simpa only [canonicalOpen, unitStrip, hend.1, hend.2] using hq
    exact ⟨hpos.ne', by
      simpa only [abs_inv] using (hb.choose_spec.2 m.val q hqK).2⟩

end N04RealizationGauge

end ContinuousFlexibility.Analysis
