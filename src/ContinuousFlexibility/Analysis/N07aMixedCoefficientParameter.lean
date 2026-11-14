module

public import ContinuousFlexibility.Analysis.N07aCoefficientParameterJets
public import ContinuousFlexibility.Analysis.N07aPrimitiveFamilyTame

/-!
# The actual mixed coefficient as an even height primitive

The odd N01 coefficient is represented by its fixed angular primitive.
The original parameter jets pass through bounded cylinder integration and
the same closed Sobolev graphs; no interchange of formal derivatives is
assumed. Both the primitive decoder and its angular derivative are exact.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearAnnularGroup
  n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup
  n07aNonlinearAnnularSMul
  n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup
  n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup
  n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup
  n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup
  n07aNonlinearDirectionsSMul
  n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup
  n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup
  n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε γ : ℝ}

theorem n07aMixedCoefficientPrimitive_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) :
    HeightMember D T γ
      (scalarAngularPrimitive (n07aCoefficientDifferenceField D S C 1
        (liftSectorParameter S C z))) := by
  have hraw := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hsector := h01.2.2.1.liftSectorParameter_sector z
  apply n07a_scalarAngularPrimitive_heightMember hT
    (n07aCoefficientDifferenceField_contDiffOn hS hT h01 hraw hsector 1)
  · intro r θ
    simpa only [eq_self, ite_true, neg_one_mul] using
      n07aCoefficientDifferenceField_reflection (C := C) hS 1
        (liftSectorParameter S C z) r θ
  · exact n07aCoefficientDifferenceField_periodic hS 1 _
  · intro p hp
    exact n07aCoefficientDifferenceField_zero_outside 1 _ hp
  · exact n07aCoefficientDifferenceField_weightedJets_memLp hS hT h01 hγ hraw hsector 1

def n07aMixedCoefficientHeight
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    (z : StateDirections S × ℝ) : (S.height γ).Space := by
  classical
  exact if hz : z ∈ sectorNeighborhood S base ε ε then
    SobolevModelData.liftHeight (hS.1 γ)
      (scalarAngularPrimitive (n07aCoefficientDifferenceField D S C 1
        (liftSectorParameter S C z)))
      (n07aMixedCoefficientPrimitive_heightMember hS hT h01 hγ hz) else 0

theorem n07aMixedCoefficientHeight_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) :
    (S.height γ).decode (n07aMixedCoefficientHeight hS hT h01 hγ z) =
      scalarAngularPrimitive (n07aCoefficientDifferenceField D S C 1
        (liftSectorParameter S C z)) := by
  classical
  unfold n07aMixedCoefficientHeight
  rw [dite_eq_left hz]
  exact SobolevModelData.decode_liftHeight (hS.1 γ) _ _

theorem n07aMixedCoefficientHeight_angularPartial
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    angularPartial ((S.height γ).decode (n07aMixedCoefficientHeight hS hT h01 hγ z)) p =
      n07aCoefficientDifferenceField D S C 1 (liftSectorParameter S C z) p := by
  rw [n07aMixedCoefficientHeight_decode hS hT h01 hγ hz]
  exact n07a_angularPartial_scalarAngularPrimitive_on
    (n07aCoefficientDifferenceField_contDiffOn hS hT h01
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) 1) hp

theorem n07aMixedCoefficientHeight_fixedNeighborhoodSmoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64) :
    FixedNeighborhoodSmoothTame (n07aParameterGrading S) (S.height γ).grading
      (sectorNeighborhood S base ε ε) base loss
      (n07aMixedCoefficientHeight hS hT h01 hγ) := by
  let : IsTopologicalAddGroup (StateDirections S × ℝ) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  let : ContinuousSMul ℝ (StateDirections S × ℝ) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  let : FirstCountableTopology (StateDirections S × ℝ) :=
    (n07aParameterGrading_withSeminorms S).firstCountableTopology
  apply n07a_primitiveHeightFamily_fixedNeighborhoodSmoothTame
    (E := StateDirections S × ℝ) (δ := (3 / 64 : ℝ))
    (A := S.height γ) (U := sectorNeighborhood S base ε ε)
    (p := n07aParameterGrading S) (base := base) (loss := loss)
    (f := fun z => n07aCoefficientDifferenceField D S C 1 (liftSectorParameter S C z))
    (g := n07aMixedCoefficientHeight hS hT h01 hγ)
    (hT := hT) (hA := hS.1 γ) (hU := n07a_sectorNeighborhood_isOpen S base ε ε)
    (hp := n07aParameterGrading_withSeminorms S)
    (hmono := n07aParameterGrading_monotone S)
    (hf := fun z hz => n07aCoefficientDifferenceField_contDiffOn hS hT h01
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) 1)
    (hg := fun z hz => n07aMixedCoefficientHeight_decode hS hT h01 hγ hz)
    (J := n07aCoefficientParameterJet hT h01 1) (hJ := ?_) (hγδ := hγ)
  intro k s
  let data := n07aCoefficientParameterJet_decay_bound hT h01 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  have hb := data.choose_spec.2
  exact ⟨B, hB.le, fun a b p hab z hz v => hb 1 a b p hab z hz v⟩

theorem n07aMixedCoefficientHeight_smoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64) :
    SmoothTameOn (n07aParameterGrading S) (S.height γ).grading
      (sectorNeighborhood S base ε ε) (n07aMixedCoefficientHeight hS hT h01 hγ) :=
  (n07aMixedCoefficientHeight_fixedNeighborhoodSmoothTame hS hT h01 hγ).1

end ContinuousFlexibility.Analysis
