import ContinuousFlexibility.Analysis.CanonicalMaterialRatioDifferenceJets
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# The actual fixed geometric atoms have zero state differences

Both interval lengths and the material scale evaluated at the physical
unit point are fixed by the same atlas and material data. Their six
current-minus-reference jet fields therefore vanish. The already defined
zero directional tower is transported by equality, so no second derivative
representation or spatial reference estimate is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry

def CanonicalFixedGeometryAtom (a : Atom) : Prop :=
  a = .physicalLength ∨ a = .physicalLengthInverse ∨
    a = .canonicalLength ∨ a = .canonicalLengthInverse ∨
    a = .materialEll ∨ a = .materialEllInverse

theorem canonical_fixedGeometryAtom_state_independent
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {a : Atom} (ha : CanonicalFixedGeometryAtom a)
    (z w : AnnularState S × ℝ) (m : ℕ) :
    atom D T S C L K z m a = atom D T S C L K w m a := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem canonical_fixedGeometryDifferenceJets_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {a : Atom} (ha : CanonicalFixedGeometryAtom a)
    (z : Parameter S) (m i j : ℕ) (p : unitStrip) :
    differenceJets D T S C L K z a m i j p = 0 := by
  have he := canonical_fixedGeometryAtom_state_independent
    (D := D) (T := T) (C := C) (L := L) (K := K) ha
    (liftSectorParameter S C z) (C.referenceState, 0) m
  have hzero :
      (fun q : PolarPoint =>
        atom D T S C L K (liftSectorParameter S C z) m a q -
          atom D T S C L K (C.referenceState, 0) m a q) =
        (fun _ : PolarPoint => (0 : ℝ)) := by
    funext q
    exact sub_eq_zero.mpr (congrFun he q)
  change mixedDerivative i j _ (p : PolarPoint) = 0
  rw [hzero]
  simp only [mixedDerivative, iteratedDeriv_fun_const_zero]

/-- Reuse the same genuine zero tower for the actual fixed geometric
slice. All spatial orders, including zero, and all state orders vanish. -/
theorem exists_canonicalFixedGeometryDifference_zero_tower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    {a : Atom} (ha : CanonicalFixedGeometryAtom a) :
    ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : Parameter S => differenceJets D T S C L K z a),
      ∀ k z v, J.D k z v = 0 := by
  have hratio : CanonicalMaterialRatioAtom .ratioH := Or.inl rfl
  obtain ⟨J, hJ⟩ := exists_canonicalMaterialRatioDifference_zero_tower
    (D := D) (T := T) (C := C) (L := L) (K := K)
    (base := base) (ε := ε) hratio
  have he : ∀ z ∈ sectorNeighborhood S base ε ε,
      differenceJets D T S C L K z .ratioH =
        differenceJets D T S C L K z a := by
    intro z hz
    funext m i j p
    rw [canonical_materialRatioDifferenceJets_eq_zero hratio,
      canonical_fixedGeometryDifferenceJets_eq_zero ha]
  exact ⟨J.congr he, hJ⟩

end ContinuousFlexibility.Analysis
