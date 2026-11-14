module

public import ContinuousFlexibility.Analysis.SolveReturnEquations
public import ContinuousFlexibility.Analysis.N08Neighborhoods

/-!
# The six actual material ratios have zero state differences

The physical unit point and the sample attached to a fixed atlas do not
depend on the state. Consequently all six material ratios have identical
current and reference functions, including every mixed spatial jet. The
zero multilinear maps give a genuine state derivative tower. No estimate
for the reference spatial jets, or lower bound E0 >= 1, is used here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry

def CanonicalMaterialRatioAtom (a : Atom) : Prop :=
  a = .ratioH ∨ a = .ratioHInverse ∨ a = .ratioM ∨
    a = .ratioMInverse ∨ a = .ratioE0 ∨ a = .ratioE0Inverse

theorem canonical_materialRatioAtom_state_independent
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {a : Atom} (ha : CanonicalMaterialRatioAtom a)
    (z w : AnnularState S × ℝ) (m : ℕ) :
    atom D T S C L K z m a = atom D T S C L K w m a := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem canonical_materialRatioDifferenceJets_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {a : Atom} (ha : CanonicalMaterialRatioAtom a)
    (z : Parameter S) (m i j : ℕ) (p : unitStrip) :
    differenceJets D T S C L K z a m i j p = 0 := by
  have he := canonical_materialRatioAtom_state_independent
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

/-- The tower belongs to the actual ratio slice of `differenceJets` on
the actual sector neighborhood. It requires no geometric certificate. -/
theorem exists_canonicalMaterialRatioDifference_zero_tower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    {a : Atom} (ha : CanonicalMaterialRatioAtom a) :
    ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : Parameter S => differenceJets D T S C L K z a),
      ∀ k z v, J.D k z v = 0 := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : Parameter S => differenceJets D T S C L K z a) := {
    open_domain := n08_isOpen_sectorNeighborhood S base ε ε
    D := fun _ _ => 0
    zero := by
      intro z hz
      funext m i j p
      exact (canonical_materialRatioDifferenceJets_eq_zero ha z m i j p).symm
    continuous := by
      intro n
      simpa only [ContinuousMultilinearMap.zero_apply] using
        (continuous_const.continuousOn : ContinuousOn
          (fun _ : Parameter S × (Fin n → Parameter S) =>
            (0 : ℕ → ℕ → ℕ → unitStrip → ℝ))
          (sectorNeighborhood S base ε ε ×ˢ univ))
    derivative := by
      intro n z hz v w
      simpa only [ContinuousMultilinearMap.zero_apply] using
        (hasProjectiveLineDerivAt_const
          (0 : ℕ → ℕ → ℕ → unitStrip → ℝ) z w) }
  exact ⟨J, fun _ _ _ => rfl⟩

end ContinuousFlexibility.Analysis
