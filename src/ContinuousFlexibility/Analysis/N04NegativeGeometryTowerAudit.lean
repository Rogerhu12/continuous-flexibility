import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N07aParameterGrading
import ContinuousFlexibility.Analysis.SmoothDirectionsMixedScalarLine
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# The piece predicate does not restrict the current tower's domain

These results audit the unchanged `CurrentJetDataOn` interface.  Its
regularity and estimates are restricted by the piece predicate `P`, but
its existential directional tower is indexed by every natural number.
Consequently even the empty piece predicate requires actual parameter
smoothness on every piece.  The spatially constant family `|z.2|` supplies
a counterexample on every positive-radius sector neighborhood.

This is a counterexample to vacuity of the interface on an empty family,
not a construction of a gauge contradicting the NegativeGeometry node.
No frozen definition or blueprint statement is changed here.
-/

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

/-- The frozen interface supplies a genuine directional tower for every
piece, without requiring that the piece satisfy `P`. -/
theorem n04NegativeGeometry_currentData_tower_all_pieces
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (m i j : ℕ) (q : unitStrip) :
    Nonempty (SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val)) :=
  ⟨h.2.choose m i j q⟩

/-- For the empty piece predicate all estimates are vacuous, but the
unrestricted existence of the directional towers remains. -/
theorem n04NegativeGeometry_currentData_empty_iff
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ} :
    CurrentJetDataOn S T cell (fun _ => False) base ε f f₀ ↔
      Nonempty (∀ m (i j : ℕ) (q : unitStrip),
        SmoothDirections (sectorNeighborhood S base ε ε)
          (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val)) := by
  constructor
  · intro h
    exact ⟨h.2.choose⟩
  · intro h
    exact h.elim fun J =>
      ⟨fun _ _ _ hm => False.elim hm, J,
        ⟨0, fun _ => ⟨1, zero_lt_one, fun _ _ _ hm => False.elim hm⟩⟩,
        fun _ => ⟨0, fun _ => ⟨1, zero_lt_one, fun _ _ _ _ hm => False.elim hm⟩⟩⟩

private theorem n04NegativeGeometry_no_abs_snd_tower
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup (E × ℝ)] [ContinuousSMul ℝ (E × ℝ)]
    {U : Set (E × ℝ)} (hzero : (0 : E × ℝ) ∈ U) :
    ¬ Nonempty (SmoothDirections U (fun z : E × ℝ => |z.2|)) := by
  intro h
  apply h.elim
  intro J
  have hd := (J.hasDerivAt_line (0 : E × ℝ) (0, 1) (t := 0)
    (by simpa only [zero_smul, add_zero] using hzero)).differentiableAt
  change DifferentiableAt ℝ (fun t : ℝ => |0 + t * 1|) 0 at hd
  exact not_differentiableAt_abs_zero (by simpa only [zero_add, mul_one] using hd)

/-- A concrete family fails the interface for every predicate, including
the empty predicate, because the scalar parameter has a cusp at zero. -/
theorem n04NegativeGeometry_abs_parameter_not_currentData
    (S : PhysicalSpacesData) (T : MaterialData) (cell : ℕ → ℕ)
    (P : ℕ → Prop) (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ¬ CurrentJetDataOn S T cell P base ε
      (fun z _ _ => |z.2|) (fun _ _ => 0) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  intro h
  let q : unitStrip := ⟨(1 / 2, 0), by
    constructor
    · constructor <;> norm_num
    · exact mem_univ _⟩
  have hJ := n04NegativeGeometry_currentData_tower_all_pieces h 0 0 0 q
  have hzero : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε :=
    ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have habs : Nonempty (SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : Parameter S => |z.2|)) :=
    hJ.elim fun J => ⟨J.congr (fun _ _ => by
      simp only [mixedDerivative, iteratedDeriv_zero, sub_zero])⟩
  exact n04NegativeGeometry_no_abs_snd_tower hzero habs

end ContinuousFlexibility.Analysis

#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_currentData_tower_all_pieces
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_currentData_empty_iff
/--
info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_abs_parameter_not_currentData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_abs_parameter_not_currentData
