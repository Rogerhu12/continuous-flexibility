import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceAtoms
import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeRegularity
import ContinuousFlexibility.Analysis.N04PrincipalPositivePairInputs
import ContinuousFlexibility.Analysis.N04PrincipalPositiveIndex

/-!
# Paired inputs for the positive geometry collector

An individual current atom and the supplied material certificate give its
paired tower. The fixed width factor uses the original positive component
and sample. Neither construction assumes the complete geometry interface.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
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

theorem positiveGeometry_atom_pair_of_data {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε)
    (hmaterial : N04PositiveReferenceMaterialBounds G.W.T G.X.cell G.Y G.H)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) (ha : atomIsGeometry a)
    (h : G.Data η (G.Pos η) base ε (G.atomFamily η a) (G.atomRef η a)) :
    G.n04PrincipalPositivePair η base ε (G.atomFamily η a) (G.atomRef η a) := by
  have hr := G.positiveGeometry_reference_atom_jets hA hmaterial
  have hh := G.n04PrincipalPositive_sample_height_bound η
  apply h.n04Principal_pairBounds
    (fun m hm => ((hr 0).choose_spec.2 η m hm a ha).1) ?_
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 hh.choose_spec.1.le hh.choose_spec.2
  intro s
  exact ⟨(hr s).choose, (hr s).choose_spec.1, fun m hm q i j hij =>
    ((hr s).choose_spec.2 η m hm a ha).2.2 q.val q.property i j hij⟩

/-- The physical length and its reciprocal use the positive component
selected by the actual whole-piece index. -/
theorem positiveGeometry_width_values {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      ∀ m, G.Pos η m →
        0 < (G.V η).physicalRight m - (G.V η).physicalLeft m ∧
        ((G.V η).physicalRight m - (G.V η).physicalLeft m)⁻¹ ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  let wd := n04PositiveGeometry_component_width_cost G.W G.X
  let B : ℝ := wd.choose
  have hB : 1 ≤ B := wd.choose_spec.1
  refine ⟨B, zero_lt_one.trans_le hB, fun η m hm => ?_⟩
  let ix := G.n04PrincipalDivided_positive_index η hm
  let i := ix.choose
  have hf := n04WholeReferenceGaugeAtlasData_positive_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun j => positiveReferenceCylinderChart (G.Y j))
    (fun j => positiveReferenceCylinderInverse (G.Y j))
    (fun j p => G.H j p.1) G.τ G.σ G.Q G.N
    (G.W.C.referenceState, 0) m i ix.choose_spec
  have hp : (G.V η).physicalLeft m = n04PositiveLeft i := hf.2.2.1
  have hq : (G.V η).physicalRight m = n04PositiveRight i := hf.2.2.2.1
  have hc : (G.V η).cell m = G.X.cell i := hf.2.2.2.2.2.1
  have hi : n04PositiveLeft i < n04PositiveRight i := by
    have hx : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
    have hmapped := (hA.2.2.2.1 i).1.inverse_maps_open
      (x := ((1 / 2 : ℝ), 0)) ⟨hx, mem_univ _⟩
    exact hmapped.1.1.trans hmapped.1.2
  rw [hp, hq, hc]
  refine ⟨sub_pos.mpr hi, (wd.choose_spec.2 i).2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (zero_le_one.trans (G.W.floor _))
      (le_enlargedMaterialData_E0 G.W.T _) (zero_le_one.trans hB))
    (zero_le_one.trans hB)

/-- The canonical width is one on every positive piece, so the fixed
Jacobian factor has a paired tower without any reference-jet premise. -/
theorem positiveGeometry_widthRatio_pair {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    G.n04PrincipalPositivePair η base ε
      (fun _ m _ => ((G.V η).right m - (G.V η).left m) /
        ((G.V η).physicalRight m - (G.V η).physicalLeft m))
      (fun m _ => ((G.V η).right m - (G.V η).left m) /
        ((G.V η).physicalRight m - (G.V η).physicalLeft m)) := by
  let wd := G.positiveGeometry_width_values hA
  let B : ℝ := wd.choose
  have hB : 0 < B := wd.choose_spec.1
  apply N04PrincipalPairBounds.fixedSpatial (parameterGrading (G.S η))
    (fun m : {m : ℕ // G.Pos η m} => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ))
    (isOpen_sectorNeighborhood (G.S η) base ε ε)
    (fun m => (G.cost_nonneg η).2.2 m.val)
    (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m.val) _)
    (fun m _ => ((G.V η).right m.val - (G.V η).left m.val) /
      ((G.V η).physicalRight m.val - (G.V η).physicalLeft m.val))
    (fun _ => contDiffOn_const)
  intro s
  refine ⟨B, B, fun m i j hij q hq => ?_⟩
  have hend := G.n04PrincipalDivided_positive_endpoints η m.property
  have hw := wd.choose_spec.2 η m.val m.property
  have hn : 0 ≤ B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)) ^ B :=
    mul_nonneg hB.le (Real.rpow_nonneg ((G.cost_nonneg η).1 m.val) _)
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst i; subst j
      simpa only [mixedDerivative, iteratedDeriv_zero, hend.1, hend.2,
        sub_zero, one_div, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw.1)] using hw.2
    · simpa [mixedDerivative, iteratedDeriv_const, hi, hj] using hn
  · simpa [mixedDerivative, iteratedDeriv_const, hi] using hn

end N04RealizationGauge

end ContinuousFlexibility.Analysis
