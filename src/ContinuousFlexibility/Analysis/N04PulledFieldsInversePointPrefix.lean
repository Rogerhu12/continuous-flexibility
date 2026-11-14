module

public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseRawFamily
public import ContinuousFlexibility.Analysis.N04PulledFieldsInversePointAssembly
public import ContinuousFlexibility.Analysis.N04PulledFieldsSampleCost
public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Prefix bounds for the actual inverse-chart point

The two normalized inverse atoms share one interpolation base. The
reference length atom controls the affine radial rescaling. The angular
projection is retained exactly, so positive parameter orders keep the
sampled height factor. Every tower in the conclusion is a genuine tower
of the retained inverse point on the original neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- Interpolation of the sector grading is independent of the auxiliary
column; it is supplied by the original physical spaces. -/
theorem n04PulledFields_parameter_hasInterpolation
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    HasInterpolation (parameterGrading (G.S η)) := by
  have h : HasInterpolation (parameterGrading G.W.S) :=
    hasInterpolation_of_hasSmoothing (n07aParameterGrading_monotone G.W.S)
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing G.W.hS) hasSmoothing_realGrading)
  exact h

/-- The static physical length has the sampled bound of its own atom
in the same reference certificate. -/
theorem n04PulledFields_reference_physicalLength_bound
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : G.ReferenceData η) :
    ∃ P : ℝ, 0 < P ∧ ∀ m,
      |(G.V η).physicalRight m - (G.V η).physicalLeft m| ≤
        P * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ P := by
  refine (href.2 0).elim fun P hP => ⟨P, hP.1, fun m => ?_⟩
  have hp : ((1 / 2, 0) : PolarPoint) ∈ unitStrip := by
    constructor <;> norm_num
  simpa only [mixedDerivative, iteratedDeriv_zero, atom] using
    hP.2 m .physicalLength (1 / 2, 0) hp 0 0 (by omega)

private def n04PulledFieldsInversePoint_atom : Bool → Atom
  | false => .inverseRadial
  | true => .inverseAngleDefect

private theorem n04PulledFieldsInversePoint_atom_geometry (i : Bool) :
    atomIsGeometry (n04PulledFieldsInversePoint_atom i) := by
  cases i <;> trivial

/-- Instantiate the scalar-family theorem separately from reconstruction,
so the concrete reference and geometry certificates stay opaque there. -/
private theorem n04PulledFieldsInversePoint_scalarPrefix
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ}
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η)
    (J : ∀ i m, SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint =>
        G.atomFamily η (n04PulledFieldsInversePoint_atom i) z.1 m z.2)) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      parameterGrading (G.S η) low z ≤ 1 →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R →
      parameterGrading (G.S η) (low + N + shift * K + 1) z ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
      (∀ i, parameterGrading (G.S η) low (v i).1 ≤ 1) →
      (∀ i, parameterGrading (G.S η) (low + N + shift * K + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        |(J i m).D n (z, q) v| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
            (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
              (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K) := by
  let a : Bool → Atom := n04PulledFieldsInversePoint_atom
  have ha : ∀ i, atomIsGeometry (a i) := n04PulledFieldsInversePoint_atom_geometry
  let RF : ∀ i m, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε) unitStrip
      (fun z => G.atomFamily η (a i) z m) :=
    fun i m => n04PulledFields_currentData_rawMixedRegularity (hgeo.1 (a i) (ha i))
      (fun n => (href.1 n (a i)).1) m
  refine (n04PulledFields_sampleHeight_bounded G).elim fun Hmax hHmax => ?_
  exact n04PulledFields_currentData_rawFamily_pureWord
    (ι := Bool) (fun i => hgeo.1 (a i) (ha i))
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1
    (zero_le_one.trans hHmax.1) (hHmax.2 η)
    (fun i m => (href.1 m (a i)).1)
    (fun s => ⟨(href.2 s).choose, (href.2 s).choose_spec.1,
      fun i m q r t hrt => (href.2 s).choose_spec.2 m (a i) q.val q.property r t hrt⟩)
    RF J (n04PulledFields_parameter_hasInterpolation G η)

/-- One low order is selected before every parameter prefix. The bound
holds for any genuine tower of the actual inverse point, with one common
sampled coefficient for all pieces. -/
theorem n04PulledFields_inversePoint_prefix
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ offset : ℕ, ∀ N : ℕ,
      ∃ M A : ℝ, 1 ≤ M ∧ 0 ≤ A ∧
      ∀ m, ∀ Jφ : SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
        (fun z : Parameter (G.S η) × PolarPoint =>
          G.pulledPoint η (G.lift η z.1) m z.2),
      ∀ z ∈ sectorNeighborhood (G.S η) base ε ε, parameterGrading (G.S η) low z ≤ 1 →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R →
      parameterGrading (G.S η) (low + N + offset + 1) z ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
      (∀ i, parameterGrading (G.S η) low (v i).1 ≤ 1) →
      (∀ i, parameterGrading (G.S η) (low + N + offset + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        ‖Jφ.D n (z, q) v‖ ≤ M * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
          parameterHeightWeight
            (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
          (R ^ (1 / (((N + offset : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  let a : Bool → Atom := n04PulledFieldsInversePoint_atom
  have ha : ∀ i, atomIsGeometry (a i) := n04PulledFieldsInversePoint_atom_geometry
  let J : ∀ i m, SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.atomFamily η (a i) z.1 m z.2) :=
    fun i m => n04PulledFields_geometryAtom_jointDirections G η hgeo href (a i) (ha i) m
  have hscalar := n04PulledFieldsInversePoint_scalarPrefix G η hgeo href J
  exact n04PulledFields_inversePoint_prefix_of_scalar J
    (fun m => (G.V η).physicalLeft m)
    (fun m => (G.V η).physicalRight m - (G.V η).physicalLeft m)
    (fun m y _ => n04PulledFields_pulledPoint_eq_inverseAtoms G η m
      (n04PulledFields_admissible_physicalLength_pos G η hadm m).ne' y.1 y.2)
    (parameterGrading (G.S η)) base
    (fun m => G.W.U.E0 (G.W.U.sample ((G.V η).cell m)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ))
    (G.cost_nonneg η).2.2 (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
    (n04PulledFields_reference_physicalLength_bound G η href) hscalar

end ContinuousFlexibility.Analysis
