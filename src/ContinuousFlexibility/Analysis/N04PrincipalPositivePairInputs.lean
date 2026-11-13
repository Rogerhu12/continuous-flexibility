import ContinuousFlexibility.Analysis.N04PrincipalPairData
import ContinuousFlexibility.Analysis.N04PrincipalPairFirstMixed
import ContinuousFlexibility.Analysis.N04PrincipalPositiveReferenceFields
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope
import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# Paired primitive inputs on the positive pieces

Every primitive is the supplied current family and its exact reference.
The physical coefficient references use N01 on the positive inverse
point. The material height is uniformly bounded, and interpolation uses
the unchanged sector grading of the original physical spaces.
-/

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

/-- The same paired estimate with its index restricted to positive
pieces. The scalar functions retain the frozen interface's argument order. -/
abbrev n04PrincipalPositivePair (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (b : ℕ) (ε : ℝ)
    (f : Parameter (G.S η) → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  N04PrincipalPairBounds (parameterGrading (G.S η))
    (fun m : {m : ℕ // G.Pos η m} => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)))
    (fun m : {m : ℕ // G.Pos η m} =>
      G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ))
    (U := sectorNeighborhood (G.S η) b ε ε) (Ω := unitStrip)
    (fun m z => f z m.val) (fun m => f₀ m.val)

theorem n04PrincipalPositive_sample_height_pos
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) :
    0 < G.W.U.H (G.W.U.sample ((G.V η).cell m)) := by
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hU : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  exact (hU.2.1 _ (materialSample_mem_interval hD hU ((G.V η).cell m))).2.1

theorem n04PrincipalPositive_sample_height_bound
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    ∃ RH : ℝ, 0 < RH ∧ ∀ m,
      G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) ≤ RH := by
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hU : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have hb := materialSample_H_E0_envelope hU hD (γ := (3 / 4 : ℝ)) (by norm_num) 0
  refine ⟨hb.choose, hb.choose_spec.1, fun m => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hb.choose_spec.2 ((G.V η).cell m)

theorem n04PrincipalPositive_parameter_interpolation
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    HasInterpolation (parameterGrading (G.S η)) := by
  have hp : Monotone (parameterGrading G.W.S) := n07aParameterGrading_monotone G.W.S
  have hi : HasInterpolation (parameterGrading G.W.S) :=
    hasInterpolation_of_hasSmoothing hp
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing G.W.hS) hasSmoothing_realGrading)
  exact hi

theorem n04PrincipalPositive_lift_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) : G.lift η 0 = G.ref η := by
  change liftSectorParameter (G.S η) (G.C η) 0 = ((G.C η).referenceState, 0)
  exact (liftSectorParameter_eq_affine (G.S η) (G.C η) 0).trans
    ((congrArg (fun w : AnnularState (G.S η) × ℝ => ((G.C η).referenceState, 0) + w)
      (ContinuousLinearMap.map_zero (sectorParameterInclusion (G.S η)))).trans (add_zero _))

theorem n04PrincipalPositive_sector_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (0 : Parameter (G.S η)) ∈ sectorNeighborhood (G.S η) b ε ε := by
  constructor
  · change sectorGrading (G.S η) b 0 < ε
    exact (sectorGrading (G.S η) b).map_zero'.trans_lt hε
  · change |(0 : ℝ)| < ε
    simpa only [abs_zero] using hε

theorem n04PrincipalPositive_atom_pairBounds {b : ℕ} {ε : ℝ}
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (G.Pos η) b ε) (a : Atom) (ha : atomIsGeometry a) :
    G.n04PrincipalPositivePair η b ε (G.atomFamily η a) (G.atomRef η a) := by
  have hheight := G.n04PrincipalPositive_sample_height_bound η
  apply (hg.1 a ha).n04Principal_pairBounds (fun m _ => (href.1 m a).1) ?_
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 hheight.choose_spec.1.le hheight.choose_spec.2
  intro s
  have hb := href.2 s
  exact ⟨hb.choose, hb.choose_spec.1, fun m _ q i j hij =>
    hb.choose_spec.2 m a q.val q.property i j hij⟩

theorem n04PrincipalPositive_height_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (G.Pos η) b ε) :
    G.n04PrincipalPositivePair η b ε (G.pulledHeight η) (G.pulledHeightRef η) := by
  have hreference := G.n04PrincipalPositive_pulledHeightRef_jets h η href
  have hheight := G.n04PrincipalPositive_sample_height_bound η
  apply hg.2.n04Principal_pairBounds (fun m _ => hreference.1 m false) ?_
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 hheight.choose_spec.1.le hheight.choose_spec.2
  intro s
  have hb := hreference.2 s
  exact ⟨hb.choose, hb.choose_spec.1, fun m _ q i j hij =>
    hb.choose_spec.2 m false q i j hij⟩

theorem n04PrincipalPositive_coefficient_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hf : G.FieldData η b ε) (c : Fin 3) :
    G.n04PrincipalPositivePair η b ε
      (G.pulled η (G.coefficientField η c)) (G.pulledRef η (G.coefficientField η c)) := by
  have hreference := G.n04PrincipalPositive_pulledCoefficientRef_jets h η href
  have hheight := G.n04PrincipalPositive_sample_height_bound η
  have hdata : G.Data η (G.Pos η) b ε
      (G.pulled η (G.coefficientField η c)) (G.pulledRef η (G.coefficientField η c)) :=
    (hf.1 c).mono (fun _ _ => trivial) le_rfl le_rfl
      (G.cost_nonneg η).1 (G.cost_nonneg η).2.1
  apply hdata.n04Principal_pairBounds (fun m hm => hreference.1 m hm c) ?_
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 hheight.choose_spec.1.le hheight.choose_spec.2
  intro s
  have hb := hreference.2 s
  exact ⟨hb.choose, hb.choose_spec.1, fun m hm q i j hij =>
    hb.choose_spec.2 m hm c q i j hij⟩

theorem n04PrincipalPositive_width_pairBounds {b : ℕ} {ε : ℝ}
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    G.n04PrincipalPositivePair η b ε
      (fun _ m _ => (G.V η).physicalRight m - (G.V η).physicalLeft m)
      (fun m _ => (G.V η).physicalRight m - (G.V η).physicalLeft m) := by
  apply N04PrincipalPairBounds.fixedSpatial (parameterGrading (G.S η))
    (fun m : {m : ℕ // G.Pos η m} => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ))
    (isOpen_sectorNeighborhood (G.S η) b ε ε)
    (fun m => (G.cost_nonneg η).2.2 m.val)
    (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m.val) _)
    (fun m _ => (G.V η).physicalRight m.val - (G.V η).physicalLeft m.val)
    (fun _ => contDiffOn_const)
  intro s
  have hb := href.2 s
  refine ⟨hb.choose, hb.choose, fun m i j hij q hq => ?_⟩
  exact (Real.norm_eq_abs _).trans_le (hb.choose_spec.2 m.val .physicalLength q hq i j hij)

theorem n04PrincipalPositive_const_pairBounds {b : ℕ} {ε : ℝ}
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (c : ℝ) :
    G.n04PrincipalPositivePair η b ε (fun _ _ _ => c) (fun _ _ => c) := by
  apply N04PrincipalPairBounds.fixedSpatial (parameterGrading (G.S η))
    (fun m : {m : ℕ // G.Pos η m} => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ))
    (isOpen_sectorNeighborhood (G.S η) b ε ε)
    (fun m => (G.cost_nonneg η).2.2 m.val)
    (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m.val) _)
    (fun _ _ => c) (fun _ => contDiffOn_const)
  intro s
  refine ⟨|c|, 0, fun m i j hij q hq => ?_⟩
  rw [Real.rpow_zero, mul_one]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [mixedDerivative, iteratedDeriv_const, hi, hj, Real.norm_eq_abs]

end N04RealizationGauge

end ContinuousFlexibility.Analysis
