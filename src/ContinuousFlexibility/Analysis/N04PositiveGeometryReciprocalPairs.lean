import ContinuousFlexibility.Analysis.N04PositiveGeometryAtomPairInputs
import ContinuousFlexibility.Analysis.N04PositiveGeometryPairCurrentData
import ContinuousFlexibility.Analysis.N04PrincipalPairNeighborhood

/-!
# Height and Jacobian reciprocals on one neighborhood

The exact reference inverses already have material value bounds. The
paired denominator estimate therefore selects a common smaller
neighborhood before all orders of its reciprocal. Both denominators are
strictly positive by the actual positive range geometry.
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

theorem positiveGeometry_data_of_pair {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (a : Atom) (ha : atomIsGeometry a)
    (h : G.n04PrincipalPositivePair η base ε (G.atomFamily η a) (G.atomRef η a)) :
    ∃ b : ℕ, base ≤ b ∧
      G.Data η (G.Pos η) b (min ε (1 / 2)) (G.atomFamily η a) (G.atomRef η a) :=
  h.to_currentDataOn hA.2.1 (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1
    (fun z hz m hm => (G.positiveAtom_regular η hA a ha z hz m hm).2)
    (fun m _ => G.atomRef_eq_zero η a m)

/-- `false` is height and `true` is the forward Jacobian. The conclusion
uses the literal stored reciprocal atoms in both cases. -/
theorem positiveGeometry_denominator_inverse_pair {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε)
    (hmaterial : N04PositiveReferenceMaterialBounds G.W.T G.X.cell G.Y G.H)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (jacobian : Bool)
    (h : G.n04PrincipalPositivePair η base ε
      (G.atomFamily η (if jacobian then .jacobian else .height))
      (G.atomRef η (if jacobian then .jacobian else .height))) :
    ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      G.n04PrincipalPositivePair η b δ
        (G.atomFamily η (if jacobian then .jacobianInverse else .heightInverse))
        (G.atomRef η (if jacobian then .jacobianInverse else .heightInverse)) := by
  let a : Atom := if jacobian then .jacobian else .height
  let ai : Atom := if jacobian then .jacobianInverse else .heightInverse
  have hai : atomIsGeometry ai := by cases jacobian <;> trivial
  have hfi (z : Parameter (G.S η)) (m : ℕ) (q : PolarPoint) :
      G.atomFamily η ai z m q = (G.atomFamily η a z m q)⁻¹ := by
    cases jacobian <;> rfl
  have hri (m : ℕ) (q : PolarPoint) :
      G.atomRef η ai m q = (G.atomRef η a m q)⁻¹ := by
    cases jacobian <;> rfl
  let rd := G.positiveGeometry_reference_atom_jets hA hmaterial 0
  have hr : ∃ R : ℝ, 0 < R ∧
      ∀ m : {m : ℕ // G.Pos η m}, ∀ q ∈ unitStrip,
        G.atomRef η a m.val q ≠ 0 ∧
          |(G.atomRef η a m.val q)⁻¹| ≤
            R * G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)) ^ R := by
    refine ⟨rd.choose, rd.choose_spec.1, fun m q hq => ?_⟩
    have hg := G.positiveRangeGeometry η hA 0
      (G.n04PrincipalPositive_sector_zero η base hA.2.1) m.val m.property
    have hpos : 0 < G.atomRef η a m.val q := by
      rw [G.atomRef_eq_zero η a m.val]
      cases jacobian with
      | false => exact hg.height_positive _
      | true => exact abs_pos.mpr (hg.jacobian_positive _).ne'
    have hb := (rd.choose_spec.2 η m.val m.property ai hai).2.2 q hq 0 0 (by omega)
    have hb' : |G.atomRef η ai m.val q| ≤
        rd.choose * G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)) ^ rd.choose := by
      simpa only [mixedDerivative, iteratedDeriv_zero, Prod.eta] using hb
    exact ⟨hpos.ne', (congrArg abs (hri m.val q).symm).trans_le hb'⟩
  have hinv := h.inverse_neighborhood G.W.radial.1
    (isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT) hA.2.1
    (G.n04PrincipalPositive_parameter_interpolation η)
    (fun m => (G.cost_nonneg η).2.2 m.val)
    (fun m q _ => (congrFun (G.atomRef_eq_zero η a m.val) q).symm) hr
  refine ⟨hinv.choose, hinv.choose_spec.1, hinv.choose_spec.2.choose,
    hinv.choose_spec.2.choose_spec.1, hinv.choose_spec.2.choose_spec.2.1,
    hinv.choose_spec.2.choose_spec.2.2.1, ?_⟩
  exact hinv.choose_spec.2.choose_spec.2.2.2.congr
    (isOpen_Ioo.prod isOpen_univ)
    (fun m z _ q _ => (hfi z m.val q).symm)
    (fun m q _ => (hri m.val q).symm)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
