import ContinuousFlexibility.Analysis.N04PrincipalPositiveDeterminantPairs
import ContinuousFlexibility.Analysis.N04PrincipalPositivePolynomial
import ContinuousFlexibility.Analysis.N07aActualCubicFactors

/-!
# Paired bounds for the actual positive principal coefficients

The determinant reciprocal selects one common neighborhood. On that
domain the same nine primitive factors give all three components through
the inverse-adjugate polynomial. The reference expression is the actual
reference member, obtained by evaluating the same formula at zero.
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

/-- A selector version of the exact positive principal formula, with
the actual signed inverse determinant as its scalar reciprocal input. -/
theorem n04PrincipalPositive_principal_polynomial {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m) {q : PolarPoint} (hq : q ∈ unitStrip) (v : Fin 3) :
    G.atomFamily η (n07aCubicPrincipalAtom v) z m q =
      n04PrincipalPositivePolynomial v
        (G.pulled η (G.coefficientField η 0) z m q)
        (G.pulled η (G.coefficientField η 1) z m q)
        (G.pulled η (G.coefficientField η 2) z m q)
        (G.pulledHeight η z m q)
        ((planeJacobian ((G.V η).inverseChart (G.lift η z) m) q)⁻¹)
        (((G.V η).physicalRight m - (G.V η).physicalLeft m) *
          mixedDerivative 1 0 (G.atomFamily η .inverseRadial z m) q)
        (((G.V η).physicalRight m - (G.V η).physicalLeft m) *
          mixedDerivative 0 1 (G.atomFamily η .inverseRadial z m) q)
        (mixedDerivative 1 0 (G.atomFamily η .inverseAngleDefect z m) q)
        (1 + mixedDerivative 0 1 (G.atomFamily η .inverseAngleDefect z m) q) := by
  have hf := G.n04PrincipalPositive_principal_unit_formula h η hz hm hq
  have hw : G.lift η z ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector (G.S η) (G.lift η z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hJ : planeJacobian ((G.V η).inverseChart (G.lift η z) m) q =
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) *
          mixedDerivative 1 0 (G.atomFamily η .inverseRadial z m) q *
          (1 + mixedDerivative 0 1 (G.atomFamily η .inverseAngleDefect z m) q) -
        mixedDerivative 1 0 (G.atomFamily η .inverseAngleDefect z m) q *
          (((G.V η).physicalRight m - (G.V η).physicalLeft m) *
            mixedDerivative 0 1 (G.atomFamily η .inverseRadial z m) q) :=
    G.n04PrincipalPositive_inverseJacobian_formula h η hw hs hm q
  dsimp only at hf
  rw [← hJ] at hf
  fin_cases v
  · simpa [n07aCubicPrincipalAtom, n04PrincipalPositivePolynomial] using hf.1
  · simpa [n07aCubicPrincipalAtom, n04PrincipalPositivePolynomial] using hf.2.1
  · simpa [n07aCubicPrincipalAtom, n04PrincipalPositivePolynomial] using hf.2.2

theorem n04PrincipalPositive_principal_pairBounds_of_inverse {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (G.Pos η) b ε) (hf : G.FieldData η b ε)
    (hJ : G.n04PrincipalPositivePair η b ε
      (fun z m q => (planeJacobian ((G.V η).inverseChart (G.lift η z) m) q)⁻¹)
      (fun m q => (planeJacobian ((G.V η).inverseChart (G.ref η) m) q)⁻¹))
    (v : Fin 3) :
    G.n04PrincipalPositivePair η b ε
      (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v)) := by
  have hp := n07aParameterGrading_monotone (G.S η)
  have hI := G.n04PrincipalPositive_parameter_interpolation η
  have hU := isOpen_sectorNeighborhood (G.S η) b ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hz0 := G.n04PrincipalPositive_sector_zero η b h.2.1
  have hUne : (sectorNeighborhood (G.S η) b ε ε).Nonempty := ⟨0, hz0⟩
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
  have ha := G.n04PrincipalPositive_coefficient_pairBounds h η href hf 0
  have hb := G.n04PrincipalPositive_coefficient_pairBounds h η href hf 1
  have hc := G.n04PrincipalPositive_coefficient_pairBounds h η href hf 2
  have hH := G.n04PrincipalPositive_height_pairBounds h η href hg
  have hpoly := n04PrincipalPositivePolynomial_pairBounds hp hI hU hΩ hE hW
    ha hb hc hH hJ hRr hRt hTr hTt v
  apply hpoly.congr hΩ
  · intro m z hz q hq
    exact (G.n04PrincipalPositive_principal_polynomial h η hz m.property hq v).symm
  · intro m q hq
    have hzero := G.n04PrincipalPositive_principal_polynomial h η hz0 m.property hq v
    simpa only [atomFamily, atomRef, pulled, pulledRef, pulledHeight, pulledHeightRef,
      heightField, G.n04PrincipalPositive_lift_zero η, Bool.false_eq_true, ↓reduceIte]
      using hzero.symm

/-- A single smaller positive neighborhood supplies all three actual
principal pairs. It is chosen before the component and all jet orders. -/
theorem n04PrincipalPositive_principal_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (G.Pos η) b ε) (hf : G.FieldData η b ε) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      ∀ v : Fin 3, G.n04PrincipalPositivePair η b' ε'
        (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v)) := by
  have hshrink := G.n04PrincipalPositive_inverseJacobianInverse_pairBounds h η href hg
  let b' : ℕ := hshrink.choose
  have hbb' : b ≤ b' := hshrink.choose_spec.1
  let ε' : ℝ := hshrink.choose_spec.2.choose
  have hε' : 0 < ε' := hshrink.choose_spec.2.choose_spec.1
  have hε'ε : ε' ≤ ε := hshrink.choose_spec.2.choose_spec.2.1
  have hhalf : ε' ≤ 1 / 2 := hshrink.choose_spec.2.choose_spec.2.2.1
  have hJ := hshrink.choose_spec.2.choose_spec.2.2.2
  have h' := G.admissible_mono h hbb' hε' hε'ε
  have hg' := G.geometryData_mono η hg (fun _ hm => hm) hbb' hε'ε
  have hf' := G.fieldData_mono η hf hbb' hε'ε
  exact ⟨b', hbb', ε', hε', hε'ε, hhalf, fun v =>
    G.n04PrincipalPositive_principal_pairBounds_of_inverse h' η href hg' hf' hJ v⟩

end N04RealizationGauge

end ContinuousFlexibility.Analysis
