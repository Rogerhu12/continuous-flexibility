import ContinuousFlexibility.Analysis.N04PrincipalNegativeReferenceInputs
import ContinuousFlexibility.Analysis.N04PrincipalNegativePotentialExpression
import ContinuousFlexibility.Analysis.N04PrincipalPairAlgebra

/-!
# Paired current jets of the actual negative potential

The negative normal form reduces the potential to a fixed finite
differential expression in pulled height and its reciprocal. Its two
fixed spatial factors are controlled by the same atlas's reference atoms.
The paired calculus retains the height gain in the actual difference.
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

/-- The paired calculus on the negative pieces of this fixed atlas. -/
abbrev n04PrincipalNegativePairBounds
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (base : ℕ) (ε : ℝ)
    (f : Parameter (G.S η) → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  N04PrincipalPairBounds (parameterGrading (G.S η))
    (fun m : {m : ℕ // G.Neg η m} => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)))
    (fun m : {m : ℕ // G.Neg η m} =>
      G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ))
    (U := sectorNeighborhood (G.S η) base ε ε) (Ω := unitStrip)
    (fun m z => f z m.val) (fun m => f₀ m.val)

/-- Every negative stationary principal or divided atom is paired with
its fixed reference. Its actual difference tower vanishes identically. -/
theorem n04PrincipalNegative_stationary_pairBounds {base : ℕ} {ε : ℝ}
    (h : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (a : Atom) (ha : n04PrincipalNegativeStationary a) :
    G.n04PrincipalNegativePairBounds η base ε (G.atomFamily η a) (G.atomRef η a) := by
  let ι : Type := {m : ℕ // G.Neg η m}
  let p := parameterGrading (G.S η)
  let E : ι → ℝ := fun m => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val))
  let W : ι → ℝ := fun m =>
    G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ)
  let U := sectorNeighborhood (G.S η) base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood (G.S η) base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hE (m : ι) : 1 ≤ E m := (G.cost_nonneg η).2.2 m.val
  have hW (m : ι) : 0 ≤ W m := Real.rpow_nonneg ((G.cost_nonneg η).2.1 m.val) _
  have hfixed : N04PrincipalPairBounds p E W (U := U) (Ω := unitStrip)
      (fun m _ => G.atomRef η a m.val) (fun m => G.atomRef η a m.val) := by
    apply N04PrincipalPairBounds.fixedSpatial p E W hU hE hW
      (fun m => G.atomRef η a m.val) (fun m => (href.1 m.val a).1)
    intro s
    refine ⟨(href.2 s).choose, (href.2 s).choose, ?_⟩
    intro m i j hij q hq
    exact (Real.norm_eq_abs _).trans_le
      ((href.2 s).choose_spec.2 m.val a q hq i j hij)
  apply hfixed.congr hΩ
  · intro m z hz q hq
    exact (G.n04PrincipalNegative_stationary_eqOn h η hz m.val m.property a ha hq).symm
  · intro m q _
    rfl

/-- Genuine full, reference and difference towers of the actual negative
potential, with one low order before all spatial and parameter orders. -/
theorem n04PrincipalNegative_potential_pairBounds {base : ℕ} {ε : ℝ}
    (h : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hI : HasInterpolation (parameterGrading (G.S η)))
    (hweight : ∀ m, G.Neg η m →
      0 < G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ))
    (hH : G.n04PrincipalNegativePairBounds η base ε
      (G.pulledHeight η) (G.pulledHeightRef η))
    (hQ : G.n04PrincipalNegativePairBounds η base ε
      (fun z m q => (G.pulledHeight η z m q)⁻¹)
      (fun m q => (G.pulledHeightRef η m q)⁻¹)) :
    G.n04PrincipalNegativePairBounds η base ε
      (G.atomFamily η .potential) (G.atomRef η .potential) := by
  let ι : Type := {m : ℕ // G.Neg η m}
  let p := parameterGrading (G.S η)
  let E : ι → ℝ := fun m => G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val))
  let W : ι → ℝ := fun m =>
    G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ)
  let U := sectorNeighborhood (G.S η) base ε ε
  have hp : Monotone p := n07aParameterGrading_monotone (G.S η)
  have hU : IsOpen U := isOpen_sectorNeighborhood (G.S η) base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hE (m : ι) : 1 ≤ E m := (G.cost_nonneg η).2.2 m.val
  have hW (m : ι) : 0 < W m := hweight m.val m.property
  have hW0 (m : ι) : 0 ≤ W m := (hW m).le
  have hparts := G.n04PrincipalPositive_admissible_parts h η
  have hA := hparts.1
  have hB := hparts.2.1
  have hzref : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) base ε :=
    reference_mem_stateNeighborhood (G.S η) (G.C η) base h.2.1
  have hsref : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  have hlength := n04PrincipalNegative_inverseLengthSquare_reference_bound href
    (G.cost_nonneg η).2.2
  let ell : ι → PolarPoint → ℝ := fun m _ =>
    ((G.V η).right m.val - (G.V η).left m.val)⁻¹ ^ 2
  have hEll : N04PrincipalPairBounds p E W (U := U) (Ω := unitStrip)
      (fun m _ => ell m) ell := by
    apply N04PrincipalPairBounds.fixedSpatial p E W hU hE hW0 ell
      (fun _ => contDiffOn_const)
    intro s
    refine ⟨hlength.choose, hlength.choose, ?_⟩
    intro m a b _ q _
    exact (Real.norm_eq_abs _).trans_le (hlength.choose_spec.2 m.val a b q)
  have hradial := n04PrincipalNegative_canonicalRadial_reference_bound
    hA hB href hzref hsref
  let radial : ι → PolarPoint → ℝ := fun m q => (canonicalUnitPoint (G.V η) m.val q).1
  have hRadial : N04PrincipalPairBounds p E W (U := U) (Ω := unitStrip)
      (fun m _ => radial m) radial := by
    apply N04PrincipalPairBounds.fixedSpatial p E W hU hE hW0 radial
      (fun m => (n04PrincipalNegative_canonicalRadial_smooth (K := G.V η) m.val).contDiffOn)
    intro s
    refine ⟨(hradial s).choose, (hradial s).choose, ?_⟩
    intro m a b hab q hq
    exact (Real.norm_eq_abs _).trans_le
      ((hradial s).choose_spec.2 m.val m.property q hq a b hab)
  have hrr := (hQ.coordinatePartial hΩ true).coordinatePartial hΩ true
  have htt := (hQ.coordinatePartial hΩ false).coordinatePartial hΩ false
  have hleft := hEll.mul hrr hp hI hU hΩ hE hW
  have hright := hRadial.mul htt hp hI hU hΩ hE hW
  have hoperator := hleft.sub hright hp hU hΩ hE hW0
  have hpotential := (hH.neg hU hΩ).mul hoperator hp hI hU hΩ hE hW
  apply hpotential.congr hΩ
  · intro m z hz q hq
    have hw : G.lift η z ∈ stateNeighborhood (G.S η) (G.C η) base ε :=
      liftSectorParameter_mem_stateNeighborhood hz le_rfl
    have hs : stateSector (G.S η) (G.lift η z).1 :=
      G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
    exact (n04PrincipalNegative_potential_partial_formula
      hA hB hw hs m.val m.property hq).symm
  · intro m q hq
    exact (n04PrincipalNegative_potential_partial_formula
      hA hB hzref hsref m.val m.property hq).symm

end N04RealizationGauge

end ContinuousFlexibility.Analysis
