module

public import ContinuousFlexibility.Analysis.N04PrincipalNegativePotential
public import ContinuousFlexibility.Analysis.N07aCanonicalOpenTests

/-!
# Periodicity of the negative principal fields

Stationary atoms inherit their reference periodicity. The actual
potential is a finite expression in pulled height, its reciprocal, and
their spatial derivatives; all of these preserve the same angular
period on the open unit strip.
-/

@[expose] public section

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

/-- The unit strip is a canonical open interval with endpoints zero and
one. No positive-piece hypothesis is needed for derivative periodicity. -/
theorem n04PrincipalNegative_unitStrip_mixedDerivative_periodic
    {S : PhysicalSpacesData} (K : CanonicalData S) {f : PolarPoint → ℝ}
    (hf : ∀ q ∈ unitStrip, f (q + (0, Real.pi)) = f q) (i j : ℕ) :
    ∀ q ∈ unitStrip,
      mixedDerivative i j f (q + (0, Real.pi)) = mixedDerivative i j f q := by
  let K' : CanonicalData S := { K with left := fun _ => 0, right := fun _ => 1 }
  exact n07a_mixedDerivative_periodic_on (K := K') (m := 0) hf i j

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalNegative_stationary_periodic {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Neg η m) (a : Atom) (ha : n04PrincipalNegativeStationary a) :
    ∀ q ∈ unitStrip,
      G.atomFamily η a z m (q + (0, Real.pi)) = G.atomFamily η a z m q := by
  have he := G.n04PrincipalNegative_stationary_eqOn h η hz m hm a ha
  intro q hq
  have hq' : q + (0, Real.pi) ∈ unitStrip := by
    exact ⟨by simpa only [Set.mem_Ioo, Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  exact (he hq').trans (((href.1 m a).2 q hq).trans (he hq).symm)

theorem n04PrincipalNegative_potential_periodic {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (hg : G.GeometryData η (G.Neg η) b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Neg η m) :
    ∀ q ∈ unitStrip,
      G.atomFamily η .potential z m (q + (0, Real.pi)) =
        G.atomFamily η .potential z m q := by
  let V : PolarPoint → ℝ := fun p => (G.pulledHeight η z m p)⁻¹
  have hH := (hg.2.1 z hz m hm).2
  have hV : ∀ q ∈ unitStrip, V (q + (0, Real.pi)) = V q := by
    intro q hq
    exact congrArg (fun t : ℝ => t⁻¹) (hH q hq)
  have hVrr := n04PrincipalNegative_unitStrip_mixedDerivative_periodic (G.V η) hV 2 0
  have hVtt := n04PrincipalNegative_unitStrip_mixedDerivative_periodic (G.V η) hV 0 2
  have hparts := G.n04PrincipalPositive_admissible_parts h η
  have hw : G.lift η z ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector (G.S η) (G.lift η z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  intro q hq
  have hq' : q + (0, Real.pi) ∈ unitStrip := by
    exact ⟨by simpa only [Set.mem_Ioo, Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have hform := n04PrincipalNegative_potential_unit_formula (T := G.W.U)
    hparts.1 hparts.2.1 hw hs m hm hq
  have hform' := n04PrincipalNegative_potential_unit_formula (T := G.W.U)
    hparts.1 hparts.2.1 hw hs m hm hq'
  change G.atomFamily η .potential z m q = -G.pulledHeight η z m q *
    (((G.V η).right m - (G.V η).left m)⁻¹ ^ 2 * mixedDerivative 2 0 V q -
      (canonicalUnitPoint (G.V η) m q).1 * mixedDerivative 0 2 V q) at hform
  change G.atomFamily η .potential z m (q + (0, Real.pi)) =
    -G.pulledHeight η z m (q + (0, Real.pi)) *
      (((G.V η).right m - (G.V η).left m)⁻¹ ^ 2 *
        mixedDerivative 2 0 V (q + (0, Real.pi)) -
        (canonicalUnitPoint (G.V η) m (q + (0, Real.pi))).1 *
          mixedDerivative 0 2 V (q + (0, Real.pi))) at hform'
  have hradial : (canonicalUnitPoint (G.V η) m (q + (0, Real.pi))).1 =
      (canonicalUnitPoint (G.V η) m q).1 := by
    simp only [canonicalUnitPoint, Prod.fst_add, add_zero]
  rw [hH q hq, hVrr q hq, hVtt q hq, hradial] at hform'
  exact hform'.trans hform.symm

end N04RealizationGauge

end ContinuousFlexibility.Analysis
