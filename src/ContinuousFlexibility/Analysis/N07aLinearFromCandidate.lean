import ContinuousFlexibility.Analysis.N07aLinearAssembly

/-!
# Closing the actual inverse from a bounded physical candidate

The estimate is proved for the original reconstructed candidate. Uniqueness
against every HeightPair transfers it to every normalized solution before
the actual continuous linear inverse is packaged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_exists_scalarLinearInverse_of_boundedCandidate
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (u : CanonicalGeometry.Parameter S → S.Source → HeightPair S × ℝ)
    (hsol : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f,
      N07aScalarSolution D S C L (liftSectorParameter S C z) f (u z f))
    (hbound : ∃ d low : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f,
        n07aOutputGrading S s (u z f) ≤ A *
          (S.sourceGrading (s + d) f +
            (1 + CanonicalGeometry.parameterGrading S (s + d) z) * S.sourceGrading low f))
    (hunique : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : S.Source, ∀ u v : HeightPair S × ℝ,
        N07aScalarSolution D S C L z f u →
        N07aScalarSolution D S C L z f v → u = v) :
    ∃ G : ScalarInverseData S, ScalarLinearInverseProperties D S C L G base ε := by
  have hexists (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
      (hs : stateSector S z.1) (f : S.Source) :
      ∃ v : HeightPair S × ℝ, N07aScalarSolution D S C L z f v := by
    let ζ := n07aSectorParameterOfState h01.2.2.1 z hs
    have hζ : ζ ∈ sectorNeighborhood S base ε ε :=
      n07aSectorParameterOfState_mem h01.2.2.1 hz hs
    refine ⟨u ζ f, ?_⟩
    have h := hsol ζ hζ f
    simpa only [ζ, lift_n07aSectorParameterOfState] using h
  have htame : N07aScalarSolutionTame D S C L base ε := by
    let d : ℕ := hbound.choose
    let low : ℕ := hbound.choose_spec.choose
    have hb := hbound.choose_spec.choose_spec
    refine ⟨d, low, fun s _ => ?_⟩
    let A : ℝ := (hb s).choose
    have hA : 0 < A := (hb s).choose_spec.1
    refine ⟨A, hA.le, fun z hz f v hv => ?_⟩
    have he : v = u z f := hunique (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) f v (u z f) hv (hsol z hz f)
    exact (congrArg (n07aOutputGrading S s) he).le.trans ((hb s).choose_spec.2 z hz f)
  exact n07a_exists_scalarLinearInverse_of_solutions hS hT h01 h02 h03
    hexists hunique htame

end ContinuousFlexibility.Analysis
