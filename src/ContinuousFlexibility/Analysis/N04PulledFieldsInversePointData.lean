import ContinuousFlexibility.Analysis.N04PulledFieldsInversePointPrefix

/-!
# Actual inverse-point data on every sufficiently small neighborhood

One low order is chosen from the current geometry and the same reference
certificate. Genuine inverse towers are restricted to stronger low-order
neighborhoods. Their derivatives stay unchanged, while monotonicity of
the parameter grading supplies the stronger low and high conditions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

/-- Genuine joint towers of the retained inverse point with their
parameter-budget prefix, on one fixed state neighborhood. -/
structure N04PulledFieldsInversePointData
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (base : ℕ) (ε : ℝ) where
  joint : ∀ m, SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
    (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2)
  prefix : ∀ K : ℕ, ∃ offset : ℕ, ∀ N : ℕ,
    ∃ M A : ℝ, 1 ≤ M ∧ 0 ≤ A ∧
    ∀ m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
    ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R →
    parameterGrading (G.S η) (base + N + offset + 1) z ≤ R →
    ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
    ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
    (∀ i, parameterGrading (G.S η) base (v i).1 ≤ 1) →
    (∀ i, parameterGrading (G.S η) (base + N + offset + 1) (v i).1 ≤ R) →
    (∀ i, ‖(v i).2‖ ≤ 1) →
    (∀ i, w.isState i = false → (v i).1 = 0) →
    (∀ i, w.isState i = true → (v i).2 = 0) →
      ‖(joint m).D n (z, q) v‖ ≤
        M * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
          parameterHeightWeight
            (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
          (R ^ (1 / (((N + offset : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset)

/-- The inverse data are available on every stronger low-order
neighborhood whose radius is at most one half and at most the input
radius. This choice precedes all parameter and spatial orders. -/
theorem n04PulledFields_inversePoint_neighborhood
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η) :
    ∃ low : ℕ, base ≤ low ∧ ∀ base' : ℕ, ∀ ε' : ℝ,
      low ≤ base' → ε' ≤ ε → ε' ≤ 1 / 2 →
      Nonempty (N04PulledFieldsInversePointData G η base' ε') := by
  refine (n04PulledFields_inversePoint_prefix G η hadm hgeo href).elim fun low hlow => ?_
  refine ⟨low, hlow.1, fun base' ε' hl hε hhalf => ?_⟩
  have hb : base ≤ base' := hlow.1.trans hl
  have hsub : sectorNeighborhood (G.S η) base' ε' ε' ⊆
      sectorNeighborhood (G.S η) base ε ε := sectorNeighborhood_mono (G.S η) hb hε hε
  have hU : IsOpen (sectorNeighborhood (G.S η) base' ε' ε') :=
    isOpen_sectorNeighborhood (G.S η) base' ε' ε'
  let J0 : ∀ m, SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2) :=
    fun m => n04PulledFields_admissible_inversePoint_jointDirections G η hadm hgeo href m
  let J : ∀ m, SmoothDirections (sectorNeighborhood (G.S η) base' ε' ε' ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2) :=
    fun m => (J0 m).restrict (hU.prod (isOpen_Ioo.prod isOpen_univ))
      (fun _ hz => ⟨hsub hz.1, hz.2⟩)
  refine ⟨{ joint := J, prefix := ?_ }⟩
  intro K
  refine (hlow.2 K).elim fun offset hoffset => ⟨offset, fun N => ?_⟩
  refine (hoffset N).elim fun M hM => hM.elim fun A hMA => ?_
  refine ⟨M, A, hMA.1, hMA.2.1, ?_⟩
  intro m z hz q hq R hR hzR n hn hnN w hw v hvlow hvR hvphys hvstate hvangle
  have hsmall : parameterGrading (G.S η) low z ≤ 1 :=
    (n07aParameterGrading_monotone (G.S η) hl z).trans
      (n04PulledFields_parameterGrading_le_one (G.S η) hhalf hz)
  have hhigh : low + N + offset + 1 ≤ base' + N + offset + 1 := by omega
  exact hMA.2.2 m (J0 m) z (hsub hz) hsmall q hq R hR
    ((n07aParameterGrading_monotone (G.S η) hhigh z).trans hzR) n hn hnN w hw v
    (fun i => (n07aParameterGrading_monotone (G.S η) hl (v i).1).trans (hvlow i))
    (fun i => (n07aParameterGrading_monotone (G.S η) hhigh (v i).1).trans (hvR i))
    hvphys hvstate hvangle

end ContinuousFlexibility.Analysis
