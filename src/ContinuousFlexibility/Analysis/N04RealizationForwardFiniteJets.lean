import ContinuousFlexibility.Analysis.FiniteInverseMaterialBounds
import ContinuousFlexibility.Analysis.N04RealizationForwardE0Bounds
import ContinuousFlexibility.Analysis.N04RealizationInverseE0Bounds
import ContinuousFlexibility.Analysis.N07aActualChartDifferentials
import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# Finite forward jets on the actual moving physical pieces

One smaller state neighborhood controls the first forward differential.
The positive jets of the genuine inverse then give every finite forward
jet prefix on that same neighborhood. The sampled E0 power is retained,
and the state dependence is a finite polynomial at a finite grading order.
No zeroth-order bound on the unwrapped angular coordinate is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency true

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
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- The neighborhood is chosen before the requested finite order. All
positive forward jets are estimated on their genuine moving domains with
the original sampled coefficient envelope. -/
theorem n04Realization_forwardChart_finite_E0_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ N : ℕ, ∃ r d : ℕ, ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
        ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
          ∀ m x, x ∈ physicalPieceOpen S K z m → ∀ k : ℕ, 1 ≤ k → k ≤ N →
            ‖iteratedFDeriv ℝ k (K.chart z m) x‖ ≤
              C₀ * T.E0 (T.sample (K.cell m)) ^ A *
                (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d := by
  obtain ⟨base', hb, η, hη, hηε, B₀, hB₀, hfirst⟩ :=
    n04Realization_actualForwardFirstE0_neighborhood hD hT hε hrefState
      hgeom href hcur hfloor
  obtain ⟨dInv, hinverseJets⟩ :=
    n04Realization_inverseChart_positive_E0_jets hD hT hrefState href hcur
      (fun m => (hgeom.referenceBounds m).2.1)
      (fun m => (hgeom.referenceBounds m).1) hfloor
  let U : Set (AnnularState S × ℝ) :=
    {z | z ∈ stateNeighborhood S C base' η ∧ stateSector S z.1}
  let Ω : (AnnularState S × ℝ) → ℕ → Set PolarPoint :=
    fun z m => physicalPieceOpen S K z m
  let W : ℕ → ℝ := fun m => T.E0 (T.sample (K.cell m))
  let rho : ℕ → (AnnularState S × ℝ) → ℝ :=
    fun r z => 1 + stateGrading S r (z.1 - C.referenceState) + |z.2|
  have hUold (z : AnnularState S × ℝ) (hz : z ∈ U) :
      z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb hηε hz.1
  have hrho (r : ℕ) (z : AnnularState S × ℝ) (_hz : z ∈ U) : 1 ≤ rho r z := by
    dsimp only [rho]
    linarith only [apply_nonneg (stateGrading S r) (z.1 - C.referenceState),
      abs_nonneg z.2]
  have hrhoMono (z : AnnularState S × ℝ) (_hz : z ∈ U) :
      Monotone (fun r => rho r z) := by
    intro a b hab
    dsimp only [rho]
    linarith only [stateGrading_monotone S hab (z.1 - C.referenceState)]
  have hforward : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      ContDiffAt ℝ ∞ (K.chart z m) x := by
    intro z hz m x hx
    exact (hgeom.charts z (hUold z hz) hz.2 m).2.2.2.2.1.contDiffAt
      ((hgeom.domains z (hUold z hz) hz.2 m).1.mem_nhds hx)
  have hinverse : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      ContDiffAt ℝ ∞ (K.inverseChart z m) (K.chart z m x) := by
    intro z hz m x hx
    have hc := hgeom.charts z (hUold z hz) hz.2 m
    exact hc.2.2.2.2.2.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hc.1 hx))
  have hgerm : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      K.inverseChart z m ∘ K.chart z m =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) := by
    intro z hz m x hx
    have hc := hgeom.charts z (hUold z hz) hz.2 m
    have hΩ : IsOpen (physicalPieceOpen S K z m) :=
      (hgeom.domains z (hUold z hz) hz.2 m).1
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hc.2.2.1 y hy
  have hleft : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      (fderiv ℝ (K.chart z m) x).comp
          (fderiv ℝ (K.inverseChart z m) (K.chart z m x)) =
        ContinuousLinearMap.id ℝ PolarPoint := by
    intro z hz m x hx
    have hc := hgeom.charts z (hUold z hz) hz.2 m
    simpa only [hc.2.2.1 x hx] using
      (n07a_actualChart_fderiv_inverse hgeom (hUold z hz) hz.2 m (hc.1 hx)).1
  have hfirstState : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      ‖fderiv ℝ (K.chart z m) x‖ ≤ B₀ * W m ^ B₀ := by
    intro z hz m x hx
    let ζ : Parameter S := n06PrimitiveParameterOfState hrefState z hz.2
    have hζ : ζ ∈ sectorNeighborhood S base' η η :=
      n06PrimitiveParameterOfState_mem hrefState hz.1 hz.2
    have hlift : liftSectorParameter S C ζ = z :=
      n06PrimitiveParameterOfState_lift hrefState z hz.2
    have hxζ : x ∈ physicalPieceOpen S K (liftSectorParameter S C ζ) m := by
      simpa only [hlift] using hx
    simpa only [hlift] using hfirst ζ hζ m x hxζ
  have hjets : ∀ n : ℕ, 2 ≤ n → ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
        ‖iteratedFDeriv ℝ n (K.inverseChart z m) (K.chart z m x)‖ ≤
          B * W m ^ B * rho (n + dInv) z := by
    intro n hn
    obtain ⟨B, hB, hbound⟩ := hinverseJets n (by omega)
    refine ⟨B, hB, ?_⟩
    intro z hz m x hx
    exact hbound z (hUold z hz) hz.2 m (K.chart z m x)
      ((hgeom.charts z (hUold z hz) hz.2 m).1 hx)
  have hfinite := nonlinearInverse_finitePrefix_weighted_bound
    U Ω W rho K.chart K.inverseChart dInv hB₀ hfloor hrho hrhoMono
      hforward hinverse hgerm hleft hfirstState hjets
  refine ⟨base', hb, η, hη, hηε, ?_⟩
  intro N
  obtain ⟨d, C₀, A, hC₀, hA, hbound⟩ := hfinite N
  refine ⟨N + dInv, d, C₀, A, hC₀, hA, ?_⟩
  intro z hz hs m x hx k hk hkN
  exact hbound z ⟨hz, hs⟩ m x hx k hk hkN

end ContinuousFlexibility.Analysis
