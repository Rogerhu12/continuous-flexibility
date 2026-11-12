import ContinuousFlexibility.Analysis.N07aScalarSolution
import ContinuousFlexibility.Analysis.TameLinear
import ContinuousFlexibility.Statements.N07aRegularity

/-!
# Packaging unique physical solutions as the actual continuous linear inverse

This internal assembly takes existence, uniqueness among all common-height
candidates, and one uniform physical estimate.  Linearity follows from
the actual equation.  Continuity follows from that estimate and the
prescribed seminorm topologies.  No continuous or linear choice of
solutions is assumed.
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

/-- A single fixed-loss estimate for the actual normalized solutions. -/
def N07aScalarSolutionTame (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  ∃ d low : ℕ, ∀ s : ℕ, low ≤ s → ∃ C0 : ℝ, 0 ≤ C0 ∧
    ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f : S.Source, ∀ u : HeightPair S × ℝ,
      N07aScalarSolution D S C L (liftSectorParameter S C z) f u →
      n07aOutputGrading S s u ≤ C0 *
        (S.sourceGrading (s + d) f +
          (1 + n07aParameterGrading S (s + d) z) * S.sourceGrading low f)

private theorem n07a_oneHigh_fixed_parameter_bound {hi lo a C0 : ℝ}
    (hlo : lo ≤ hi) (ha : 0 ≤ a) (hC : 0 ≤ C0) :
    C0 * (hi + a * lo) ≤ (C0 * (1 + a)) * hi := by
  calc
    C0 * (hi + a * lo) ≤ C0 * (hi + a * hi) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlo ha)) hC
    _ = _ := by ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- All premises are physical conclusions to be supplied by the Banach
solution, its Height realization, and the all-candidate uniqueness proof. -/
theorem n07a_exists_scalarLinearInverse_of_solutions
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (hexists : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : S.Source, ∃ u : HeightPair S × ℝ, N07aScalarSolution D S C L z f u)
    (hunique : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : S.Source, ∀ u v : HeightPair S × ℝ,
        N07aScalarSolution D S C L z f u →
        N07aScalarSolution D S C L z f v → u = v)
    (hbound : N07aScalarSolutionTame D S C L base ε) :
    ∃ G : ScalarInverseData S, ScalarLinearInverseProperties D S C L G base ε := by
  classical
  let U := stateNeighborhood S C base ε
  let chosen : (z : AnnularState S × ℝ) → z ∈ U → stateSector S z.1 →
      S.Source → (HeightPair S × ℝ) :=
    fun z hz hs f => (hexists z hz hs f).choose
  have hchosen (z : AnnularState S × ℝ) (hz : z ∈ U) (hs : stateSector S z.1)
      (f : S.Source) : N07aScalarSolution D S C L z f (chosen z hz hs f) :=
    (hexists z hz hs f).choose_spec
  let V : (z : AnnularState S × ℝ) → z ∈ U → stateSector S z.1 →
      S.Source →ₗ[ℝ] (HeightPair S × ℝ) := fun z hz hs =>
    { toFun := chosen z hz hs
      map_add' := fun f g => hunique z hz hs (f + g) _ _
        (hchosen z hz hs (f + g))
        (n07aScalarSolution_add hS hT h01 h02 h03 hz hs
          (hchosen z hz hs f) (hchosen z hz hs g))
      map_smul' := fun c f => hunique z hz hs (c • f) _ _
        (hchosen z hz hs (c • f))
        (n07aScalarSolution_smul hS hT h01 h02 h03 hz hs (hchosen z hz hs f) c) }
  have hVsolution (z : AnnularState S × ℝ) (hz : z ∈ U)
      (hs : stateSector S z.1) (f : S.Source) :
      N07aScalarSolution D S C L z f (V z hz hs f) := hchosen z hz hs f
  let d : ℕ := hbound.choose
  let low : ℕ := hbound.choose_spec.choose
  have hb := hbound.choose_spec.choose_spec
  have hlocal (z : AnnularState S × ℝ) (hz : z ∈ U) (hs : stateSector S z.1) :
      IsTameLinear S.sourceGrading (n07aOutputGrading S) (V z hz hs) d low := by
    let ζ := n07aSectorParameterOfState h01.2.2.1 z hs
    have hζ : ζ ∈ sectorNeighborhood S base ε ε :=
      n07aSectorParameterOfState_mem h01.2.2.1 hz hs
    intro s hslow
    let data := hb s hslow
    let C0 : ℝ := data.choose
    have hC0 : 0 ≤ C0 := data.choose_spec.1
    let a : ℝ := 1 + n07aParameterGrading S (s + d) ζ
    have ha : 0 ≤ a := add_nonneg zero_le_one
      (apply_nonneg (n07aParameterGrading S (s + d)) ζ)
    refine ⟨⟨C0 * (1 + a), mul_nonneg hC0 (add_nonneg zero_le_one ha)⟩, ?_⟩
    intro f
    have hsol : N07aScalarSolution D S C L (liftSectorParameter S C ζ) f
        (V z hz hs f) := by
      simpa only [ζ, lift_n07aSectorParameterOfState] using hVsolution z hz hs f
    have hraw := data.choose_spec.2 ζ hζ f (V z hz hs f) hsol
    have hlo : S.sourceGrading low f ≤ S.sourceGrading (s + d) f :=
      n07aSourceGrading_monotone S (hslow.trans (Nat.le_add_right s d)) f
    exact hraw.trans (n07a_oneHigh_fixed_parameter_bound hlo ha hC0)
  let G : ScalarInverseData S :=
    { G := fun z => if hz : z ∈ U ∧ stateSector S z.1 then
        (hlocal z hz.1 hz.2).toContinuousLinearMap
          (n07aSourceGrading_withSeminorms S)
          (n07aOutputGrading_withSeminorms S) (n07aOutputGrading_monotone S)
      else 0 }
  have hG (z : AnnularState S × ℝ) (hz : z ∈ U) (hs : stateSector S z.1)
      (f : S.Source) : G.G z f = V z hz hs f := by
    simp only [G, dif_pos (show z ∈ U ∧ stateSector S z.1 from ⟨hz, hs⟩),
      IsTameLinear.toContinuousLinearMap_apply]
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z hz hs f
    exact Eq.mp (congrArg (N07aScalarSolution D S C L z f) (hG z hz hs f).symm)
      (hVsolution z hz hs f)
  · intro z hz hs η μ f hrow heq
    exact (hG z hz hs f).trans
      (hunique z hz hs f _ (η, μ) (hVsolution z hz hs f) ⟨hrow, heq⟩)
  · refine ⟨d, low, ?_⟩
    intro s hslow
    let data := hb s hslow
    refine ⟨data.choose, data.choose_spec.1, ?_⟩
    intro z hz f
    have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
    have hs := h01.2.2.1.liftSectorParameter_sector z
    apply data.choose_spec.2 z hz f (G.G (liftSectorParameter S C z) f)
    exact Eq.mp (congrArg (N07aScalarSolution D S C L (liftSectorParameter S C z) f)
      (hG _ hz' hs f).symm) (hVsolution _ hz' hs f)

end ContinuousFlexibility.Analysis
