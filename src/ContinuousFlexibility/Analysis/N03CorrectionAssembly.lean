import ContinuousFlexibility.Analysis.ReturnCorrectionSpeedGap
import ContinuousFlexibility.Analysis.ReturnCorrectionOperatorComparison
import ContinuousFlexibility.Analysis.N02ReturnAssembly

/-!
# Assembly of the actual N03 correction

The symmetric coefficients, corrected flow, and independent-residual
source operator share one cutoff family and one neighborhood. Once the
actual source realization and its smooth tame tower are supplied, every
clause of the frozen N03 property follows from the proved geometric and
divergence identities.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.exists_returnCorrection_of_smoothTame_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (hdisc : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (hflow : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
      returnCorrectedMinusFlow S C χ z m (C.left m) θ = θ ∧
      ContinuousOn (fun r => returnCorrectedMinusFlow S C χ z m r θ)
        (Icc (C.left m) (C.right m)) ∧
      (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt
        (fun s => returnCorrectedMinusFlow S C χ z m s θ)
        (minusCharacteristicSpeed (returnCorrectedCoefficients D S C χ z)
          (r, returnCorrectedMinusFlow S C χ z m r θ)) r) ∧
      rightChartCandidate S C z m (returnCorrectedMinusFlow S C χ z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m ∧
      rightChartCandidate S C z m (-returnCorrectedMinusFlow S C χ z m (C.right m) (-θ)) =
        stateLeftChart S z.1 m θ + C.travel m)
    (E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source)
    (hE : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ ρ η p,
      (S.height (3 / 4 : ℝ)).decode (E z ρ η).val p =
        returnCorrectionResidualErrorField D S C R χ z ρ η p)
    (htame : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
      S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
        E (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    ∃ L : ReturnCorrectionData S, L.error = E ∧ N03Properties D T S C R L base ε := by
  let L : ReturnCorrectionData S :=
    { coefficients := returnCorrectedCoefficients D S C χ
      minusFlow := returnCorrectedMinusFlow S C χ
      error := E }
  refine ⟨L, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, hflow, ?_, ?_, htame⟩
  · intro z hz hs p
    rfl
  · intro z hz hs p hp hpositive
    exact returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero D S C χ z p
      (hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hp.1 hpositive.le)
  · intro z hz hs p hp hzero
    exact returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero D S C χ z p
      (hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hp.1
        (by rw [hzero]))
  · intro z hz hs r θ
    exact returnCorrectedCoefficients_parity D S C χ z
      (fun s t => (originalCoefficients_parity_of_physical hS C z s t).1)
      (fun s t => (originalCoefficients_parity_of_physical hS C z s t).2.1)
      (fun s t => (originalCoefficients_parity_of_physical hS C z s t).2.2) r θ
  · intro z hz hs η p hp
    exact (hN.divergenceOperator_returnCorrectedCoefficients hR hS hT hz hs
      χ hχ hχrange hsupp hend (hdisc z hz) η p hp).trans
        (hE z hz hs (R.residual z) η p).symm
  · intro z hz hs ρ η
    exact physicalSourceIntegral_decode_source_eq_zero hS (E z ρ η)

end ContinuousFlexibility.Statements
