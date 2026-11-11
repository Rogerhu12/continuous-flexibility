import ContinuousFlexibility.Analysis.ReturnCorrectionBufferedCollars
import ContinuousFlexibility.Analysis.N01FlowInverseJetBounds
import ContinuousFlexibility.Analysis.NonlinearNeighborhoodRestriction

/-!
# One common buffered cutoff and uniform inverse neighborhood

The buffered cutoff, all collar witnesses, and the actual correction
flow are retained. A further restriction of the same N01 neighborhood
gives the common first-angular-derivative bounds required by the genuine
selector-uniform circle estimates. Any previously constructed N02
operator is retained by `N02Properties.restrict_neighborhood`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

local instance returnCorrectionUniformNeighborhoodStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem N01Properties.exists_opticalCorrection_flow_buffered_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
      (∃ j : ℕ → ℕ, ∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
        0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
        (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
          0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
          (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
          ∀ r ∈ Icc (x m - δ m) (x m + δ m),
            radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
        (∀ m, χ m = returnOpticalCutoff (x m) (δ m / 2)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Icc (x m - δ m / 2) (x m + δ m / 2)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Ioo (x m - δ m) (x m + δ m)) ∧
        (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
          |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
          p.1 ∈ Icc (x m - δ m) (x m + δ m) →
          let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
          0 < d ∧ d ≤ (originalCoefficients D S C z).a p ∧
          d ≤ -(originalCoefficients D S C z).c p ∧
          d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
          0 < (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ tsupport (deriv (χ m)) →
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 → ∀ m θ,
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
          stateLeftChart S z.1 m θ + C.travel m) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧
          deriv (C.minusFlow z m r) θ ≤ 3 / 2) ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε',
        ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
          deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2 := by
  obtain ⟨b₀, ε₀, χ, hb₀, hε₀, hε₀ε, hN₀, hχ, hend, hcollar,
    hdisc, hcorrected⟩ := hN.exists_opticalCorrection_flow_buffered hS hT
  obtain ⟨b₁, ε₁, hb₁, hε₁, hε₁₀, hN₁, hinverse⟩ :=
    hN₀.exists_uniform_inverse_angular_jets hS hT
  have hsub : stateNeighborhood S C b₁ ε₁ ⊆ stateNeighborhood S C b₀ ε₀ :=
    stateNeighborhood_mono S C hb₁ hε₁₀
  have hflow : ∀ z ∈ stateNeighborhood S C b₁ ε₁, stateSector S z.1 →
      ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧
        deriv (C.minusFlow z m r) θ ≤ 3 / 2 :=
    fun z hz hs => (hinverse z hz hs).1
  refine ⟨b₁, ε₁, χ, hb₀.trans hb₁, hε₁, hε₁₀.trans hε₀ε,
    hN₁, hχ, hend, ?_, (fun z hz => hdisc z (hsub hz)),
    (fun z hz => hcorrected z (hsub hz)), hflow, ?_⟩
  · obtain ⟨j, x, δ, K, A, B, lam, P, hK, hA, hB, hlam, hP,
      hdata, heq, hsupp, hbuffer, hjets, hpositive⟩ := hcollar
    exact ⟨j, x, δ, K, A, B, lam, P, hK, hA, hB, hlam, hP,
      hdata, heq, hsupp, hbuffer, hjets, fun z hz => hpositive z (hsub hz)⟩
  · intro z hz
    exact hflow (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN₁.2.2.1.liftSectorParameter_sector z)

end ContinuousFlexibility.Statements
