import ContinuousFlexibility.Analysis.ReturnCorrectionHeightMember
import ContinuousFlexibility.Analysis.N01FlowInverseJetBounds
import ContinuousFlexibility.Analysis.ReturnCorrectionSpeedGap

/-!
# One actual optical cutoff family yields physical source members

The collar family is selected from the reference profile, then the
original N01 neighborhood is restricted once more to control every
actual inverse flow. The exact independent-residual error has all
weighted physical jets in L² for every residual and height input.
No source-membership or extra regularity condition is assumed.

The quantitative collar witnesses are retained for the subsequent
parameter-jet estimates on this same family.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem N01Properties.exists_opticalCorrection_source_members
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ, ∃ j : ℕ → ℕ,
      ∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
        0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
        (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
        ∀ r ∈ Icc (x m - δ m) (x m + δ m),
          radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
      (∀ m, χ m = returnOpticalCutoff (x m) (δ m)) ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m)) ∧
      (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
        |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ Icc (x m - δ m) (x m + δ m) →
        let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
        0 < d ∧
        d ≤ (originalCoefficients D S C z).a p ∧
        d ≤ -(originalCoefficients D S C z).c p ∧
        d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        (∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2) ∧
        (∀ n : ℕ, 1 ≤ n → ∃ K : ℝ, 0 ≤ K ∧ ∀ m θ,
          |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ K) ∧
        (∀ m θ,
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
        ∀ (R : ReturnEquationData S) (ρ : CircleSpace S) (η : HeightPair S),
          HeightMember D T (3 / 4 : ℝ) (returnCorrectionResidualErrorField D S C R χ z ρ η) := by
  obtain ⟨base₁, ε₁, χ, hb₁, hε₁, hε₁ε, hN₁, hχ, hendI, hcollars,
    hdisc, hcorrected⟩ := hN.exists_opticalCorrection_flow hS hT
  obtain ⟨j, x, δ, K, A, B, lam, P, hK, hA, hB, hlam, hP,
    hdata, hχeq, hsupp, hjets, hpositive⟩ := hcollars
  have hend (m : ℕ) :
      χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
      tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m) :=
    ⟨(hendI m).1, (hendI m).2.1, hsupp m⟩
  obtain ⟨base₂, ε₂, hb₂, hε₂, hε₂ε₁, hN₂, hinverse⟩ :=
    hN₁.exists_uniform_inverse_angular_jets hS hT
  refine ⟨base₂, ε₂, χ, j, x, δ, K, A, B, lam, P, hb₁.trans hb₂,
    hε₂, hε₂ε₁.trans hε₁ε, hK, hA, hB, hlam, hP, hN₂,
    hdata, hχeq, hχ, hend, hjets, ?_, ?_⟩
  · intro z hz m p hp
    exact hpositive z (stateNeighborhood_mono S C hb₂ hε₂ε₁ hz) m p hp
  · intro z hz hsector
    obtain ⟨hflow, hinv⟩ := hinverse z hz hsector
    have hendpoint (n : ℕ) (hn : 1 ≤ n) : ∃ K : ℝ, 0 ≤ K ∧ ∀ m θ,
        |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ K := by
      obtain ⟨K, hK, _, he⟩ := hinv n hn
      exact ⟨K, hK, he⟩
    have hz₁ : z ∈ stateNeighborhood S C base₁ ε₁ :=
      stateNeighborhood_mono S C hb₂ hε₂ε₁ hz
    refine ⟨hflow, hendpoint, hcorrected z hz₁ hsector, fun R ρ η => ?_⟩
    have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) := (hdata m).1
    have hδ (m : ℕ) : 0 < δ m := (hdata m).2.1
    have hinside (m : ℕ) : C.left m < x m - δ m ∧ x m + δ m < C.right m :=
      ⟨(hdata m).2.2.1, (hdata m).2.2.2.1⟩
    have hspeed (m : ℕ) (r : ℝ) (hr : r ∈ Icc (x m - δ m) (x m + δ m)) :
        radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r :=
      (hdata m).2.2.2.2.2 r hr
    have hlower (m : ℕ) (p : PolarPoint)
        (hp : p.1 ∈ Icc (x m - δ m) (x m + δ m)) :
        (lam / 2) ^ 2 * radialE (D.cellIndex (j m)) ^ (-(2 * P)) ≤
          (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
      have hpow : radialE (D.cellIndex (j m)) ^ (-(2 * P)) =
          (radialE (D.cellIndex (j m)) ^ (-P)) ^ 2 := by
        rw [pow_two, ← Real.rpow_add (Real.exp_pos _)]
        congr 1
        ring
      have hscale : (lam / 2) ^ 2 * radialE (D.cellIndex (j m)) ^ (-(2 * P)) =
          (lam * radialE (D.cellIndex (j m)) ^ (-P) / 2) ^ 2 := by
        rw [hpow]
        ring
      exact hscale.trans_le (hpositive z hz₁ m p hp).2.2.2.1
    have hcutoff (n : ℕ) : ∃ Kₙ Pₙ : ℝ, 0 ≤ Kₙ ∧ 0 ≤ Pₙ ∧ ∀ m r,
        |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ Pₙ := by
      obtain ⟨Kₙ, hKₙ, hb⟩ := hjets n
      exact ⟨Kₙ, A * n, hKₙ.le, mul_nonneg hA.le (Nat.cast_nonneg _), hb⟩
    exact hN₂.returnCorrectionResidualErrorField_heightMember_of_collar
      hS hT R hz hsector j x δ hδ hcell hinside χ (fun m => (hχ m).1)
      (fun m r => (hχ m).2 r) (fun m => (hend m).2.2)
      (fun m => ⟨(hend m).1, (hend m).2.1⟩)
      (sq_pos_of_pos (div_pos hlam (by norm_num)))
      (mul_nonneg (by norm_num) hP.le) hB hlower hspeed hcutoff hflow hendpoint ρ η

end ContinuousFlexibility.Statements
