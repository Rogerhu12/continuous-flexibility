module

public import ContinuousFlexibility.Analysis.N01DiscriminantGlobalJets
public import ContinuousFlexibility.Analysis.RootCoefficientAxisDivision

/-!
# Uniform jets of the actual divided factor at every root

The discriminant bound is uniform over the original annulus. On the
root axis, exact radial division samples only that same point and costs
one derivative. All numerical constants therefore precede the root,
orientation, smooth factor, state and qualitative strip radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

def N01RootFactorAxisGlobalBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base low outLoss : ℕ) (ε : ℝ)
    (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ r ∈ Ioo D.a D.b, ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R → ∀ n : ℕ, ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n
          (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) (0, θ)‖ ≤
          B n * (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
            (z - (C.referenceState, 0)))

/-- The genuine divided root factor has globally uniform upper jets on
its root axis. Its reciprocal is a separate quantitative input. -/
theorem n01_rootFactor_axis_global_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01RootFactorAxisGlobalBound D S C base low outLoss ε B := by
  obtain ⟨low, outLoss, A, hA, hdiscriminant⟩ :=
    n01_discriminant_global_fixed_loss hS hT hN
  refine ⟨low, outLoss + 1, (fun n => (2 : ℝ) ^ n * A (n + 1)),
    fun n => mul_pos (pow_pos (by norm_num) n) (hA (n + 1)), ?_⟩
  intro z hz hs hlow r hr σ hσ g hg R hR hstrip n θ
  have hwref : ContDiff ℝ ∞ D.w := hN.1.1.choose_spec.1.2.2.1.1
  have hM : 0 ≤ A (n + 1) *
      (1 + pairGrading (stateGrading S) realGrading ((n + 1) + outLoss)
        (z - (C.referenceState, 0))) :=
    mul_nonneg (hA (n + 1)).le (add_nonneg zero_le_one (apply_nonneg _ _))
  have hb := norm_iteratedFDeriv_rootCoefficientRadialFactor_root_le_of_physical_mixed
    hwref hg (contDiff_stateProfile_of_n01 hS hT hN z.1)
    (contDiff_stateHeight_of_n01 hS hT hN z) hσ hR hstrip n θ hM
    (fun a b hab => by
      simpa only [originalCoefficients, hab] using
        hdiscriminant z hz hs hlow a b (r, θ) ⟨hr, mem_univ _⟩)
  have hindex : (n + 1) + outLoss = n + (outLoss + 1) := by omega
  simpa only [hindex, mul_assoc] using hb

end ContinuousFlexibility.Analysis
