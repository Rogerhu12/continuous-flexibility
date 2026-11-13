import ContinuousFlexibility.Analysis.N01OriginalCoefficientGlobalJets
import ContinuousFlexibility.Analysis.CoefficientDiscriminantMaterialBounds
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# One common global bound for the actual coefficient discriminant

The coefficient estimates are uniform over the original physical
annulus. Smooth representatives are used only for their exact germs at
the evaluation point, so their cutoff radii incur no derivative cost.
The existing polynomial closure preserves one high state seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

def N01DiscriminantGlobalBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base low outLoss : ℕ) (ε : ℝ)
    (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ a b : ℕ, ∀ q ∈ annularOpen D,
      |mixedDerivative a b
        (fun x => (originalCoefficients D S C z).b x ^ 2 -
          (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x) q| ≤
        B (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
          (z - (C.referenceState, 0)))

/-- All constants precede every point and component of the physical
annulus. Neither a cell nor a local geometric radius enters the bound. -/
theorem n01_discriminant_global_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01DiscriminantGlobalBound D S C base low outLoss ε B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hmaterial⟩ :=
    coefficientDiscriminant_fixed_loss_material_bound hp hI loss
  choose A hA hraw using fun n => originalCoefficient_global_bound_of_n01 hS hT hN n
  let M : ℕ → ℝ := fun n => 1 + A n
  have hM (n : ℕ) : 1 ≤ M n := le_add_of_nonneg_right (hA n).le
  choose Q hQ hbound using hmaterial M hM
  let B : ℕ → ℝ := fun n => 1 + ∑ i : Fin (n + 1), Q i (n - i)
  have hB (n : ℕ) : 0 < B n := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hQ i (n - i)).le))
  have hQB (a b : ℕ) : Q a b ≤ B (a + b) := by
    have hi : a < a + b + 1 := by omega
    have ht := Finset.single_le_sum
      (f := fun i : Fin (a + b + 1) => Q i (a + b - i))
      (fun i _ => (hQ i (a + b - i)).le)
      (Finset.mem_univ (⟨a, hi⟩ : Fin (a + b + 1)))
    have ht' : Q a b ≤ ∑ i : Fin (a + b + 1), Q i (a + b - i) := by
      simpa only [show a + b - a = b by omega] using ht
    exact ht'.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨low, outLoss, B, hB, ?_⟩
  intro z hz hs hlow a b q hq
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hrep (i : Fin 3) := exists_global_contDiff_germ_of_open hU
    (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs i) hq
  choose F hF he using hrep
  have hinput (i : Fin 3) (c d : ℕ) (_hcd : c + d ≤ a + b) :
      |mixedDerivative c d (F i) q| ≤
        M (c + d) * (1 : ℝ) ^ M (c + d) *
          (1 + pairGrading (stateGrading S) realGrading (c + d + loss)
            (z - (C.referenceState, 0))) := by
    simp only [Real.one_rpow, mul_one]
    rw [mixedDerivative_eq_of_germ (he i) c d]
    exact (hraw (c + d) z hz hs i c d le_rfl q hq).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
  have hlocal := hbound a b (z - (C.referenceState, 0)) hlow 1 le_rfl F hF q hinput
  have hdiscriminant : (fun x => F 1 x ^ 2 - F 0 x * F 2 x) =ᶠ[𝓝 q]
      (fun x => (originalCoefficients D S C z).b x ^ 2 -
        (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x) := by
    filter_upwards [he 0, he 1, he 2] with x h0 h1 h2
    rw [h0, h1, h2]
    norm_num [canonicalCoefficientComponent]
  rw [mixedDerivative_eq_of_germ hdiscriminant a b] at hlocal
  have hlocal' : |mixedDerivative a b
      (fun x => (originalCoefficients D S C z).b x ^ 2 -
        (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x) q| ≤
      Q a b * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
        (z - (C.referenceState, 0))) := by
    simpa only [Real.one_rpow, mul_one] using hlocal
  exact hlocal'.trans (mul_le_mul_of_nonneg_right (hQB a b)
    (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
