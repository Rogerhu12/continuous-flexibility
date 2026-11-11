import ContinuousFlexibility.Analysis.N01LocalizedCoefficientBounds
import ContinuousFlexibility.Analysis.CoefficientDiscriminantMaterialBounds

/-!
# A common fixed loss for the actual N01 coefficient discriminant

The low order and the loss are chosen before the physical cell, interval,
or derivative order. Reference compactness constants and N01's material
sample factors enter only the numerical constant chosen before the state.
The actual discriminant is recovered from the fixed clamp by locality.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n01_coefficientDiscriminant_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ l u ρ : ℝ, ∀ hlu : l ≤ u, ∀ hρ : 0 < ρ,
      Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo l u ⊆ D.cells m →
      ∀ a b : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (fun x => (originalCoefficients D S C z).b x ^ 2 -
            (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x) q| ≤
          B * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
            (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hmaterial⟩ :=
    coefficientDiscriminant_fixed_loss_material_bound hp hI loss
  refine ⟨low, outLoss, ?_⟩
  intro l u ρ hlu hρ hphysical m hcell
  choose A hA hAbound using
    (fun n => localizedOriginalCoefficient_fixed_loss_bound_of_n01
      hS hT hN hlu hρ hphysical m hcell n)
  intro a b
  obtain ⟨B, hB, hbound⟩ := hmaterial A hA a b
  refine ⟨B, hB, ?_⟩
  intro z hz hsector hlow q hq
  let K := localizedOriginalCoefficient D S C hlu hρ z
  have hK (i : Fin 3) : ContDiff ℝ ∞ (K i) :=
    contDiff_localizedOriginalCoefficient hS hT hN hlu hρ hphysical hz hsector i
  have hj (c : Fin 3) (i j : ℕ) (_ : i + j ≤ a + b) :
      |mixedDerivative i j (K c) q| ≤
        A (i + j) * (1 : ℝ) ^ (A (i + j)) *
          (1 + pairGrading (stateGrading S) realGrading (i + j + loss)
            (z - (C.referenceState, 0))) := by
    simpa only [Real.one_rpow, mul_one] using
      hAbound (i + j) z hz hsector c i j le_rfl q hq
  have hlocalized := hbound (z - (C.referenceState, 0)) hlow 1 le_rfl K hK q hj
  have he : EqOn (fun x => K 1 x ^ 2 - K 0 x * K 2 x)
      (fun x => (originalCoefficients D S C z).b x ^ 2 -
        (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x)
      (Ioo l u ×ˢ (univ : Set ℝ)) := by
    intro x hx
    change (localizedOriginalCoefficient D S C hlu hρ z 1 x) ^ 2 -
      localizedOriginalCoefficient D S C hlu hρ z 0 x *
        localizedOriginalCoefficient D S C hlu hρ z 2 x = _
    rw [localizedOriginalCoefficient_eqOn D S C hlu hρ z 1 hx,
      localizedOriginalCoefficient_eqOn D S C hlu hρ z 0 hx,
      localizedOriginalCoefficient_eqOn D S C hlu hρ z 2 hx]
    norm_num [canonicalCoefficientComponent]
  have hjet := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) he a b hq
  exact (congrArg abs hjet).symm.trans_le
    (by simpa only [Real.one_rpow, mul_one] using hlocalized)

end ContinuousFlexibility.Analysis
