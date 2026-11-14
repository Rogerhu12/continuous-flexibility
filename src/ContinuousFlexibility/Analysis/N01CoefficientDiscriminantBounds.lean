module

public import ContinuousFlexibility.Analysis.N01LocalizedCoefficientBounds
public import ContinuousFlexibility.Analysis.CoefficientDiscriminantMaterialBounds

/-!
# A common fixed loss for the actual N01 coefficient discriminant

The low order and the loss are chosen before the physical cell, interval,
or derivative order. Reference compactness constants and N01's material
sample factors enter only the numerical constant chosen before the state.
The actual discriminant is recovered from the fixed clamp by locality.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The envelope-one specialization is kept abstract in the state space. -/
private def CoefficientDiscriminantOneBoundAtOrder
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (low outLoss inputLoss : ℕ)
    (A : ℕ → ℝ) (a b : ℕ) (B : ℝ) : Prop :=
  ∀ z : E, p low z ≤ 1 →
    ∀ K : Fin 3 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (K i)) →
    ∀ q : PolarPoint,
    (∀ c : Fin 3, ∀ i j : ℕ, i + j ≤ a + b →
      |mixedDerivative i j (K c) q| ≤
        A (i + j) * (1 + p (i + j + inputLoss) z)) →
    |mixedDerivative a b (fun x => K 1 x ^ 2 - K 0 x * K 2 x) q| ≤
      B * (1 + p (a + b + outLoss) z)

private theorem coefficientDiscriminant_fixed_loss_bound_one
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ a b : ℕ, ∃ B : ℝ, 0 < B ∧
        CoefficientDiscriminantOneBoundAtOrder p low outLoss inputLoss A a b B := by
  obtain ⟨low, outLoss, hmaterial⟩ :=
    coefficientDiscriminant_fixed_loss_material_bound hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A hA a b
  obtain ⟨B, hB, hbound⟩ := hmaterial A hA a b
  refine ⟨B, hB, ?_⟩
  intro z hz K hK q hj
  have hinput (c : Fin 3) (i j : ℕ) (hij : i + j ≤ a + b) :
      |mixedDerivative i j (K c) q| ≤
        A (i + j) * (1 : ℝ) ^ A (i + j) * (1 + p (i + j + inputLoss) z) := by
    simpa only [Real.one_rpow, mul_one] using hj c i j hij
  simpa only [Real.one_rpow, mul_one] using
    hbound z hz 1 le_rfl K hK q hinput

/-- Exactly the former expanded state- and point-wise conclusion. -/
def N01CoefficientDiscriminantBoundAtOrder
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε l u : ℝ) (a b : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
      |mixedDerivative a b
        (fun x => (originalCoefficients D S C z).b x ^ 2 -
          (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x) q| ≤
        B * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
          (z - (C.referenceState, 0)))

private theorem localizedOriginalCoefficient_discriminant_jet
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (z : AnnularState S × ℝ) (a b : ℕ) {q : PolarPoint}
    (hq : q ∈ Ioo l u ×ˢ (univ : Set ℝ)) :
    mixedDerivative a b
      (fun x => localizedOriginalCoefficient D S C hlu hρ z 1 x ^ 2 -
        localizedOriginalCoefficient D S C hlu hρ z 0 x *
          localizedOriginalCoefficient D S C hlu hρ z 2 x) q =
    mixedDerivative a b
      (fun x => (originalCoefficients D S C z).b x ^ 2 -
        (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x) q := by
  apply mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) _ a b hq
  intro x hx
  change localizedOriginalCoefficient D S C hlu hρ z 1 x ^ 2 -
    localizedOriginalCoefficient D S C hlu hρ z 0 x *
      localizedOriginalCoefficient D S C hlu hρ z 2 x = _
  rw [localizedOriginalCoefficient_eqOn D S C hlu hρ z 1 hx,
    localizedOriginalCoefficient_eqOn D S C hlu hρ z 0 hx,
    localizedOriginalCoefficient_eqOn D S C hlu hρ z 2 hx]
  norm_num [canonicalCoefficientComponent]

private theorem n01_coefficientDiscriminant_bound_of_material
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (hphysical : Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b)
    (A : ℕ → ℝ)
    (hA : ∀ n, LocalizedOriginalCoefficientBoundAtOrder
      D S C base loss ε hlu hρ n (A n))
    (a b : ℕ) (B : ℝ)
    (hbound : CoefficientDiscriminantOneBoundAtOrder
      (pairGrading (stateGrading S) realGrading) low outLoss loss A a b B) :
    N01CoefficientDiscriminantBoundAtOrder D S C base low outLoss ε l u a b B := by
  intro z hz hsector hlow q hq
  have hK (i : Fin 3) :
      ContDiff ℝ ∞ (localizedOriginalCoefficient D S C hlu hρ z i) :=
    contDiff_localizedOriginalCoefficient hS hT hN hlu hρ hphysical hz hsector i
  have hlocalized := hbound (z - (C.referenceState, 0)) hlow
    (localizedOriginalCoefficient D S C hlu hρ z) hK q
    (fun c i j _ => hA (i + j) z hz hsector c i j le_rfl q hq)
  exact (congrArg abs
    (localizedOriginalCoefficient_discriminant_jet D S C hlu hρ z a b hq)).symm.trans_le
      hlocalized

theorem n01_coefficientDiscriminant_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ l u ρ : ℝ, ∀ hlu : l ≤ u, ∀ hρ : 0 < ρ,
      Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo l u ⊆ D.cells m →
      ∀ a b : ℕ, ∃ B : ℝ, 0 < B ∧
        N01CoefficientDiscriminantBoundAtOrder D S C base low outLoss ε l u a b B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hmaterial⟩ :=
    coefficientDiscriminant_fixed_loss_bound_one hp hI loss
  refine ⟨low, outLoss, ?_⟩
  intro l u ρ hlu hρ hphysical m hcell
  choose A hA hAbound using
    (fun n => localizedOriginalCoefficient_fixed_loss_bound_of_n01
      hS hT hN hlu hρ hphysical m hcell n)
  intro a b
  obtain ⟨B, hB, hbound⟩ := hmaterial A hA a b
  exact ⟨B, hB, n01_coefficientDiscriminant_bound_of_material
    hS hT hN hlu hρ hphysical A hAbound a b B hbound⟩

end ContinuousFlexibility.Analysis
