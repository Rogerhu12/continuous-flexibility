import ContinuousFlexibility.Radial.InnerActualModelChain
import ContinuousFlexibility.Radial.InnerMorseAllBandsGeometry

/-!
# Selecting the actual central model and the two physical tail arrays

A single dependent selector fills the model slots of every finite inner
domain. Its central and tail values are exact, including the first band
with no tail slots. Properties therefore pass from the same local models
to the assembled array without choosing new witnesses.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

private theorem innerMorseInnerCenterMap_injective (K : ℕ) :
    Function.Injective (fun _ : PUnit => innerMorseInnerCenter K) :=
  fun a b _ => Subsingleton.elim a b

private theorem innerMorseInnerCenterTail_cover (K : ℕ) (p : Fin (2 * K + 1)) :
    (∃ _ : PUnit, p = innerMorseInnerCenter K) ∨
      ∃ sp : Bool × Fin K, p = innerMorseInnerTailSlot K sp.1 sp.2 := by
  rcases innerMorseInnerModel_cases K p with h | ⟨side, q, h⟩
  · exact Or.inl ⟨PUnit.unit, h⟩
  · exact Or.inr ⟨(side, q), h⟩

section DependentModels

variable {K : ℕ} {β : Fin (2 * K + 1) → Type*}
  (center : β (innerMorseInnerCenter K))
  (tails : ∀ side : Bool, ∀ p : Fin K, β (innerMorseInnerTailSlot K side p))

def innerMorseInnerModelElim (p : Fin (2 * K + 1)) : β p :=
  innerDisjointCoverElim
    (fun _ : PUnit => innerMorseInnerCenter K)
    (fun sp : Bool × Fin K => innerMorseInnerTailSlot K sp.1 sp.2)
    (innerMorseInnerCenterMap_injective K) (innerMorseInnerTailSlot_injective K)
    (fun _ sp => (innerMorseInnerTailSlot_ne_center K sp.1 sp.2).symm)
    (innerMorseInnerCenterTail_cover K)
    (fun _ => center) (fun sp => tails sp.1 sp.2) p

theorem innerMorseInnerModelElim_center :
    innerMorseInnerModelElim center tails (innerMorseInnerCenter K) = center :=
  innerDisjointCoverElim_left (β := β)
    (fun _ : PUnit => innerMorseInnerCenter K)
    (fun sp : Bool × Fin K => innerMorseInnerTailSlot K sp.1 sp.2)
    (innerMorseInnerCenterMap_injective K) (innerMorseInnerTailSlot_injective K)
    (fun _ sp => (innerMorseInnerTailSlot_ne_center K sp.1 sp.2).symm)
    (innerMorseInnerCenterTail_cover K)
    (fun _ => center) (fun sp => tails sp.1 sp.2) PUnit.unit

theorem innerMorseInnerModelElim_tail (side : Bool) (p : Fin K) :
    innerMorseInnerModelElim center tails (innerMorseInnerTailSlot K side p) = tails side p :=
  innerDisjointCoverElim_right (β := β)
    (fun _ : PUnit => innerMorseInnerCenter K)
    (fun sp : Bool × Fin K => innerMorseInnerTailSlot K sp.1 sp.2)
    (innerMorseInnerCenterMap_injective K) (innerMorseInnerTailSlot_injective K)
    (fun _ sp => (innerMorseInnerTailSlot_ne_center K sp.1 sp.2).symm)
    (innerMorseInnerCenterTail_cover K)
    (fun _ => center) (fun sp => tails sp.1 sp.2) (side, p)

/-- A property of the chosen central and tail objects is a property
of the same complete model array. -/
theorem innerMorseInnerModelElim_all (P : ∀ p, β p → Prop)
    (hcenter : P (innerMorseInnerCenter K) center)
    (htails : ∀ side p, P (innerMorseInnerTailSlot K side p) (tails side p))
    (p : Fin (2 * K + 1)) : P p (innerMorseInnerModelElim center tails p) := by
  rcases innerMorseInnerModel_cases K p with rfl | ⟨side, q, rfl⟩
  · rw [innerMorseInnerModelElim_center]
    exact hcenter
  · rw [innerMorseInnerModelElim_tail]
    exact htails side q

end DependentModels

end ContinuousFlexibility.Radial
