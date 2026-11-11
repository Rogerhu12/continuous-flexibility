import ContinuousFlexibility.Radial.RetainedMorseModelChart
import ContinuousFlexibility.Radial.InnerActualModelChain
import ContinuousFlexibility.Radial.InnerMorseInnerChain

/-!
# One actual central-and-tail model dictionary

The finite model slots contain the given fixed central chart and the
physical transports of the original localized Morse buffers. The two
side factors belong to the same retained pair. The selector has exact
application lemmas, so the local estimates refer to the original models.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

theorem innerMorseInnerTailSlot_pair_injective (k : ℕ) :
    Function.Injective (fun sp : Bool × Fin k => innerMorseInnerTailSlot k sp.1 sp.2) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ he
  have hv := congrArg Fin.val he
  have hp := p.isLt
  have hq := q.isLt
  cases s <;> cases t
  · exact Prod.ext rfl (Fin.ext (by
      simpa only [innerMorseInnerTailSlot, Bool.false_eq_true, ite_false] using hv))
  · simp only [innerMorseInnerTailSlot, Bool.false_eq_true, ite_false, ite_true] at hv
    omega
  · simp only [innerMorseInnerTailSlot, Bool.false_eq_true, ite_false, ite_true] at hv
    omega
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [innerMorseInnerTailSlot, ite_true] at hv
      omega

theorem innerMorseInnerModelSlot_cases {k : ℕ} (p : Fin (2 * k + 1)) :
    p = innerMorseInnerCenter k ∨ ∃ side q, p = innerMorseInnerTailSlot k side q := by
  by_cases hp : p.val < k
  · exact Or.inr ⟨false, ⟨p.val, hp⟩, Fin.ext rfl⟩
  by_cases hp0 : p.val = k
  · exact Or.inl (Fin.ext hp0)
  · refine Or.inr ⟨true, ⟨p.val - k - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [innerMorseInnerTailSlot, ite_true]
    omega

def innerMorseModelElim {k : ℕ} {β : Fin (2 * k + 1) → Type*}
    (central : β (innerMorseInnerCenter k))
    (tail : ∀ side p, β (innerMorseInnerTailSlot k side p))
    (p : Fin (2 * k + 1)) : β p :=
  innerDisjointCoverElim (fun _ : Unit => innerMorseInnerCenter k)
    (fun sp : Bool × Fin k => innerMorseInnerTailSlot k sp.1 sp.2)
    (fun _ _ _ => Subsingleton.elim _ _) (innerMorseInnerTailSlot_pair_injective k)
    (fun _ sp => (innerMorseInnerTailSlot_ne_center k sp.1 sp.2).symm)
    (fun p => by
      rcases innerMorseInnerModelSlot_cases p with hp | ⟨side, q, hp⟩
      · exact Or.inl ⟨(), hp⟩
      · exact Or.inr ⟨(side, q), hp⟩)
    (fun _ => central) (fun sp => tail sp.1 sp.2) p

theorem innerMorseModelElim_center {k : ℕ} {β : Fin (2 * k + 1) → Type*}
    (central : β (innerMorseInnerCenter k))
    (tail : ∀ side p, β (innerMorseInnerTailSlot k side p)) :
    innerMorseModelElim central tail (innerMorseInnerCenter k) = central :=
  innerDisjointCoverElim_left (fun _ : Unit => innerMorseInnerCenter k)
    (fun sp : Bool × Fin k => innerMorseInnerTailSlot k sp.1 sp.2)
    (fun a b _ => Subsingleton.elim a b) (innerMorseInnerTailSlot_pair_injective k)
    (fun _ sp => (innerMorseInnerTailSlot_ne_center k sp.1 sp.2).symm)
    (fun p => by
      rcases innerMorseInnerModelSlot_cases p with hp | ⟨side, q, hp⟩
      · exact Or.inl ⟨(), hp⟩
      · exact Or.inr ⟨(side, q), hp⟩)
    (fun _ => central) (fun sp => tail sp.1 sp.2) ()

theorem innerMorseModelElim_tail {k : ℕ} {β : Fin (2 * k + 1) → Type*}
    (central : β (innerMorseInnerCenter k))
    (tail : ∀ side p, β (innerMorseInnerTailSlot k side p)) (side : Bool) (p : Fin k) :
    innerMorseModelElim central tail (innerMorseInnerTailSlot k side p) = tail side p :=
  innerDisjointCoverElim_right (fun _ : Unit => innerMorseInnerCenter k)
    (fun sp : Bool × Fin k => innerMorseInnerTailSlot k sp.1 sp.2)
    (fun a b _ => Subsingleton.elim a b) (innerMorseInnerTailSlot_pair_injective k)
    (fun _ sp => (innerMorseInnerTailSlot_ne_center k sp.1 sp.2).symm)
    (fun p => by
      rcases innerMorseInnerModelSlot_cases p with hp | ⟨side, q, hp⟩
      · exact Or.inl ⟨(), hp⟩
      · exact Or.inr ⟨(side, q), hp⟩)
    (fun _ => central) (fun sp => tail sp.1 sp.2) (side, p)

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G₀ : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  {k : ℕ} (H : InnerRadialChainGeometry D (2 * (2 * k + 1)))
  (bordered : Bool) (j : ℝ) (column : RadialModeL2 D)
  (htail : ∀ side p,
    H.left (innerModelChainPiece (innerMorseInnerTailSlot k side p)) =
      P.sideRadius side * innerMorseChainCut S.chain side
        (innerMorseInnerTailIndex S.chain.index k side p) 0 ∧
    H.right (innerModelChainPiece (innerMorseInnerTailSlot k side p)) =
      P.sideRadius side * innerMorseChainCut S.chain side
        (innerMorseInnerTailIndex S.chain.index k side p) 1)
  {Cmodel Kmodel : ℝ}
  (hB : ∀ side p, BufferHypotheses
    (innerMorseBufferData (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p)) j
      (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)))
  (M : ∀ side p, InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p)) j
      (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) Cmodel Kmodel)

local notation "center" => innerModelChainPiece (innerMorseInnerCenter k)
def retainedMorseTailModelChart (side : Bool) (p : Fin k) :
    InnerRadialModelChart D H bordered j center column
      (innerModelChainPiece (innerMorseInnerTailSlot k side p)) :=
  P.retainedMorseModelChart hw hS G₀ hband H bordered j center
    (innerModelChainPiece (innerMorseInnerTailSlot k side p)) column
    side (innerMorseInnerTailIndex S.chain.index k side p)
    (innerMorseInnerTailIndex_bounds S.chain.index k side p).1
    (innerMorseInnerTailPiece_ne_center k side p) (htail side p).1 (htail side p).2
    (hB side p) (M side p)

variable (centralModel : InnerRadialModelChart D H bordered j center column center)

def retainedMorseModelFamily (p : Fin (2 * k + 1)) :
    InnerRadialModelChart D H bordered j center column (innerModelChainPiece p) :=
  innerMorseModelElim
    (β := fun p => InnerRadialModelChart D H bordered j center column (innerModelChainPiece p))
    centralModel
    (P.retainedMorseTailModelChart hw hS G₀ hband H bordered j column htail hB M) p

theorem retainedMorseModelFamily_center :
    P.retainedMorseModelFamily hw hS G₀ hband H bordered j column htail hB M centralModel
      (innerMorseInnerCenter k) = centralModel :=
  innerMorseModelElim_center
    (β := fun p => InnerRadialModelChart D H bordered j center column (innerModelChainPiece p))
    centralModel
    (P.retainedMorseTailModelChart hw hS G₀ hband H bordered j column htail hB M)

theorem retainedMorseModelFamily_tail (side : Bool) (p : Fin k) :
    P.retainedMorseModelFamily hw hS G₀ hband H bordered j column htail hB M centralModel
      (innerMorseInnerTailSlot k side p) =
      P.retainedMorseTailModelChart hw hS G₀ hband H bordered j column htail hB M side p :=
  innerMorseModelElim_tail
    (β := fun p => InnerRadialModelChart D H bordered j center column (innerModelChainPiece p))
    centralModel
    (P.retainedMorseTailModelChart hw hS G₀ hband H bordered j column htail hB M) side p

theorem retainedMorseTailModelChart_kappa_pos (hC : 0 < Cmodel) (side : Bool)
    (p : Fin k) (i : Fin 2) :
    0 < (P.retainedMorseTailModelChart hw hS G₀ hband H bordered j column htail hB M side p).kappa i := by
  rw [retainedMorseTailModelChart, retainedMorseModelChart_kappa]
  exact mul_pos
    (mul_pos (P.sideHeight_pos side)
      (innerMorseChain_height_pos (hS.2.2.2.1 S.sigma hS.2.2.1).1 side
        (innerMorseInnerTailIndex_bounds S.chain.index k side p).1))
    ((div_pos (buffer_mass_pos (hB side p) i) hC).trans_le
      ((M side p).column i).inward_lower)

theorem retainedMorseModelFamily_kappa_pos (hC : 0 < Cmodel)
    (hcentral : ∀ i, 0 < centralModel.kappa i) (p : Fin (2 * k + 1)) (i : Fin 2) :
    0 < (P.retainedMorseModelFamily hw hS G₀ hband H bordered j column htail hB M
      centralModel p).kappa i := by
  rcases innerMorseInnerModelSlot_cases p with rfl | ⟨side, p, rfl⟩
  · rw [retainedMorseModelFamily_center]
    exact hcentral i
  · rw [retainedMorseModelFamily_tail]
    exact P.retainedMorseTailModelChart_kappa_pos hw hS G₀ hband H bordered j column htail hB M
      hC side p i

end SeedRetainedPair

end ContinuousFlexibility.Radial
