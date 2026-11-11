import ContinuousFlexibility.Radial.RetainedMorseModelFamily
import ContinuousFlexibility.Radial.RetainedMorseGapCharts
import ContinuousFlexibility.Radial.InnerRadialGapHardy

/-!
# One actual central, Morse, and gap dictionary

All local entries refer to the same physical finite chain. The model
selector keeps the original localized witnesses and the gap selector
keeps their constructed physical Poisson columns. Incidence and positive
cut diagonals follow from this alternating dictionary.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length T : ℝ}
  (P : SeedRetainedPair S K q length) {Γ : ConnectedReferenceGeometry}
  (hD : RadialProfileGeometry Γ.reference) (hw : Γ.reference.w = P.pair.profile)
  (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (hq : 0 < q) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (k : ℕ) (hk : 0 < k)
  (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
    (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
  (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
  (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
    (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
  (bordered : Bool) (j : ℝ) (hj : 0 < j) (column : RadialModeL2 Γ.reference)

local notation "H" => P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk
local notation "center" => innerModelChainPiece (innerMorseInnerCenter k)

variable {CM KM : ℝ}
  (hB : ∀ side p, BufferHypotheses
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)))
  (models : ∀ side p, InnerBufferLocalizedData
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) CM KM)
  (centralModel : InnerRadialModelChart Γ.reference H bordered j center column center)

local notation "tails" => P.retainedMorseInnerGeometry_tail hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk
local notation "MF" => P.retainedMorseModelFamily hw hS G₀ hfirst H bordered j column
  tails hB models centralModel
local notation "QF" => P.retainedMorseGapChart hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk hbridge hmodel hwindow j hj

def retainedMorseActualChain :
    InnerRadialActualChain Γ.reference H bordered j center column :=
  innerActualChainOfModelsAndGaps H bordered j (innerMorseInnerCenter k) column MF QF

local notation "A" => P.retainedMorseActualChain hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hj column hB models centralModel

theorem retainedMorseActualChain_model (p : Fin (2 * k + 1)) :
    (A).piece (innerModelChainPiece p) = .inl (MF p) :=
  innerActualChainOfModelsAndGaps_model H bordered j (innerMorseInnerCenter k) column MF QF p

theorem retainedMorseActualChain_center :
    (A).piece center = .inl centralModel := by
  rw [retainedMorseActualChain_model, retainedMorseModelFamily_center]

theorem retainedMorseActualChain_tail (side : Bool) (p : Fin k) :
    (A).piece (innerModelChainPiece (innerMorseInnerTailSlot k side p)) =
      .inl (P.retainedMorseTailModelChart hw hS G₀ hfirst H bordered j column
        tails hB models side p) := by
  rw [retainedMorseActualChain_model, retainedMorseModelFamily_tail]

theorem retainedMorseActualChain_gap (g : Fin (2 * k + 2)) :
    (A).piece (innerModelChainGap g) = .inr (QF g) :=
  innerActualChainOfModelsAndGaps_gap H bordered j (innerMorseInnerCenter k) column MF QF g

theorem retainedMorseActualChain_kappa_pos (hCM : 0 < CM)
    (hcentral : ∀ i, 0 < centralModel.kappa i) (i : Fin (2 * (2 * k + 1))) :
    0 < (A).kappa i :=
  innerActualChainOfModelsAndGaps_kappa_pos H bordered j (innerMorseInnerCenter k) column MF QF
    (P.retainedMorseModelFamily_kappa_pos hw hS G₀ hfirst H bordered j column
      tails hB models centralModel hCM hcentral) i

theorem retainedMorseActualChain_kappa_separated (i : Fin (2 * (2 * k + 1))) :
    ((A).piece i.castSucc).kappa 1 = 0 ∨ ((A).piece i.succ).kappa 0 = 0 :=
  innerActualChainOfModelsAndGaps_kappa_separated H bordered j
    (innerMorseInnerCenter k) column MF QF i

theorem retainedMorseActualChain_model_internal (hCM : 0 < CM)
    (hcentral : ∀ i, 0 < centralModel.kappa i) (p : Fin (2 * (2 * k + 1) + 1))
    (M : InnerRadialModelChart Γ.reference H bordered j center column p)
    (hp : (A).piece p = .inl M) :
    0 < p.val ∧ p.val < 2 * (2 * k + 1) ∧ ∀ i, 0 < M.kappa i :=
  innerActualChainOfModelsAndGaps_model_internal H bordered j
    (innerMorseInnerCenter k) column MF QF
    (P.retainedMorseModelFamily_kappa_pos hw hS G₀ hfirst H bordered j column
      tails hB models centralModel hCM hcentral) p M hp

/-- A property of the actual model pieces reduces to the same central
witness and the same localized Morse witnesses. -/
theorem retainedMorseActualChain_model_induction
    (property : ∀ p, InnerRadialModelChart Γ.reference H bordered j center column p → Prop)
    (hcentral : property center centralModel)
    (htail : ∀ side p, property (innerModelChainPiece (innerMorseInnerTailSlot k side p))
      (P.retainedMorseTailModelChart hw hS G₀ hfirst H bordered j column tails hB models side p)) :
    ∀ p (M : InnerRadialModelChart Γ.reference H bordered j center column p),
      (A).piece p = .inl M → property p M := by
  intro p M hp
  rcases innerModelChainPiece_or_gap p with ⟨p, rfl⟩ | ⟨g, rfl⟩
  · rcases innerMorseInnerModelSlot_cases p with rfl | ⟨side, p, rfl⟩
    · rw [retainedMorseActualChain_center] at hp
      have he : centralModel = M := Sum.inl.inj hp
      simpa only [← he] using hcentral
    · rw [retainedMorseActualChain_tail] at hp
      have he := Sum.inl.inj hp
      simpa only [← he] using htail side p
  · rw [retainedMorseActualChain_gap] at hp
    cases hp

end SeedRetainedPair

end ContinuousFlexibility.Radial
