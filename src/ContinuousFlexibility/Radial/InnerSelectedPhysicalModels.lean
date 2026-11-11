import ContinuousFlexibility.Radial.InnerSelectedCentralChart
import ContinuousFlexibility.Radial.InnerSelectedPhysicalGaps
import ContinuousFlexibility.Radial.InnerMorseScaledPhysicalChart
import ContinuousFlexibility.Radial.InnerMorseInnerModelArray

/-!
# The same selected models on the actual physical inner chain

One central model and the two arrays of retained Morse models fill the
alternating chain. Every model is the original selected R09 witness,
transported to the final reference by its actual chart. The gaps use the
actual radial IVP construction. No weight parameter enters the model
array or the resulting physical operator dictionary.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

section TailModel

variable {a CM KM η : ℝ}
  (hfamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))
  (side : Bool) (p : Fin K)

/-- This is the original selector, with no new choice of a local model. -/
def tailLocalizedModel : InnerBufferLocalizedData
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      ((2 : ℝ) * q)
      (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index K side p) : ℝ) ^ 9)) CM KM :=
  innerSelectedMorseModel hfamily P.realization rfl
    (innerMorseInnerTailIndex S.chain.index K side p) (S.chain.index + K) q
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).2 hq hband

include P hfamily hq hband in
theorem tailModel_hypotheses : BufferHypotheses
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      ((2 : ℝ) * q)
      (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index K side p) : ℝ) ^ 9)) :=
  innerSelectedMorseModel_hypotheses hfamily P.realization rfl
    (innerMorseInnerTailIndex S.chain.index K side p) (S.chain.index + K) q
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).2 hq hband

theorem tailLocalizedModel_energy_pos (i : Fin 2) :
    0 < ((P.tailLocalizedModel hfamily K q hq hband side p).column i).inwardEnergy :=
  innerSelectedMorseModel_energy_pos hfamily P.realization rfl
    (innerMorseInnerTailIndex S.chain.index K side p) (S.chain.index + K) q
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).2 hq hband i

theorem tailLocalizedModel_remainder (i : Fin 2) :
    innerMorseModelNormalizedRemainder
      (P.tailLocalizedModel hfamily K q hq hband side p) i ≤ 1 / ((2 : ℝ) * q) :=
  innerSelectedMorseModel_remainder hfamily P.realization rfl
    (innerMorseInnerTailIndex S.chain.index K side p) (S.chain.index + K) q
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).2 hq hband i

/-- The actual independently scaled tail chart, using the same model
and the same single central scalar column as the rest of the chain. -/
def tailModel :
    InnerRadialModelChart D (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport)
      (innerModelChainPiece (innerMorseInnerTailSlot K side p)) :=
  innerMorseScaledPhysicalModelChart P.realization P.index_ge D (P.chain K)
    (decide (q = 1)) ((2 : ℝ) * q)
    (innerModelChainPiece (innerMorseInnerCenter K))
    (innerModelChainPiece (innerMorseInnerTailSlot K side p))
    (P.centralColumn q hsupport) side
    (innerMorseInnerTailIndex S.chain.index K side p)
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (P.radiusScale side) (P.heightScale side)
    (P.radiusScale_pos side) (P.heightScale_pos side)
    (fun _ hx => P.tail_profile side
      (innerMorseInnerTailIndex_bounds S.chain.index K side p).1 hx)
    (innerMorseInnerTailPiece_ne_center K side p)
    (P.tail_left K side p) (P.tail_right K side p)
    (P.tailModel_hypotheses hfamily K q hq hband side p)
    (P.tailLocalizedModel hfamily K q hq hband side p)

@[simp] theorem tailModel_localized :
    (P.tailModel hfamily hsupport K q hq hband side p).localized =
      P.tailLocalizedModel hfamily K q hq hband side p := rfl

theorem tailModel_kappa :
    (P.tailModel hfamily hsupport K q hq hband side p).kappa =
      innerPhysicalCutKappa
        (P.heightScale side *
          morseChainAmplitude S.chain S.sigma (innerMorseInnerTailIndex S.chain.index K side p))
        (fun _ => 1)
        (fun i => ((P.tailLocalizedModel hfamily K q hq hband side p).column i).inwardEnergy) := by
  funext i
  exact innerMorseScaledPhysicalModelChart_kappa P.realization P.index_ge D (P.chain K)
    (decide (q = 1)) ((2 : ℝ) * q)
    (innerModelChainPiece (innerMorseInnerCenter K))
    (innerModelChainPiece (innerMorseInnerTailSlot K side p))
    (P.centralColumn q hsupport) side
    (innerMorseInnerTailIndex S.chain.index K side p)
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (P.radiusScale side) (P.heightScale side)
    (P.radiusScale_pos side) (P.heightScale_pos side)
    (fun _ hx => P.tail_profile side
      (innerMorseInnerTailIndex_bounds S.chain.index K side p).1 hx)
    (innerMorseInnerTailPiece_ne_center K side p)
    (P.tail_left K side p) (P.tail_right K side p)
    (P.tailModel_hypotheses hfamily K q hq hband side p)
    (P.tailLocalizedModel hfamily K q hq hband side p) i

theorem tailModel_kappa_pos (i : Fin 2) :
    0 < (P.tailModel hfamily hsupport K q hq hband side p).kappa i := by
  rw [P.tailModel_kappa hfamily hsupport K q hq hband side p]
  simp only [innerPhysicalCutKappa, one_pow, mul_one]
  exact mul_pos
    (mul_pos (P.heightScale_pos side)
      (innerMorseChain_height_pos P.realization side
        (innerMorseInnerTailIndex_bounds S.chain.index K side p).1))
    (P.tailLocalizedModel_energy_pos hfamily K q hq hband side p i)

theorem tailModel_errorMatrix :
    (P.tailModel hfamily hsupport K q hq hband side p).errorMatrix =
      (P.tailLocalizedModel hfamily K q hq hband side p).physicalFluxError
        (P.heightScale side *
          morseChainAmplitude S.chain S.sigma (innerMorseInnerTailIndex S.chain.index K side p))
        (fun _ => 1) := rfl

/-- The physical column is formed from the same selected localized
model. Its measure and all chart proofs are those of the stored piece. -/
theorem tailModel_column (i : Fin 2) :
    let A := P.tailModel hfamily hsupport K q hq hband side p
    A.column i = innerModelPhysicalPoissonColumn D
      (P.tailModel_hypotheses hfamily K q hq hband side p)
      (P.tailLocalizedModel hfamily K q hq hband side p)
      A.height_pos A.radius_smooth A.scale_smooth A.chart_pos A.in_core
      A.weight_identity A.U A.U_nonneg A.log_deriv_bound i := rfl

end TailModel

private theorem twice_nat_pos {q : ℕ} (hq : 1 ≤ q) : 0 < (2 : ℝ) * q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  positivity

section ModelArray

variable {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))

/-- One dependent array with the original central and both tail values. -/
def models (p : Fin (2 * K + 1)) :
    InnerRadialModelChart D (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport)
      (innerModelChainPiece p) :=
  innerMorseInnerModelElim
    (β := fun p => InnerRadialModelChart D (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport)
      (innerModelChainPiece p))
    (P.centralModel hCentralFamily hX hsupport (P.chain K)
      (innerModelChainPiece (innerMorseInnerCenter K)) q hq
      (P.center_left_cut K) (P.center_right_cut K))
    (P.tailModel hMorseFamily hsupport K q hq hband) p

theorem models_center :
    P.models hCentralFamily hMorseFamily hX hsupport K q hq hband (innerMorseInnerCenter K) =
      P.centralModel hCentralFamily hX hsupport (P.chain K)
        (innerModelChainPiece (innerMorseInnerCenter K)) q hq
        (P.center_left_cut K) (P.center_right_cut K) :=
  innerMorseInnerModelElim_center _ _

theorem models_tail (side : Bool) (p : Fin K) :
    P.models hCentralFamily hMorseFamily hX hsupport K q hq hband
        (innerMorseInnerTailSlot K side p) =
      P.tailModel hMorseFamily hsupport K q hq hband side p :=
  innerMorseInnerModelElim_tail _ _ side p

theorem models_kappa_pos (p : Fin (2 * K + 1)) (i : Fin 2) :
    0 < (P.models hCentralFamily hMorseFamily hX hsupport K q hq hband p).kappa i := by
  rcases innerMorseInnerModel_cases K p with rfl | ⟨side, p, rfl⟩
  · rw [P.models_center]
    exact P.centralModel_kappa_pos hCentralFamily hX hsupport (P.chain K)
      (innerModelChainPiece (innerMorseInnerCenter K)) q hq
      (P.center_left_cut K) (P.center_right_cut K) i
  · rw [P.models_tail]
    exact P.tailModel_kappa_pos hMorseFamily hsupport K q hq hband side p i

/-- The actual operator dictionary on every finite band, including K=0.
No weight exponent or sign occurs in this definition. -/
def actualChain :
    InnerRadialActualChain D (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) :=
  innerActualChainOfModelsAndGaps (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
    (innerMorseInnerCenter K) (P.centralColumn q hsupport)
    (P.models hCentralFamily hMorseFamily hX hsupport K q hq hband)
    (P.gapChart K ((2 : ℝ) * q) (twice_nat_pos hq))

theorem actualChain_model (p : Fin (2 * K + 1)) :
    (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).piece
        (innerModelChainPiece p) =
      Sum.inl (P.models hCentralFamily hMorseFamily hX hsupport K q hq hband p) :=
  innerActualChainOfModelsAndGaps_model _ _ _ _ _ _ _ p

theorem actualChain_gap (g : Fin (2 * K + 2)) :
    (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).piece
        (innerModelChainGap g) =
      Sum.inr (P.gapChart K ((2 : ℝ) * q) (twice_nat_pos hq) g) :=
  innerActualChainOfModelsAndGaps_gap _ _ _ _ _ _ _ g

theorem actualChain_kappa_pos (i : Fin (2 * (2 * K + 1))) :
    0 < (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).kappa i :=
  innerActualChainOfModelsAndGaps_kappa_pos _ _ _ _ _ _ _
    (P.models_kappa_pos hCentralFamily hMorseFamily hX hsupport K q hq hband) i

theorem actualChain_kappa_separated (i : Fin (2 * (2 * K + 1))) :
    ((P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).piece
        i.castSucc).kappa 1 = 0 ∨
      ((P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).piece
        i.succ).kappa 0 = 0 :=
  innerActualChainOfModelsAndGaps_kappa_separated _ _ _ _ _ _ _ i

theorem actualChain_model_internal (p : Fin (2 * (2 * K + 1) + 1))
    (A : InnerRadialModelChart D (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) p)
    (hp : (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).piece p =
      Sum.inl A) : 0 < p.val ∧ p.val < 2 * (2 * K + 1) ∧ ∀ i, 0 < A.kappa i :=
  innerActualChainOfModelsAndGaps_model_internal _ _ _ _ _ _ _
    (P.models_kappa_pos hCentralFamily hMorseFamily hX hsupport K q hq hband) p A hp

end ModelArray

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
