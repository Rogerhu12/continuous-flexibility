import ContinuousFlexibility.Radial.InnerRadialPoissonSigns
import ContinuousFlexibility.Radial.InnerActualModelChain
import ContinuousFlexibility.Radial.InnerMorseInnerWeights

/-!
# Actual cut and piece weights for the inner Poisson estimate

The spatial multiplier uses the physical walls stored in the same
actual model dictionary. Its values on the internal cuts agree with
the existing interface weight. On a model it is the original physical
interpolation, and on a gap it is the common cut value.

Only active gap endpoints are constrained. The exterior zero traces
keep their arbitrary default entry one. Both reciprocal signs use
the same functions and the same piece geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerSignedWeight_eq_rpow {α : Type*} (W : α → ℝ)
    (sign : Bool) (x : α) :
    innerSignedWeight W sign x = (W x) ^ (if sign then (1 : ℝ) else -1) := by
  cases sign with
  | false =>
    simp only [innerSignedWeight, Bool.false_eq_true, ite_false, Real.rpow_neg_one]
  | true =>
    simp only [innerSignedWeight, ite_true, Real.rpow_one]

/-- The signed local cut weight is the signed weight of the same
retained model, with its original two endpoint conventions. -/
theorem innerMorseInnerInterfaceWeight_signed_model (N K : ℕ) (a γ : ℝ)
    (p : Fin (2 * K + 1)) (sign : Bool) (i : Fin 2) :
    innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainPiece p)
      (innerSignedWeight (innerMorseInnerInterfaceWeight N K a γ) sign) 1 i =
        innerSignedWeight (innerMorseInnerModelWeight N K a γ p) sign i := by
  rw [innerChainScalarRestriction_signedWeight, innerMorseInnerInterfaceWeight_model]
  simp only [innerSignedWeight]

theorem innerMorseInnerInterfaceWeight_signed_center (N K : ℕ) (a γ : ℝ)
    (sign : Bool) (i : Fin 2) :
    innerChainScalarRestriction (2 * (2 * K + 1))
      (innerModelChainPiece (innerMorseInnerCenter K))
      (innerSignedWeight (innerMorseInnerInterfaceWeight N K a γ) sign) 1 i = 1 := by
  rw [innerMorseInnerInterfaceWeight_signed_model]
  simp only [innerSignedWeight, innerMorseInnerModelWeight_center, inv_one, ite_self]

theorem innerMorseInnerInterfaceWeight_signed_tail (N K : ℕ) (a γ : ℝ)
    (side : Bool) (p : Fin K) (sign : Bool) (i : Fin 2) :
    innerChainScalarRestriction (2 * (2 * K + 1))
      (innerModelChainPiece (innerMorseInnerTailSlot K side p))
      (innerSignedWeight (innerMorseInnerInterfaceWeight N K a γ) sign) 1 i =
        innerSignedWeight
          (innerMorseCutWeight N a γ side (innerMorseInnerTailIndex N K side p)) sign i := by
  rw [innerMorseInnerInterfaceWeight_signed_model]
  simp only [innerSignedWeight, innerMorseInnerModelWeight_tail]

section ActualChain

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  {bordered : Bool} {j : ℝ} {central : Fin (2 * (2 * K + 1) + 1)}
  {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- The actual spatial weight and the actual boundary equivalence
use exactly the same value at each internal cut. -/
theorem innerMorseInnerWeight_actual_at_interface
    (i : Fin (2 * (2 * K + 1))) :
    innerMorseInnerWeight N K a γ G C.leftWall C.rightWall (G.cuts i.castSucc.succ) =
      innerMorseInnerInterfaceWeight N K a γ i :=
  innerMorseInnerWeight_at_interface N K a γ G C.leftWall C.rightWall
    (fun p => (C.walls_inside p).2.1) (fun p => (C.walls_inside p).2.2) i

theorem innerMorseInnerWeight_actual_signed_at_interface
    (sign : Bool) (i : Fin (2 * (2 * K + 1))) :
    innerSignedWeight (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall) sign
        (G.cuts i.castSucc.succ) =
      innerSignedWeight (innerMorseInnerInterfaceWeight N K a γ) sign i := by
  simp only [innerSignedWeight, innerMorseInnerWeight_actual_at_interface N K a γ G C i]

/-- The closed model interval sees interpolation between the images
of the very buffer walls used by that actual model. -/
theorem innerMorseInnerWeight_actual_on_model
    (p : Fin (2 * K + 1))
    (M : InnerRadialModelChart D G bordered j central column (innerModelChainPiece p))
    (hp : C.piece (innerModelChainPiece p) = Sum.inl M)
    {x : ℝ} (hx : x ∈ Icc (G.left (innerModelChainPiece p))
      (G.right (innerModelChainPiece p))) :
    innerMorseInnerWeight N K a γ G C.leftWall C.rightWall x =
      innerInterpolatedWeight
        (M.radius (bufferInnerWall M.buffer 0)) (M.radius (bufferInnerWall M.buffer 1))
        (innerMorseInnerModelWeight N K a γ p 0)
        (innerMorseInnerModelWeight N K a γ p 1) x := by
  have h := innerMorseInnerWeight_on_closed_model N K a γ G C.leftWall C.rightWall
    (fun q => (C.walls_inside q).2.1) (fun q => (C.walls_inside q).2.2)
    p (C.walls_inside (innerModelChainPiece p)).1 hx
  rw [C.leftWall_model hp, C.rightWall_model hp] at h
  exact h

theorem innerMorseInnerWeight_actual_signed_on_model
    (p : Fin (2 * K + 1))
    (M : InnerRadialModelChart D G bordered j central column (innerModelChainPiece p))
    (hp : C.piece (innerModelChainPiece p) = Sum.inl M)
    (sign : Bool) {x : ℝ} (hx : x ∈ Icc (G.left (innerModelChainPiece p))
      (G.right (innerModelChainPiece p))) :
    innerSignedWeight (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall) sign x =
      (innerInterpolatedWeight
        (M.radius (bufferInnerWall M.buffer 0)) (M.radius (bufferInnerWall M.buffer 1))
        (innerMorseInnerModelWeight N K a γ p 0)
        (innerMorseInnerModelWeight N K a γ p 1) x) ^
          (if sign then (1 : ℝ) else -1) := by
  rw [innerSignedWeight_eq_rpow, innerMorseInnerWeight_actual_on_model N K a γ G C p M hp hx]

theorem innerMorseInnerWeight_actual_signed_on_tail
    (side : Bool) (p : Fin K)
    (M : InnerRadialModelChart D G bordered j central column
      (innerModelChainPiece (innerMorseInnerTailSlot K side p)))
    (hp : C.piece (innerModelChainPiece (innerMorseInnerTailSlot K side p)) = Sum.inl M)
    (sign : Bool) {x : ℝ} (hx : x ∈
      Icc (G.left (innerModelChainPiece (innerMorseInnerTailSlot K side p)))
        (G.right (innerModelChainPiece (innerMorseInnerTailSlot K side p)))) :
    innerSignedWeight (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall) sign x =
      (innerMorseInterpolatedWeight N a γ side (innerMorseInnerTailIndex N K side p)
        (M.radius (bufferInnerWall M.buffer 0)) (M.radius (bufferInnerWall M.buffer 1)) x) ^
          (if sign then (1 : ℝ) else -1) := by
  simpa only [innerMorseInnerModelWeight_tail, innerMorseInterpolatedWeight] using
    innerMorseInnerWeight_actual_signed_on_model N K a γ G C
      (innerMorseInnerTailSlot K side p) M hp sign hx

/-- The single central scalar and its physical field see weight one
for either sign on the full closed middle model. -/
theorem innerMorseInnerWeight_actual_signed_on_center
    (sign : Bool) {x : ℝ} (hx : x ∈
      Icc (G.left (innerModelChainPiece (innerMorseInnerCenter K)))
        (G.right (innerModelChainPiece (innerMorseInnerCenter K)))) :
    innerSignedWeight (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall) sign x = 1 := by
  have h := innerMorseInnerWeight_on_closed_center N K a γ G C.leftWall C.rightWall
    (fun p => (C.walls_inside p).2.1) (fun p => (C.walls_inside p).2.2)
    (C.walls_inside (innerModelChainPiece (innerMorseInnerCenter K))).1 hx
  simp only [innerSignedWeight, h, inv_one, ite_self]

/-- One genuine gap constant supplies the spatial weight and every
active boundary entry. No equation is imposed on an exterior dummy
entry whose trace is zero. -/
theorem innerMorseInnerWeight_actual_gap_data (g : Fin (2 * K + 2)) :
    0 < innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ ∧
      EqOn (innerMorseInnerWeight N K a γ G C.leftWall C.rightWall)
        (fun _ => innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ)
        (Ioo (G.left (innerModelChainGap g)) (G.right (innerModelChainGap g))) ∧
      (0 < (innerModelChainGap g).val →
        innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainGap g)
          (innerMorseInnerInterfaceWeight N K a γ) 1 0 =
            innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ∧
      ((innerModelChainGap g).val < 2 * (2 * K + 1) →
        innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainGap g)
          (innerMorseInnerInterfaceWeight N K a γ) 1 1 =
            innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) := by
  refine ⟨innerMorseInnerCutWeight_pos N K a γ _, ?_, ?_, ?_⟩
  · intro x hx
    exact innerMorseInnerWeight_on_gap N K a γ G C.leftWall C.rightWall g
      ⟨hx.1, hx.2.le⟩
  · intro hleft
    change innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainGap g)
        (fun i => innerMorseInnerCutWeight N K a γ i.castSucc.succ) 1 0 =
      innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ
    exact (innerChainScalarRestriction_full_left (2 * (2 * K + 1)) (innerModelChainGap g)
      (innerMorseInnerCutWeight N K a γ) hleft).trans
        (innerMorseInnerCutWeight_gap N K a γ g)
  · intro hright
    change innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainGap g)
        (fun i => innerMorseInnerCutWeight N K a γ i.castSucc.succ) 1 1 =
      innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ
    exact innerChainScalarRestriction_full_right (2 * (2 * K + 1)) (innerModelChainGap g)
      (innerMorseInnerCutWeight N K a γ) hright

end ActualChain

end ContinuousFlexibility.Radial
