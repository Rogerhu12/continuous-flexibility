import ContinuousFlexibility.Analysis.N04NegativeChartOpticalSpeedBounds
import ContinuousFlexibility.Analysis.N01cFiniteAffineSpeedFactors
import ContinuousFlexibility.Analysis.N01cComponentSpeedPeriodicity
import ContinuousFlexibility.Analysis.N01ActualRootGeometry

/-!
# Actual divided characteristic fields on a complete negative half

The inward drift and divided optical speed are the original normalized
factors times the actual affine optical square root. These same fields
are smooth at every point of the closed half on every finite state plot.
No extension radius enters their definitions or their physical identities.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

variable (W : N04RealizationStart)

def negativeInwardPoint (m : ℕ) (side : Bool) (p : PolarPoint) : PolarPoint :=
  (inwardComponentPoint (W.C.left m) (W.C.right m) side p.1, p.2)

theorem negativeInwardPoint_contDiff (m : ℕ) (side : Bool) :
    ContDiff ℝ ∞ (W.negativeInwardPoint m side) := by
  cases side <;> simp only [negativeInwardPoint, inwardComponentPoint,
    Bool.false_eq_true, ↓reduceIte]
  · exact (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  · exact (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

theorem negativeInwardPoint_mem_annular (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    W.negativeInwardPoint m side p ∈ annularOpen W.D := by
  have hc := W.through03.1.1.2.2.2.1.1 m
  have hi := inwardComponentPoint_mem side
    (show p.1 ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) from
      ⟨hp.1, hp.2.trans (W.negativeOpticalWidth_le_component m side)⟩)
  exact ⟨⟨hc.1.trans_le hi.1, hi.2.trans_lt hc.2.2⟩, mem_univ _⟩

private theorem negativeHalf_partA : N01PartA W.D W.T W.S W.C := by
  have h := W.through03.1.1
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem negativeHalf_partB : N01PartB W.D W.S W.C W.base W.ε := by
  have h := W.through03.1.1
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1⟩

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}

def fullHalfDrift (_F : NegativeOpticalFactors W e)
    (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) (p : PolarPoint) : ℝ :=
  -n01ComponentRootOrientation side *
    normalizedSpeedFactor W.D W.S W.C 0 z (W.negativeInwardPoint m side p)

def fullHalfSpeed (F : NegativeOpticalFactors W e)
    (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) (p : PolarPoint) : ℝ :=
  F.opticalSpeed z m side p.1 *
    normalizedSpeedFactor W.D W.S W.C 1 z (W.negativeInwardPoint m side p)

variable (F : NegativeOpticalFactors W e)

theorem fullHalfFields_periodic (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) :
    (∀ t, Function.Periodic (fun θ => F.fullHalfDrift z m side (t, θ)) Real.pi) ∧
      ∀ t, Function.Periodic (fun θ => F.fullHalfSpeed z m side (t, θ)) Real.pi := by
  have hp (i : Fin 2) (t θ : ℝ) :
      normalizedSpeedFactor W.D W.S W.C i z (W.negativeInwardPoint m side (t, θ + Real.pi)) =
        normalizedSpeedFactor W.D W.S W.C i z (W.negativeInwardPoint m side (t, θ)) := by
    simpa only [negativeInwardPoint, Prod.mk_add_mk, add_zero] using
      normalizedSpeedFactor_periodic (C := W.C) W.hS z i
        (W.negativeInwardPoint m side (t, θ))
  exact ⟨fun t θ => congrArg (fun a => -n01ComponentRootOrientation side * a) (hp 0 t θ),
    fun t θ => congrArg (fun a => F.opticalSpeed z m side t * a) (hp 1 t θ)⟩

theorem fullHalfFields_reference (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    F.fullHalfDrift (W.C.referenceState, 0) m side p = 0 ∧
      F.fullHalfSpeed (W.C.referenceState, 0) m side p = Real.sqrt (F.reference m side p.1) := by
  have hf := normalizedSpeedFactor_reference W.hS W.hT W.negativeHalf_partA
    W.ε_pos W.negativeHalf_partB (W.negativeInwardPoint_mem_annular m side hp)
  simp only [fullHalfDrift, fullHalfSpeed, hf.1, hf.2, mul_zero, mul_one,
    opticalSpeed, F.stateSquare_reference]

theorem fullHalfFields_minus_speed
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p.1 ∈ Ioc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    n01ComponentRootOrientation side *
        minusCharacteristicSpeed (originalCoefficients W.D W.S W.C z)
          (W.negativeInwardPoint m side p) =
      F.fullHalfDrift z m side p - n01ComponentRootOrientation side *
        Real.sqrt p.1 * F.fullHalfSpeed z m side p := by
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) hz
  have hf := minusCharacteristicSpeed_normalized_factors W.hS W.hT
    W.negativeHalf_partA W.negativeHalf_partB hz'
    (W.negativeInwardPoint_mem_annular m side ⟨hp.1.le, hp.2⟩)
  have ho : Real.sqrt (-deriv (stateProfile W.D W.S W.C z.1)
        (W.negativeInwardPoint m side p).1 /
        ((W.negativeInwardPoint m side p).1 * stateProfile W.D W.S W.C z.1
          (W.negativeInwardPoint m side p).1)) =
      Real.sqrt p.1 * F.opticalSpeed z m side p.1 := by
    change Real.sqrt (n01aOpticalRadicand (stateProfile W.D W.S W.C z.1)
      (inwardComponentPoint (W.C.left m) (W.C.right m) side p.1)) = _
    rw [F.stateSquare_actual z m side
      ⟨hp.1, hp.2.trans_lt (W.negativeOpticalWidth_lt_component m side)⟩,
      Real.sqrt_mul hp.1.le]
    rfl
  rw [hf, ho]
  dsimp only [fullHalfDrift, fullHalfSpeed]
  ring

/-- A finite state plot is smooth at each actual point, including the
physical root. This supplies an open germ without any quantitative
assumption on the size of an extension outside the closed half. -/
theorem fullHalfFields_finiteAffine_contDiffAt
    {n : ℕ} (x : AnnularState W.S × ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState W.S × ℝ)) (y : Fin n → ℝ)
    (hy : x + L y ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (m : ℕ) (side : Bool) (p : PolarPoint)
    (hp : p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    ContDiffAt ℝ ∞ (fun q : (Fin n → ℝ) × PolarPoint =>
      F.fullHalfDrift (x + L q.1) m side q.2) (y, p) ∧
    ContDiffAt ℝ ∞ (fun q : (Fin n → ℝ) × PolarPoint =>
      F.fullHalfSpeed (x + L q.1) m side q.2) (y, p) := by
  have hy' : x + L y ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) hy
  let V := ((fun q => x + L q) ⁻¹' stateNeighborhood W.S W.C W.base W.ε) ×ˢ
    annularOpen W.D
  have hV : IsOpen V :=
    ((isOpen_stateNeighborhood W.S W.C W.base W.ε).preimage
      (continuous_const.add L.continuous)).prod (isOpen_Ioo.prod isOpen_univ)
  have hn (i : Fin 2) : ContDiffAt ℝ ∞ (fun q : (Fin n → ℝ) × PolarPoint =>
      normalizedSpeedFactor W.D W.S W.C i (x + L q.1)
        (W.negativeInwardPoint m side q.2)) (y, p) :=
    ((contDiffOn_normalizedSpeedFactor_finiteAffine W.hS W.hT W.negativeHalf_partA
      W.negativeHalf_partB x L i).contDiffAt
      (hV.mem_nhds ⟨hy', W.negativeInwardPoint_mem_annular m side hp⟩)).comp (y, p)
        (contDiff_fst.prodMk
          ((W.negativeInwardPoint_contDiff m side).comp contDiff_snd)).contDiffAt
  let K := stateJointKappaCLM W.hS W.hT W.radial.1 m
  have hk : ContDiff ℝ ∞ (fun v : Fin n → ℝ => stateKappa W.S (x + L v).1 m) := by
    have he : (fun v : Fin n → ℝ => stateKappa W.S (x + L v).1 m) =
        fun v => K x + (K.comp L) v := by
      funext v
      change K (x + L v) = K x + (K.comp L) v
      rw [map_add]
      rfl
    rw [he]
    exact contDiff_const.add (K.comp L).contDiff
  have hq : ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × PolarPoint =>
      F.stateSquare (x + L q.1) m side q.2.1) :=
    ((F.reference_smooth m side).comp contDiff_snd.fst).sub
      ((hk.comp contDiff_fst).mul ((F.control_smooth m side).comp contDiff_snd.fst))
  exact ⟨contDiffAt_const.mul (hn 0),
    (hq.contDiffAt.sqrt (F.stateSquare_pos hy m side hp).ne').mul (hn 1)⟩

end NegativeOpticalFactors

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_minus_speed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_minus_speed
