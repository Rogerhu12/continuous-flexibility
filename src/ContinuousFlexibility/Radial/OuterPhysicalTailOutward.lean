import ContinuousFlexibility.Radial.OuterPhysicalTailState

/-!
# The actual tail state in the outward radial coordinate

The outward coordinate is r on the right and -r on the left. Its flux
is the correspondingly signed physical flux, divided by the selected
positive state scale. Both orientations satisfy the same genuine
first-order system on a half-open interval with its entrance included.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def outerTailSign (right : Bool) : ℝ := if right then 1 else -1

def outerTailOutwardWeight (D : ReferenceData) (right : Bool) (t : ℝ) : ℝ :=
  D.w (outerTailSign right * t)

def outerTailOutwardLift (D : ReferenceData) (right : Bool) (j : ℕ)
    (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  tailPhysicalLift D right j u (outerTailSign right * t)

def outerTailOutwardScaledFlux (D : ReferenceData) (right : Bool) (j : ℕ)
    (lam : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  outerTailSign right * tailPhysicalFlux D right j u (outerTailSign right * t) / lam

/-- The increasing outward interval has precisely the signed-logarithmic
tail as its inverse image, with the entrance retained. -/
theorem outerTail_outward_log_mem {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) {entrance t : ℝ} (hentry : 0 < entrance)
    (ht : t ∈ Ico (outerTailSign right * entrance)
      (outerTailSign right * tailPhysicalEndpoint D right)) :
    0 < outerTailSign right * t ∧
      tailPhysicalLog right (outerTailSign right * t) ∈
        Ico (tailPhysicalLog right entrance)
          (tailPhysicalLog right (tailPhysicalEndpoint D right)) := by
  cases right with
  | true =>
      have ht' : t ∈ Ico entrance D.b := by
        simpa [outerTailSign, tailPhysicalEndpoint] using ht
      have hpos : 0 < t := hentry.trans_le ht'.1
      have hh : log t ∈ Ico (log entrance) (log D.b) :=
        ⟨log_le_log hentry ht'.1, log_lt_log hpos ht'.2⟩
      simpa [outerTailSign, tailPhysicalLog, tailPhysicalEndpoint] using And.intro hpos hh
  | false =>
      have ht' : t ∈ Ico (-entrance) (-D.a) := by
        simpa [outerTailSign, tailPhysicalEndpoint] using ht
      have hlow : -t ≤ entrance := by linarith only [ht'.1]
      have hhigh : D.a < -t := by linarith only [ht'.2]
      have hpos : 0 < -t := hD.1.trans hhigh
      have hh : -log (-t) ∈ Ico (-log entrance) (-log D.a) :=
        ⟨neg_le_neg (log_le_log hpos hlow), neg_lt_neg (log_lt_log hD.1 hhigh)⟩
      simpa [outerTailSign, tailPhysicalLog, tailPhysicalEndpoint] using And.intro hpos hh

/-- The actual gauge lift satisfies the physical outward state equation
on the full half-open tail, including the regular entrance. -/
theorem morsePhysicalDeepTail_outward_firstOrder
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K lam : ℝ}
    (hentry : 0 < entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u
      (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    (hsys : TailFirstOrderSystem
      (morsePhysicalDeepTail M D right j start entrance η K).p
      (morsePhysicalDeepTail M D right j start entrance η K).Λ u v
      (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
        (morsePhysicalDeepTail M D right j start entrance η K).endpoint)) :
    OuterFirstOrderSystem
      (fun t => lam / outerTailOutwardWeight D right t)
      (fun t => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) t / (lam * t))
      (outerTailOutwardLift D right j u)
      (outerTailOutwardScaledFlux D right j lam u)
      (Ico (outerTailSign right * entrance)
        (outerTailSign right * tailPhysicalEndpoint D right)) := by
  intro t ht
  have hcoord := outerTail_outward_log_mem hD right hentry ht
  have hstate := morsePhysicalDeepTail_state_firstOrder_at hD hlam hT hu hsys hcoord.2
  rw [tailPhysicalRadius_log right hcoord.1] at hstate
  cases right with
  | true =>
      simpa [outerTailOutwardWeight, outerTailOutwardLift,
        outerTailOutwardScaledFlux, outerTailSign] using hstate
  | false =>
      simp only [outerTailOutwardWeight, outerTailOutwardLift, outerTailOutwardScaledFlux,
        outerTailSign, Bool.false_eq_true, ite_false, neg_one_mul] at hstate ⊢
      have hwd : deriv (fun y => D.w (-y)) t = -deriv D.w (-t) := by
        have hd := (hD.2.2.1.1.differentiable (by simp) (-t)).hasDerivAt.comp t
          (hasDerivAt_id t).neg
        simpa only [Function.comp_def, mul_neg_one] using hd.deriv
      constructor
      · exact (hstate.1.comp t (hasDerivAt_id t).neg).congr_deriv (by ring)
      · have heq : (fun y => -tailPhysicalFlux D false j u (-y) / lam) =
            fun y => -(tailPhysicalFlux D false j u (-y) / lam) := by
          funext y
          ring
        rw [heq, hwd]
        exact ((hstate.2.comp t (hasDerivAt_id t).neg).neg).congr_deriv (by ring)

/-- The chosen coordinate sign is its own reciprocal. -/
theorem outerTailSign_mul_self (right : Bool) : outerTailSign right * outerTailSign right = 1 := by
  cases right <;> norm_num [outerTailSign]

@[simp] theorem outerTailOutwardLift_entrance (D : ReferenceData) (right : Bool)
    (j : ℕ) (u : ℝ → ℝ) (entrance : ℝ) :
    outerTailOutwardLift D right j u (outerTailSign right * entrance) =
      tailPhysicalLift D right j u entrance := by
  unfold outerTailOutwardLift
  rw [← mul_assoc, outerTailSign_mul_self, one_mul]

@[simp] theorem outerTailOutwardScaledFlux_entrance (D : ReferenceData) (right : Bool)
    (j : ℕ) (lam : ℝ) (u : ℝ → ℝ) (entrance : ℝ) :
    outerTailOutwardScaledFlux D right j lam u (outerTailSign right * entrance) =
      outerTailSign right * tailPhysicalFlux D right j u entrance / lam := by
  unfold outerTailOutwardScaledFlux
  rw [← mul_assoc, outerTailSign_mul_self, one_mul]

end ContinuousFlexibility.Radial
