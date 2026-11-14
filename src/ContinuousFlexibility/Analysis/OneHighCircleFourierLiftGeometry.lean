module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierCompositionLow

/-!
# Canonical derivative defects of circle lifts

The geometry entering all tame constants is the periodic function `h' - 1`.
Its continuous circle jets are constructed from the actual derivative of the
smooth degree-one lift, and are shared with the flow estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

/-- The actual derivative defect of a degree-one real circle lift. -/
def circleLiftDerivativeDefect (h : ℝ → ℝ) : ℝ → ℝ := fun x => deriv h x - 1

theorem contDiff_circleLiftDerivativeDefect {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (circleLiftDerivativeDefect h) :=
  (contDiff_infty_iff_deriv.mp hh).2.sub contDiff_const

variable {P : ℝ} [Fact (0 < P)]

/-- Differentiating the degree-one lift identity gives genuine periodicity
of the derivative defect. -/
theorem periodic_circleLiftDerivativeDefect (h : ℝ → ℝ)
    (hlift : ∀ x, h (x + P) = h x + P) : Periodic (circleLiftDerivativeDefect h) P := by
  have he : (fun x : ℝ => h (x + P)) = (fun x : ℝ => h x + P) := funext hlift
  have hd := congrArg deriv he
  intro x
  have hx := congrFun hd x
  rw [deriv_comp_add_const, deriv_add_const] at hx
  simp only [circleLiftDerivativeDefect, hx]

/-- Canonical actual circle jets of the derivative defect. -/
def circleLiftDefectJet (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (circleLiftDerivativeDefect h)
    (periodic_circleLiftDerivativeDefect h hlift) (contDiff_circleLiftDerivativeDefect hh) n

@[simp] theorem circleLiftDefectJet_coe_apply (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) (x : ℝ) :
    circleLiftDefectJet h hh hlift n (x : AddCircle P) =
      iteratedDeriv n (circleLiftDerivativeDefect h) x :=
  periodicCircleJet_coe_apply _ _ _ n x

@[simp] theorem circleLiftDefectJet_zero_coe_apply (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (x : ℝ) :
    circleLiftDefectJet h hh hlift 0 (x : AddCircle P) = deriv h x - 1 := by
  simp only [circleLiftDefectJet_coe_apply, iteratedDeriv_zero, circleLiftDerivativeDefect]

theorem circleLiftDefectJet_hasDerivAt (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => circleLiftDefectJet h hh hlift n (y : AddCircle P))
      (circleLiftDefectJet h hh hlift (n + 1) (x : AddCircle P)) x :=
  periodicCircleJet_hasDerivAt _ _ _ n x

/-- The defect jets are exactly the shifted actual lift derivatives;
only the zeroth defect jet has the constant-one correction. -/
theorem circleLiftDefectJet_coe_apply_eq (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) (n : ℕ) (x : ℝ) :
    circleLiftDefectJet h hh hlift n (x : AddCircle P) =
      iteratedDeriv (n + 1) h x - if n = 0 then 1 else 0 := by
  rw [circleLiftDefectJet_coe_apply]
  change iteratedDeriv n (fun y : ℝ => deriv h y - 1) x = _
  rw [iteratedDeriv_fun_sub (n := n)
    ((contDiff_infty_iff_deriv.mp hh).2.contDiffAt.of_le (by simp)) contDiffAt_const,
    ← iteratedDeriv_succ', iteratedDeriv_const]

end ContinuousFlexibility.Analysis
