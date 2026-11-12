import ContinuousFlexibility.Analysis.ScalarFlowVariation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Continuous angular derivatives with a continuous radial parameter

The radial variable is a parameter throughout.  This elementary calculus
records actual angular derivatives and their joint continuity, without
requiring radial derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def AngularRegular : ℕ → (ℝ → ℝ → ℝ) → Prop
  | 0, F => Continuous (fun p : PolarPoint => F p.1 p.2)
  | n + 1, F => Continuous (fun p : PolarPoint => F p.1 p.2) ∧
      (∀ r, Differentiable ℝ (F r)) ∧ AngularRegular n (fun r => deriv (F r))

theorem AngularRegular.continuous {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) : Continuous (fun p : PolarPoint => F p.1 p.2) := by
  cases n with
  | zero => exact hF
  | succ n => exact hF.1

theorem AngularRegular.congr {n : ℕ} {F G : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (hGF : ∀ r θ, G r θ = F r θ) : AngularRegular n G := by
  have h : G = F := funext fun r => funext fun θ => hGF r θ
  rw [h]
  exact hF

theorem AngularRegular.of_succ {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular (n + 1) F) : AngularRegular n F := by
  induction n generalizing F with
  | zero => exact hF.1
  | succ n ih => exact ⟨hF.1, hF.2.1, ih hF.2.2⟩

theorem angularRegular_time (n : ℕ) (k : ℝ → ℝ) (hk : Continuous k) :
    AngularRegular n (fun r _ => k r) := by
  induction n generalizing k with
  | zero => exact hk.comp continuous_fst
  | succ n ih =>
    refine ⟨hk.comp continuous_fst, fun r => differentiable_const (k r), ?_⟩
    exact (ih (fun _ => 0) continuous_const).congr fun r θ => by simp

theorem AngularRegular.add {n : ℕ} {F G : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (hG : AngularRegular n G) :
    AngularRegular n (fun r θ => F r θ + G r θ) := by
  induction n generalizing F G with
  | zero => exact hF.continuous.add hG.continuous
  | succ n ih =>
    refine ⟨hF.1.add hG.1, fun r => (hF.2.1 r).add (hG.2.1 r), ?_⟩
    apply (ih hF.2.2 hG.2.2).congr
    intro r θ
    have h := ((hF.2.1 r θ).hasDerivAt.add (hG.2.1 r θ).hasDerivAt).congr_of_eventuallyEq
      (f₁ := fun x => F r x + G r x) (Eventually.of_forall fun x => by simp only [Pi.add_apply])
    exact h.deriv

theorem AngularRegular.mul {n : ℕ} {F G : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (hG : AngularRegular n G) :
    AngularRegular n (fun r θ => F r θ * G r θ) := by
  induction n generalizing F G with
  | zero => exact hF.continuous.mul hG.continuous
  | succ n ih =>
    refine ⟨hF.1.mul hG.1, fun r => (hF.2.1 r).mul (hG.2.1 r), ?_⟩
    have hj := (ih hF.2.2 hG.of_succ).add (ih hF.of_succ hG.2.2)
    apply hj.congr
    intro r θ
    have h := ((hF.2.1 r θ).hasDerivAt.mul (hG.2.1 r θ).hasDerivAt).congr_of_eventuallyEq
      (f₁ := fun x => F r x * G r x) (Eventually.of_forall fun x => by simp only [Pi.mul_apply])
    exact h.deriv

theorem AngularRegular.neg {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) : AngularRegular n (fun r θ => -F r θ) :=
  ((angularRegular_time n (fun _ => -1) continuous_const).mul hF).congr
    (fun r θ => by ring)

theorem AngularRegular.sub {n : ℕ} {F G : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (hG : AngularRegular n G) :
    AngularRegular n (fun r θ => F r θ - G r θ) :=
  (hF.add hG.neg).congr (fun r θ => by ring)

/-- Composition in the angular variable keeps the radial parameter fixed. -/
theorem AngularRegular.comp_angle {n : ℕ} {F G : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (hG : AngularRegular n G) :
    AngularRegular n (fun r θ => F r (G r θ)) := by
  induction n generalizing F G with
  | zero => exact hF.continuous.comp (continuous_fst.prodMk hG.continuous)
  | succ n ih =>
    refine ⟨hF.1.comp (continuous_fst.prodMk hG.1),
      fun r => (hF.2.1 r).comp (hG.2.1 r), ?_⟩
    apply ((ih hF.2.2 hG.of_succ).mul hG.2.2).congr
    intro r θ
    have h := ((hF.2.1 r (G r θ)).hasDerivAt.comp θ
      (hG.2.1 r θ).hasDerivAt).congr_of_eventuallyEq
        (f₁ := fun x => F r (G r x))
        (Eventually.of_forall fun x => by simp only [Function.comp_def])
    exact h.deriv

theorem AngularRegular.exp {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) :
    AngularRegular n (fun r θ => Real.exp (F r θ)) := by
  induction n generalizing F with
  | zero => exact Real.continuous_exp.comp hF.continuous
  | succ n ih =>
    refine ⟨Real.continuous_exp.comp hF.1, fun r => (hF.2.1 r).exp, ?_⟩
    apply ((ih hF.of_succ).mul hF.2.2).congr
    intro r θ
    exact (hF.2.1 r θ).hasDerivAt.exp.deriv

theorem AngularRegular.comp_time {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (ρ : ℝ → ℝ) (hρ : Continuous ρ) :
    AngularRegular n (fun r θ => F (ρ r) θ) := by
  induction n generalizing F with
  | zero => exact hF.continuous.comp ((hρ.comp continuous_fst).prodMk continuous_snd)
  | succ n ih =>
    exact ⟨hF.1.comp ((hρ.comp continuous_fst).prodMk continuous_snd),
      fun r => hF.2.1 (ρ r), ih hF.2.2⟩

theorem AngularRegular.contDiff {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) (r : ℝ) : ContDiff ℝ n (F r) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.mpr (hF.continuous.comp (continuous_const.prodMk continuous_id))
  | succ n ih =>
    have h : ContDiff ℝ ((n : ℕ∞ω) + 1) (F r) :=
      contDiff_succ_iff_deriv.mpr ⟨hF.2.1 r, by simp, ih hF.2.2⟩
    simpa only [Nat.cast_add, Nat.cast_one] using h

theorem contDiff_of_angularRegular_all {F : ℝ → ℝ → ℝ}
    (hF : ∀ n, AngularRegular n F) (r : ℝ) : ContDiff ℝ ∞ (F r) :=
  contDiff_infty.mpr fun n => (hF n).contDiff r

/-- The highest actual angular derivative is jointly continuous. -/
theorem AngularRegular.iteratedDeriv_continuous {n : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : AngularRegular n F) :
    Continuous (fun p : PolarPoint => iteratedDeriv n (F p.1) p.2) := by
  induction n generalizing F with
  | zero => simpa only [iteratedDeriv_zero] using hF.continuous
  | succ n ih => simpa only [iteratedDeriv_succ'] using ih hF.2.2

/-- A smooth field on the closed strip has every continuous angular
derivative after clamping the time parameter. -/
theorem angularRegular_closedStripExtend_of_contDiffAt
    {a b : ℝ} (hab : a ≤ b) (A : PolarPoint → ℝ)
    (hA : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ), ContDiffAt ℝ ∞ A p)
    (n : ℕ) :
    AngularRegular n (fun r θ => closedStripExtend hab A (r, θ)) := by
  induction n generalizing A with
  | zero =>
    exact continuous_closedStripExtend hab
      (fun p hp => (hA p hp).continuousAt.continuousWithinAt)
  | succ n ih =>
    have hc : Continuous (closedStripExtend hab A) :=
      continuous_closedStripExtend hab (fun p hp => (hA p hp).continuousAt.continuousWithinAt)
    have hs (r θ : ℝ) :
        HasDerivAt (fun x => closedStripExtend hab A (r, x))
          (angularPartial A (projIcc a b hab r, θ)) θ := by
      exact hasDerivAt_angular_slice
        ((hA (projIcc a b hab r, θ)
          ⟨(projIcc a b hab r).property, mem_univ _⟩).differentiableAt (by simp))
    refine ⟨hc, fun r θ => (hs r θ).differentiableAt, ?_⟩
    have hAθ : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ), ContDiffAt ℝ ∞ (angularPartial A) p :=
      fun p hp => contDiffAt_angularPartial (hA p hp) (m := ∞) (by simp)
    exact (ih (angularPartial A) hAθ).congr fun r θ => (hs r θ).deriv

end ContinuousFlexibility.Analysis
