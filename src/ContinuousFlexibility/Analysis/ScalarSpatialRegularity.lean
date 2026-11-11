import ContinuousFlexibility.Scalar.HeightDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite scalar spatial regularity with a continuous time parameter

The first coordinate is differentiated; the second is only a continuous
parameter. The recursive predicate uses actual derivatives throughout.
Its elementary closure properties require no time derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual derivative of the spatial slice. This does not use the
totalized full Fréchet derivative when time is only continuous. -/
def scalarSpatialDerivative (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

def ScalarSpatialRegularity : ℕ → (PolarPoint → ℝ) → Prop
  | 0, f => Continuous f
  | n + 1, f => Continuous f ∧
      (∀ x t : ℝ, DifferentiableAt ℝ (fun y => f (y, t)) x) ∧
      ScalarSpatialRegularity n (scalarSpatialDerivative f)

theorem ScalarSpatialRegularity.continuous {n : ℕ} {f : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) : Continuous f := by
  cases n with
  | zero => exact hf
  | succ n => exact hf.1

theorem ScalarSpatialRegularity.of_succ {n : ℕ} {f : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity (n + 1) f) : ScalarSpatialRegularity n f := by
  induction n generalizing f with
  | zero => exact hf.1
  | succ n ih => exact ⟨hf.1, hf.2.1, ih hf.2.2⟩

theorem contDiff_scalarSpatialDerivative {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarSpatialDerivative f) := by
  have haux : ContDiff ℝ ∞ (fun z : PolarPoint × ℝ => f (z.2, z.1.2)) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have hd : ContDiff ℝ ∞
      (fun p : PolarPoint => fderiv ℝ (fun x : ℝ => f (x, p.2)) p.1) :=
    haux.fderiv contDiff_fst (by simp)
  have he : scalarSpatialDerivative f =
      fun p : PolarPoint => (fderiv ℝ (fun x : ℝ => f (x, p.2)) p.1) 1 := by
    funext p
    have hs : ContDiff ℝ ∞ (fun x : ℝ => f (x, p.2)) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    exact ((hs.differentiable (by simp) p.1).hasFDerivAt.hasDerivAt).deriv
  rw [he]
  exact hd.clm_apply contDiff_const

theorem scalarSpatialRegularity_of_contDiff {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) : ScalarSpatialRegularity n f := by
  induction n generalizing f with
  | zero => exact hf.continuous
  | succ n ih =>
      refine ⟨hf.continuous, ?_, ih ?_⟩
      · intro x t
        exact ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp)) x
      · exact contDiff_scalarSpatialDerivative hf

theorem ScalarSpatialRegularity.timeOnly {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (n : ℕ) :
    ScalarSpatialRegularity n (fun p : PolarPoint => ρ p.2) := by
  cases n with
  | zero => exact hρ.comp continuous_snd
  | succ n =>
      refine ⟨hρ.comp continuous_snd, ?_, ?_⟩
      · intro x t
        change DifferentiableAt ℝ (fun _ : ℝ => ρ t) x
        exact differentiableAt_const (ρ t)
      ·
        have he : scalarSpatialDerivative (fun p : PolarPoint => ρ p.2) = fun _ => (0 : ℝ) := by
          funext p
          exact (hasDerivAt_const p.1 (ρ p.2)).deriv
        rw [he]
        exact scalarSpatialRegularity_of_contDiff contDiff_const n

theorem ScalarSpatialRegularity.add {n : ℕ} {f g : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) (hg : ScalarSpatialRegularity n g) :
    ScalarSpatialRegularity n (fun p => f p + g p) := by
  induction n generalizing f g with
  | zero => exact Continuous.add hf hg
  | succ n ih =>
      refine ⟨hf.1.add hg.1, fun x t => (hf.2.1 x t).add (hg.2.1 x t), ?_⟩
      have he : scalarSpatialDerivative (fun p => f p + g p) =
          fun p => scalarSpatialDerivative f p + scalarSpatialDerivative g p := by
        funext p
        exact ((hf.2.1 p.1 p.2).hasDerivAt.fun_add
          (hg.2.1 p.1 p.2).hasDerivAt).deriv
      rw [he]
      exact ih hf.2.2 hg.2.2

theorem ScalarSpatialRegularity.mul {n : ℕ} {f g : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) (hg : ScalarSpatialRegularity n g) :
    ScalarSpatialRegularity n (fun p => f p * g p) := by
  induction n generalizing f g with
  | zero => exact Continuous.mul hf hg
  | succ n ih =>
      refine ⟨hf.1.mul hg.1, fun x t => (hf.2.1 x t).mul (hg.2.1 x t), ?_⟩
      have he : scalarSpatialDerivative (fun p => f p * g p) =
          fun p => scalarSpatialDerivative f p * g p + f p * scalarSpatialDerivative g p := by
        funext p
        exact ((hf.2.1 p.1 p.2).hasDerivAt.fun_mul
          (hg.2.1 p.1 p.2).hasDerivAt).deriv
      rw [he]
      exact (ih hf.2.2 hg.of_succ).add (ih hf.of_succ hg.2.2)

/-- Composition is along each spatial fiber, with the same time. -/
theorem ScalarSpatialRegularity.comp {n : ℕ} {f g : PolarPoint → ℝ}
    (hg : ScalarSpatialRegularity n g) (hf : ScalarSpatialRegularity n f) :
    ScalarSpatialRegularity n (fun p => g (f p, p.2)) := by
  induction n generalizing f g with
  | zero => exact Continuous.comp hg (Continuous.prodMk hf continuous_snd)
  | succ n ih =>
      have hd (x t : ℝ) : HasDerivAt (fun y => g (f (y, t), t))
          (scalarSpatialDerivative g (f (x, t), t) * scalarSpatialDerivative f (x, t)) x := by
        have h := (hg.2.1 (f (x, t)) t).hasDerivAt.comp x
          (hf.2.1 x t).hasDerivAt
        have he : (fun y => g (y, t)) ∘ (fun y => f (y, t)) =
            fun y => g (f (y, t), t) := by
          funext y
          exact Function.comp_apply
        rw [he] at h
        exact h
      refine ⟨hg.1.comp (hf.1.prodMk continuous_snd),
        fun x t => (hd x t).differentiableAt, ?_⟩
      have he : scalarSpatialDerivative (fun p => g (f p, p.2)) =
          fun p => scalarSpatialDerivative g (f p, p.2) * scalarSpatialDerivative f p := by
        funext p
        exact (hd p.1 p.2).deriv
      rw [he]
      exact (ih hg.2.2 hf.of_succ).mul hf.2.2

theorem ScalarSpatialRegularity.time_comp {n : ℕ} {f : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) {τ : ℝ → ℝ} (hτ : Continuous τ) :
    ScalarSpatialRegularity n (fun p : PolarPoint => f (p.1, τ p.2)) := by
  induction n generalizing f with
  | zero => exact Continuous.comp hf (continuous_fst.prodMk (hτ.comp continuous_snd))
  | succ n ih =>
      refine ⟨hf.1.comp (continuous_fst.prodMk (hτ.comp continuous_snd)),
        fun x t => hf.2.1 x (τ t), ?_⟩
      have he : scalarSpatialDerivative (fun p : PolarPoint => f (p.1, τ p.2)) =
          fun p : PolarPoint => scalarSpatialDerivative f (p.1, τ p.2) := by
        funext p
        rfl
      rw [he]
      exact ih hf.2.2

theorem ScalarSpatialRegularity.exp {n : ℕ} {f : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) :
    ScalarSpatialRegularity n (fun p => Real.exp (f p)) :=
  (scalarSpatialRegularity_of_contDiff
    (Real.contDiff_exp.comp contDiff_fst) n).comp hf

theorem ScalarSpatialRegularity.neg {n : ℕ} {f : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) :
    ScalarSpatialRegularity n (fun p => -f p) := by
  simpa only [neg_one_mul] using
    (scalarSpatialRegularity_of_contDiff
      (contDiff_const : ContDiff ℝ ∞ (fun _ : PolarPoint => (-1 : ℝ))) n).mul hf

theorem ScalarSpatialRegularity.continuous_iteratedDeriv
    {n : ℕ} {f : PolarPoint → ℝ} (hf : ScalarSpatialRegularity n f)
    (k : ℕ) (hk : k ≤ n) :
    Continuous (fun p : PolarPoint => iteratedDeriv k (fun x => f (x, p.2)) p.1) := by
  induction n generalizing f k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa only [iteratedDeriv_zero] using hf.continuous
  | succ n ih =>
      cases k with
      | zero => simpa only [iteratedDeriv_zero] using hf.continuous
      | succ k =>
          have h := ih hf.2.2 k (Nat.le_of_succ_le_succ hk)
          simpa only [scalarSpatialDerivative, ← iteratedDeriv_succ'] using h

theorem ScalarSpatialRegularity.differentiable_iteratedDeriv
    {n : ℕ} {f : PolarPoint → ℝ} (hf : ScalarSpatialRegularity (n + 1) f)
    (x t : ℝ) : DifferentiableAt ℝ
      (iteratedDeriv n (fun y => f (y, t))) x := by
  induction n generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hf.2.1 x t
  | succ n ih =>
      have h := ih hf.2.2
      simpa only [scalarSpatialDerivative, ← iteratedDeriv_succ'] using h

/-- Every finite true spatial jet gives genuine smoothness of each slice. -/
theorem contDiff_spatialSlice_of_all_regularity
    {f : PolarPoint → ℝ} (hf : ∀ n : ℕ, ScalarSpatialRegularity n f) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => f (x, t)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _ x
  exact (hf (n + 1)).differentiable_iteratedDeriv x t

end ContinuousFlexibility.Analysis
