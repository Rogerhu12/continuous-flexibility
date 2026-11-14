module

public import ContinuousFlexibility.Analysis.FiniteLinearODE
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual finite-interval linear transfer

The transfer is defined by the solutions constructed in FiniteLinearODE.
Uniqueness proves linearity and the two inverse identities. Finite
dimensionality then supplies the continuous linear equivalence.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual solution through a prescribed state, with the coefficient
clamped only outside the requested compact interval. -/
def finiteLinearSolution {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (c : ℝ) (x : E) : ℝ → E :=
  Classical.choose (exists_linear_ode_on_Icc hab A hA c x)

@[simp] theorem finiteLinearSolution_initial {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (c : ℝ) (x : E) :
    finiteLinearSolution hab A hA c x c = x :=
  (Classical.choose_spec (exists_linear_ode_on_Icc hab A hA c x)).1

theorem finiteLinearSolution_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (c : ℝ) (x : E)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivAt (finiteLinearSolution hab A hA c x)
      (A t (finiteLinearSolution hab A hA c x t)) t :=
  (Classical.choose_spec (exists_linear_ode_on_Icc hab A hA c x)).2 t ht

/-- Every actual solution agrees with the selected solution having its initial state. -/
theorem finiteLinearSolution_eq_of_solution {a b c : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (hc : c ∈ Icc a b)
    {f : ℝ → E} (hf : ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t) :
    EqOn (finiteLinearSolution hab A hA c (f c)) f (Icc a b) := by
  apply linear_ode_unique_on_Icc A hA hc
    (fun t ht => finiteLinearSolution_hasDerivAt hab A hA c (f c) ht) hf
  exact finiteLinearSolution_initial hab A hA c (f c)

theorem finiteLinearSolution_add {a b c t : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (hc : c ∈ Icc a b)
    (ht : t ∈ Icc a b) (x y : E) :
    finiteLinearSolution hab A hA c (x + y) t =
      finiteLinearSolution hab A hA c x t + finiteLinearSolution hab A hA c y t := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt
        (fun r => finiteLinearSolution hab A hA c x r + finiteLinearSolution hab A hA c y r)
        (A s (finiteLinearSolution hab A hA c x s + finiteLinearSolution hab A hA c y s)) s := by
    apply ((finiteLinearSolution_hasDerivAt hab A hA c x hs).add
      (finiteLinearSolution_hasDerivAt hab A hA c y hs)).congr_deriv
    rw [map_add]
  exact linear_ode_unique_on_Icc A hA hc
    (fun s hs => finiteLinearSolution_hasDerivAt hab A hA c (x + y) hs) hd
    (by simp only [finiteLinearSolution_initial]) ht

theorem finiteLinearSolution_smul {a b c t : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (hc : c ∈ Icc a b)
    (ht : t ∈ Icc a b) (r : ℝ) (x : E) :
    finiteLinearSolution hab A hA c (r • x) t =
      r • finiteLinearSolution hab A hA c x t := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun t => r • finiteLinearSolution hab A hA c x t)
        (A s (r • finiteLinearSolution hab A hA c x s)) s := by
    apply ((finiteLinearSolution_hasDerivAt hab A hA c x hs).const_smul r).congr_deriv
    rw [map_smul]
  exact linear_ode_unique_on_Icc A hA hc
    (fun s hs => finiteLinearSolution_hasDerivAt hab A hA c (r • x) hs) hd
    (by simp only [finiteLinearSolution_initial]) ht

/-- Changing the base point along a solution preserves that solution. -/
theorem finiteLinearSolution_rebase {a b c d t : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (hd : d ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    finiteLinearSolution hab A hA d (finiteLinearSolution hab A hA c x d) t =
      finiteLinearSolution hab A hA c x t := by
  apply linear_ode_unique_on_Icc A hA hd
    (fun s hs => finiteLinearSolution_hasDerivAt hab A hA d
      (finiteLinearSolution hab A hA c x d) hs)
    (fun s hs => finiteLinearSolution_hasDerivAt hab A hA c x hs) _ ht
  exact finiteLinearSolution_initial hab A hA d (finiteLinearSolution hab A hA c x d)

/-- The transfer and its inverse are both evaluation of actual solutions. -/
def finiteLinearTransfer {a b c d : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) : E ≃ₗ[ℝ] E where
  toFun x := finiteLinearSolution hab A hA c x d
  invFun x := finiteLinearSolution hab A hA d x c
  map_add' x y := finiteLinearSolution_add hab A hA hc hd x y
  map_smul' r x := finiteLinearSolution_smul hab A hA hc hd r x
  left_inv x := by
    change finiteLinearSolution hab A hA d (finiteLinearSolution hab A hA c x d) c = x
    exact (finiteLinearSolution_rebase hab A hA hd hc x).trans
      (finiteLinearSolution_initial hab A hA c x)
  right_inv x := by
    change finiteLinearSolution hab A hA c (finiteLinearSolution hab A hA d x c) d = x
    exact (finiteLinearSolution_rebase hab A hA hc hd x).trans
      (finiteLinearSolution_initial hab A hA d x)

theorem finiteLinearTransfer_apply {a b c d : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (x : E) :
    finiteLinearTransfer hab A hA hc hd x = finiteLinearSolution hab A hA c x d := rfl

/-- The transfer acts on the actual states of any solution. -/
theorem finiteLinearTransfer_actual {a b c d : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) {f : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t) :
    finiteLinearTransfer hab A hA hc hd (f c) = f d :=
  finiteLinearSolution_eq_of_solution hab A hA hc hf hd

/-- In finite dimensions, actual transfer is a continuous linear equivalence. -/
def finiteLinearTransferL [FiniteDimensional ℝ E] {a b c d : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) : E ≃L[ℝ] E :=
  (finiteLinearTransfer hab A hA hc hd).toContinuousLinearEquiv

theorem finiteLinearTransferL_actual [FiniteDimensional ℝ E] {a b c d : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) {f : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t) :
    finiteLinearTransferL hab A hA hc hd (f c) = f d :=
  finiteLinearTransfer_actual hab A hA hc hd hf

end ContinuousFlexibility.Analysis
