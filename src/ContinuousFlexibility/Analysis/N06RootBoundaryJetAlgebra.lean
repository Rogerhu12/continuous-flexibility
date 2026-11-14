module

public import ContinuousFlexibility.Analysis.N06RelativeBoundarySymmetry
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Boundary algebra for the regular root transport system

Multiplication by the radial coordinate lowers a genuine boundary jet
by one order. The regular Euler operator has the exact boundary
multiplier n + a. Products with an angular derivative are expressed
using only the actual radial trace jets and their ordinary angular
derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n06_iteratedDeriv_coord_mul_zero {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f 0) (n : ℕ) :
    iteratedDeriv n (fun x => x * f x) 0 =
      (n : ℝ) * iteratedDeriv (n - 1) f 0 := by
  cases n with
  | zero => simp
  | succ n =>
      have hid : ContDiffAt ℝ (n + 1 : ℕ) (fun x : ℝ => x) 0 := contDiffAt_id
      rw [iteratedDeriv_fun_mul hid
        (hf.of_le (by simp : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞))]
      rw [Finset.sum_eq_single 1]
      · simp only [iteratedDeriv_fun_id_zero, if_pos rfl, ite_true, Nat.choose_one_right,
          mul_one, Nat.add_sub_cancel]
      · intro i hi hne
        simp only [iteratedDeriv_fun_id_zero, if_neg hne, mul_zero, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem n06_iteratedDeriv_coord_sq_mul_zero {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f 0) (n : ℕ) :
    iteratedDeriv n (fun x => x ^ 2 * f x) 0 =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * iteratedDeriv (n - 2) f 0 := by
  have he : (fun x : ℝ => x ^ 2 * f x) = fun x => x * (x * f x) := by
    funext x
    ring
  have hxf : ContDiffAt ℝ ∞ (fun x : ℝ => x * f x) 0 := contDiffAt_id.mul hf
  rw [he, n06_iteratedDeriv_coord_mul_zero hxf,
    n06_iteratedDeriv_coord_mul_zero hf]
  simp only [Nat.sub_sub]
  ring

theorem n06_iteratedDeriv_euler_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x => x * deriv f x + a * f x) 0 =
      ((n : ℝ) + a) * iteratedDeriv n f 0 := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  cases n with
  | zero => simp
  | succ n =>
      have hfirst : ContDiffAt ℝ (n + 1 : ℕ) (fun x : ℝ => x * deriv f x) 0 :=
        (contDiffAt_id.mul hf'.contDiffAt).of_le (by simp)
      have hsecond : ContDiffAt ℝ (n + 1 : ℕ) (fun x : ℝ => a * f x) 0 :=
        (contDiffAt_const.mul hf.contDiffAt).of_le (by simp)
      rw [iteratedDeriv_fun_add hfirst hsecond,
        n06_iteratedDeriv_coord_mul_zero hf'.contDiffAt,
        iteratedDeriv_const_mul_field]
      simp only [Nat.add_sub_cancel, ← iteratedDeriv_succ']
      ring

/-- The finite Leibniz polynomial uses the actual trace jets, with
ordinary angular differentiation of each trace. -/
def n06RootJetProduct (a f : ℕ → ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i θ * deriv (f (n - i)) θ

theorem n06_radialBoundaryJet_angularPartial {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℕ) (θ : ℝ) :
    radialBoundaryJet (angularPartial f) c n θ =
      deriv (radialBoundaryJet f c n) θ := by
  have htrace : radialBoundaryJet f c n = fun η => mixedDerivative n 0 f (c, η) := by
    funext η
    simp only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero]
  rw [htrace, deriv_cylinder_angular_slice
    ((contDiff_mixedDerivative hf n 0).differentiable (by simp)) c θ,
    angularPartial_mixedDerivative hf n 0]
  have he := mixedDerivative_angularPartial isOpen_univ hf.contDiffOn n 0
    (mem_univ (c, θ))
  simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero] using he

theorem n06_radialBoundaryJet_mul_angularPartial {a f : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (n : ℕ) (θ : ℝ) :
    radialBoundaryJet (fun p => a p * angularPartial f p) c n θ =
      n06RootJetProduct (radialBoundaryJet a c) (radialBoundaryJet f c) n θ := by
  have ha' : ContDiff ℝ ∞ (fun r => a (r, θ)) :=
    ha.comp (contDiff_id.prodMk contDiff_const)
  have hf' : ContDiff ℝ ∞ (fun r => angularPartial f (r, θ)) :=
    (contDiff_cylinder_angularPartial hf).comp (contDiff_id.prodMk contDiff_const)
  change iteratedDeriv n (fun r => a (r, θ) * angularPartial f (r, θ)) c = _
  rw [iteratedDeriv_fun_mul (ha'.contDiffAt.of_le (by simp))
    (hf'.contDiffAt.of_le (by simp))]
  unfold n06RootJetProduct
  apply Finset.sum_congr rfl
  intro i hi
  change (n.choose i : ℝ) * radialBoundaryJet a c i θ *
    radialBoundaryJet (angularPartial f) c (n - i) θ = _
  rw [n06_radialBoundaryJet_angularPartial hf]

end ContinuousFlexibility.Analysis
