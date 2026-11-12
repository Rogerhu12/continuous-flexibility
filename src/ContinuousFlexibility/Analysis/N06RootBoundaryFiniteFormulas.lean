import ContinuousFlexibility.Analysis.N06RootBoundaryRecursion
import ContinuousFlexibility.Analysis.N06RootLabelJets

/-!
# The finite boundary formulas used by the actual root patch

The even traces through radial order four and odd traces through order
three are fixed differential expressions in the physical coefficient
traces and the derivative of the actual label. These equalities follow
from the genuine root transport equation. No regularity of G as a
function of the state is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

abbrev N06RootBoundaryInputs := Fin 9 → ℝ → ℝ

def n06RootBoundaryInputs (d c : PolarPoint → ℝ) (β : ℝ → ℝ) : N06RootBoundaryInputs :=
  ![radialBoundaryJet d 0 0, radialBoundaryJet d 0 1,
    radialBoundaryJet d 0 2, radialBoundaryJet d 0 3,
    radialBoundaryJet c 0 0, radialBoundaryJet c 0 1,
    radialBoundaryJet c 0 2, radialBoundaryJet c 0 3, deriv β]

def n06RootOddFormula0 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  (2 / 3 : ℝ) * v 4 θ * v 8 θ

def n06RootEvenFormula1 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  -(v 0 θ * v 8 θ)

def n06RootEvenFormula2 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  -(v 0 θ * deriv (n06RootEvenFormula1 v) θ + v 1 θ * v 8 θ)

def n06RootOddFormula1 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  (2 / 5 : ℝ) * (v 4 θ * deriv (n06RootEvenFormula1 v) θ + v 5 θ * v 8 θ -
    v 0 θ * deriv (n06RootOddFormula0 v) θ)

def n06RootEvenFormula3 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  -(v 0 θ * deriv (n06RootEvenFormula2 v) θ +
    2 * v 1 θ * deriv (n06RootEvenFormula1 v) θ + v 2 θ * v 8 θ) +
      2 * v 4 θ * deriv (n06RootOddFormula0 v) θ

def n06RootOddFormula2 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  (2 / 7 : ℝ) * (v 4 θ * deriv (n06RootEvenFormula2 v) θ +
    2 * v 5 θ * deriv (n06RootEvenFormula1 v) θ + v 6 θ * v 8 θ -
      2 * (v 0 θ * deriv (n06RootOddFormula1 v) θ +
        v 1 θ * deriv (n06RootOddFormula0 v) θ))

def n06RootEvenFormula4 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  -(v 0 θ * deriv (n06RootEvenFormula3 v) θ +
    3 * v 1 θ * deriv (n06RootEvenFormula2 v) θ +
    3 * v 2 θ * deriv (n06RootEvenFormula1 v) θ + v 3 θ * v 8 θ) +
      6 * (v 4 θ * deriv (n06RootOddFormula1 v) θ +
        v 5 θ * deriv (n06RootOddFormula0 v) θ)

def n06RootOddFormula3 (v : N06RootBoundaryInputs) (θ : ℝ) : ℝ :=
  (2 / 9 : ℝ) * (v 4 θ * deriv (n06RootEvenFormula3 v) θ +
    3 * v 5 θ * deriv (n06RootEvenFormula2 v) θ +
    3 * v 6 θ * deriv (n06RootEvenFormula1 v) θ + v 7 θ * v 8 θ -
      3 * (v 0 θ * deriv (n06RootOddFormula2 v) θ +
        2 * v 1 θ * deriv (n06RootOddFormula1 v) θ +
        v 2 θ * deriv (n06RootOddFormula0 v) θ))

private theorem n06RootJetProduct_zero (a f : ℕ → ℝ → ℝ) (θ : ℝ) :
    n06RootJetProduct a f 0 θ = a 0 θ * deriv (f 0) θ := by
  simp [n06RootJetProduct]

private theorem n06RootJetProduct_one (a f : ℕ → ℝ → ℝ) (θ : ℝ) :
    n06RootJetProduct a f 1 θ = a 0 θ * deriv (f 1) θ + a 1 θ * deriv (f 0) θ := by
  norm_num [n06RootJetProduct, Finset.sum_range_succ]

private theorem n06RootJetProduct_two (a f : ℕ → ℝ → ℝ) (θ : ℝ) :
    n06RootJetProduct a f 2 θ = a 0 θ * deriv (f 2) θ +
      2 * a 1 θ * deriv (f 1) θ + a 2 θ * deriv (f 0) θ := by
  norm_num [n06RootJetProduct, Finset.sum_range_succ]

private theorem n06RootJetProduct_three (a f : ℕ → ℝ → ℝ) (θ : ℝ) :
    n06RootJetProduct a f 3 θ = a 0 θ * deriv (f 3) θ +
      3 * a 1 θ * deriv (f 2) θ + 3 * a 2 θ * deriv (f 1) θ +
        a 3 θ * deriv (f 0) θ := by
  norm_num [n06RootJetProduct, Finset.sum_range_succ]

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

theorem n06_boundary_finite_formulas
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀) :
    let v := n06RootBoundaryInputs d c₀ β
    radialBoundaryJet (extendedRootEven G) 0 1 = n06RootEvenFormula1 v ∧
    radialBoundaryJet (extendedRootEven G) 0 2 = n06RootEvenFormula2 v ∧
    radialBoundaryJet (extendedRootEven G) 0 3 = n06RootEvenFormula3 v ∧
    radialBoundaryJet (extendedRootEven G) 0 4 = n06RootEvenFormula4 v ∧
    radialBoundaryJet (extendedRootOddCoefficient G) 0 0 = n06RootOddFormula0 v ∧
    radialBoundaryJet (extendedRootOddCoefficient G) 0 1 = n06RootOddFormula1 v ∧
    radialBoundaryJet (extendedRootOddCoefficient G) 0 2 = n06RootOddFormula2 v ∧
    radialBoundaryJet (extendedRootOddCoefficient G) 0 3 = n06RootOddFormula3 v := by
  let v := n06RootBoundaryInputs d c₀ β
  have he0 : radialBoundaryJet (extendedRootEven G) 0 0 = β :=
    funext P.n06_even_boundary_jet_zero
  have ho0 : radialBoundaryJet (extendedRootOddCoefficient G) 0 0 = n06RootOddFormula0 v := by
    funext θ
    exact P.n06_odd_boundary_jet_zero θ
  have he1 : radialBoundaryJet (extendedRootEven G) 0 1 = n06RootEvenFormula1 v := by
    funext θ
    have h := P.n06_even_boundary_recursion hd hc₀ 0 θ
    simp only [n06RootJetProduct_zero, he0] at h
    norm_num at h
    exact h
  have he2 : radialBoundaryJet (extendedRootEven G) 0 2 = n06RootEvenFormula2 v := by
    funext θ
    have h := P.n06_even_boundary_recursion hd hc₀ 1 θ
    simp only [n06RootJetProduct_one, he0, he1] at h
    norm_num at h
    apply h.trans
    change _ = -(radialBoundaryJet d 0 0 θ * deriv (n06RootEvenFormula1 v) θ +
      radialBoundaryJet d 0 1 θ * deriv β θ)
    ring
  have ho1 : radialBoundaryJet (extendedRootOddCoefficient G) 0 1 = n06RootOddFormula1 v := by
    funext θ
    have h := P.n06_odd_boundary_recursion_solved hd hc₀ 1 θ
    simp only [n06RootJetProduct_one, he0, he1, show 1 - 1 = (0 : ℕ) from rfl,
      n06RootJetProduct_zero, ho0] at h
    norm_num at h
    rw [h]
    change (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootEvenFormula1 v) θ +
        radialBoundaryJet c₀ 0 1 θ * deriv β θ -
          radialBoundaryJet d 0 0 θ * deriv (n06RootOddFormula0 v) θ) / (5 / 2 : ℝ) =
      (2 / 5 : ℝ) * (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootEvenFormula1 v) θ +
        radialBoundaryJet c₀ 0 1 θ * deriv β θ -
          radialBoundaryJet d 0 0 θ * deriv (n06RootOddFormula0 v) θ)
    ring
  have he3 : radialBoundaryJet (extendedRootEven G) 0 3 = n06RootEvenFormula3 v := by
    funext θ
    have h := P.n06_even_boundary_recursion hd hc₀ 2 θ
    simp only [n06RootJetProduct_two, he0, he1, he2, show 2 - 2 = (0 : ℕ) from rfl,
      n06RootJetProduct_zero, ho0] at h
    norm_num at h
    rw [h]
    change _ = -(radialBoundaryJet d 0 0 θ * deriv (n06RootEvenFormula2 v) θ +
      2 * radialBoundaryJet d 0 1 θ * deriv (n06RootEvenFormula1 v) θ +
      radialBoundaryJet d 0 2 θ * deriv β θ) +
        2 * radialBoundaryJet c₀ 0 0 θ * deriv (n06RootOddFormula0 v) θ
    ring
  have ho2 : radialBoundaryJet (extendedRootOddCoefficient G) 0 2 = n06RootOddFormula2 v := by
    funext θ
    have h := P.n06_odd_boundary_recursion_solved hd hc₀ 2 θ
    simp only [n06RootJetProduct_two, he0, he1, he2, show 2 - 1 = (1 : ℕ) from rfl,
      n06RootJetProduct_one, ho0, ho1] at h
    norm_num at h
    rw [h]
    change (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootEvenFormula2 v) θ +
      2 * radialBoundaryJet c₀ 0 1 θ * deriv (n06RootEvenFormula1 v) θ +
      radialBoundaryJet c₀ 0 2 θ * deriv β θ -
        2 * (radialBoundaryJet d 0 0 θ * deriv (n06RootOddFormula1 v) θ +
          radialBoundaryJet d 0 1 θ * deriv (n06RootOddFormula0 v) θ)) / (7 / 2 : ℝ) =
      (2 / 7 : ℝ) * (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootEvenFormula2 v) θ +
        2 * radialBoundaryJet c₀ 0 1 θ * deriv (n06RootEvenFormula1 v) θ +
        radialBoundaryJet c₀ 0 2 θ * deriv β θ -
          2 * (radialBoundaryJet d 0 0 θ * deriv (n06RootOddFormula1 v) θ +
            radialBoundaryJet d 0 1 θ * deriv (n06RootOddFormula0 v) θ))
    ring
  have he4 : radialBoundaryJet (extendedRootEven G) 0 4 = n06RootEvenFormula4 v := by
    funext θ
    have h := P.n06_even_boundary_recursion hd hc₀ 3 θ
    simp only [n06RootJetProduct_three, he0, he1, he2, he3, show 3 - 2 = (1 : ℕ) from rfl,
      n06RootJetProduct_one, ho0, ho1] at h
    norm_num at h
    apply h.trans
    change _ = -(radialBoundaryJet d 0 0 θ * deriv (n06RootEvenFormula3 v) θ +
      3 * radialBoundaryJet d 0 1 θ * deriv (n06RootEvenFormula2 v) θ +
      3 * radialBoundaryJet d 0 2 θ * deriv (n06RootEvenFormula1 v) θ +
      radialBoundaryJet d 0 3 θ * deriv β θ) +
        6 * (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootOddFormula1 v) θ +
          radialBoundaryJet c₀ 0 1 θ * deriv (n06RootOddFormula0 v) θ)
    ring
  have ho3 : radialBoundaryJet (extendedRootOddCoefficient G) 0 3 = n06RootOddFormula3 v := by
    funext θ
    have h := P.n06_odd_boundary_recursion_solved hd hc₀ 3 θ
    simp only [n06RootJetProduct_three, he0, he1, he2, he3, show 3 - 1 = (2 : ℕ) from rfl,
      n06RootJetProduct_two, ho0, ho1, ho2] at h
    norm_num at h
    rw [h]
    change (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootEvenFormula3 v) θ +
      3 * radialBoundaryJet c₀ 0 1 θ * deriv (n06RootEvenFormula2 v) θ +
      3 * radialBoundaryJet c₀ 0 2 θ * deriv (n06RootEvenFormula1 v) θ +
      radialBoundaryJet c₀ 0 3 θ * deriv β θ -
        3 * (radialBoundaryJet d 0 0 θ * deriv (n06RootOddFormula2 v) θ +
          2 * radialBoundaryJet d 0 1 θ * deriv (n06RootOddFormula1 v) θ +
          radialBoundaryJet d 0 2 θ * deriv (n06RootOddFormula0 v) θ)) / (9 / 2 : ℝ) =
      (2 / 9 : ℝ) * (radialBoundaryJet c₀ 0 0 θ * deriv (n06RootEvenFormula3 v) θ +
        3 * radialBoundaryJet c₀ 0 1 θ * deriv (n06RootEvenFormula2 v) θ +
        3 * radialBoundaryJet c₀ 0 2 θ * deriv (n06RootEvenFormula1 v) θ +
        radialBoundaryJet c₀ 0 3 θ * deriv β θ -
          3 * (radialBoundaryJet d 0 0 θ * deriv (n06RootOddFormula2 v) θ +
            2 * radialBoundaryJet d 0 1 θ * deriv (n06RootOddFormula1 v) θ +
            radialBoundaryJet d 0 2 θ * deriv (n06RootOddFormula0 v) θ))
    ring
  exact ⟨he1, he2, he3, he4, ho0, ho1, ho2, ho3⟩

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
