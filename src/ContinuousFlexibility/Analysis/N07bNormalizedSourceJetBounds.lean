import ContinuousFlexibility.Analysis.N07bFiniteJetAlgebra
import ContinuousFlexibility.Analysis.N07bAngularChainExpansion

/-!
# Finite jets of a three-branch scalar coefficient recursion

Only the four primitive fields have assumed jet bounds. The estimate for
every recursively generated coefficient is proved by induction, retaining
the full invariant `j + n <= b`. The functions and derivatives are actual
functions on an open set; equalities on that set are differentiated there.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n07bSourceChainJetConstant (b : ℕ) : ℝ := 3 * n07bFiniteJetProductConstant b

theorem one_le_n07bSourceChainJetConstant (b : ℕ) : 1 ≤ n07bSourceChainJetConstant b := by
  have h := one_le_n07bFiniteJetProductConstant b
  unfold n07bSourceChainJetConstant
  linarith

/-- Bounds on only the initial coefficient, the two direction fields,
and the drift control every actual recursive coefficient. -/
theorem n07b_threeBranch_jets_le
    {U : Set PolarPoint} (hU : IsOpen U)
    {a : (j : ℕ) → n07bAngularChainIndex j → PolarPoint → ℝ}
    {v₁ v₂ q : PolarPoint → ℝ}
    (ha : ∀ j i, ContDiffOn ℝ ∞ (a j i) U)
    (hv₁ : ContDiffOn ℝ ∞ v₁ U) (hv₂ : ContDiffOn ℝ ∞ v₂ U) (hq : ContDiffOn ℝ ∞ q U)
    (hstay : ∀ j i, EqOn (a (j + 1) (i, 0))
      (fun y => v₁ y * radialPartial (a j i) y + v₂ y * angularPartial (a j i) y + q y * a j i y) U)
    (hradial : ∀ j i, EqOn (a (j + 1) (i, 1)) (fun y => v₁ y * a j i y) U)
    (hangular : ∀ j i, EqOn (a (j + 1) (i, 2)) (fun y => v₂ y * a j i y) U)
    {x : PolarPoint} (hx : x ∈ U) (b : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (a 0 ()) x‖ ≤ R)
    (hv₁jet : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n v₁ x‖ ≤ R)
    (hv₂jet : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n v₂ x‖ ≤ R)
    (hqjet : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n q x‖ ≤ R) :
    ∀ j (i : n07bAngularChainIndex j) (n : ℕ), j + n ≤ b →
      ‖iteratedFDeriv ℝ n (a j i) x‖ ≤ n07bSourceChainJetConstant b ^ j * R ^ (j + 1) := by
  have hP : 0 ≤ n07bFiniteJetProductConstant b := zero_le_one.trans (one_le_n07bFiniteJetProductConstant b)
  have hK : 0 ≤ n07bSourceChainJetConstant b := zero_le_one.trans (one_le_n07bSourceChainJetConstant b)
  intro j
  induction j with
  | zero =>
      intro i n hn
      cases i
      simpa only [zero_add, pow_zero, pow_one, one_mul] using
        hinit n (by simpa only [zero_add] using hn)
  | succ j ih =>
      rintro ⟨i, k⟩ n hn
      have hnB : n ≤ b := by omega
      let D : ℝ := n07bSourceChainJetConstant b ^ j * R ^ (j + 1)
      let L : ℝ := n07bFiniteJetProductConstant b * R * D
      have hD : 0 ≤ D := mul_nonneg (pow_nonneg hK _) (pow_nonneg hR _)
      have hL : 0 ≤ L := mul_nonneg (mul_nonneg hP hR) hD
      have hajet (t : ℕ) (ht : t ≤ n + 1) : ‖iteratedFDeriv ℝ t (a j i) x‖ ≤ D :=
        ih i t (by omega)
      have hrad : ContDiffOn ℝ ∞ (radialPartial (a j i)) U := by
        intro y hy
        exact (contDiffAt_radialPartial ((ha j i).contDiffAt (hU.mem_nhds hy)) (by simp)).contDiffWithinAt
      have hang : ContDiffOn ℝ ∞ (angularPartial (a j i)) U := by
        intro y hy
        exact (contDiffAt_angularPartial ((ha j i).contDiffAt (hU.mem_nhds hy)) (by simp)).contDiffWithinAt
      have hmul {v g : PolarPoint → ℝ}
          (hv : ContDiffOn ℝ ∞ v U) (hg : ContDiffOn ℝ ∞ g U)
          (hvj : ∀ t : ℕ, t ≤ n → ‖iteratedFDeriv ℝ t v x‖ ≤ R)
          (hgj : ∀ t : ℕ, t ≤ n → ‖iteratedFDeriv ℝ t g x‖ ≤ D) :
          ‖iteratedFDeriv ℝ n (fun y => v y * g y) x‖ ≤ L :=
        n07b_norm_jet_mul_le hU hv hg hx hR hD hvj hgj hnB
      let g₁ : PolarPoint → ℝ := fun y => v₁ y * radialPartial (a j i) y
      let g₂ : PolarPoint → ℝ := fun y => v₂ y * angularPartial (a j i) y
      let g₃ : PolarPoint → ℝ := fun y => q y * a j i y
      have hg₁ : ContDiffOn ℝ ∞ g₁ U := hv₁.mul hrad
      have hg₂ : ContDiffOn ℝ ∞ g₂ U := hv₂.mul hang
      have hg₃ : ContDiffOn ℝ ∞ g₃ U := hq.mul (ha j i)
      have h₁ : ‖iteratedFDeriv ℝ n g₁ x‖ ≤ L := hmul hv₁ hrad
        (fun t ht => hv₁jet t (ht.trans hnB))
        (fun t ht => (n07b_norm_jet_radialPartial_le hU (ha j i) hx t).trans
          (hajet (t + 1) (by omega)))
      have h₂ : ‖iteratedFDeriv ℝ n g₂ x‖ ≤ L := hmul hv₂ hang
        (fun t ht => hv₂jet t (ht.trans hnB))
        (fun t ht => (n07b_norm_jet_angularPartial_le hU (ha j i) hx t).trans
          (hajet (t + 1) (by omega)))
      have h₃ : ‖iteratedFDeriv ℝ n g₃ x‖ ≤ L := hmul hq (ha j i)
        (fun t ht => hqjet t (ht.trans hnB)) (fun t ht => hajet t (by omega))
      have hstep : 3 * L = n07bSourceChainJetConstant b ^ (j + 1) * R ^ (j + 1 + 1) := by
        dsimp only [L, D]
        simp only [pow_succ]
        unfold n07bSourceChainJetConstant
        ring
      fin_cases k
      · change ‖iteratedFDeriv ℝ n (a (j + 1) (i, 0)) x‖ ≤
          n07bSourceChainJetConstant b ^ (j + 1) * R ^ (j + 1 + 1)
        have heq : a (j + 1) (i, 0) =ᶠ[𝓝 x] (fun y => g₁ y + g₂ y + g₃ y) :=
          Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hstay j i hy)
        rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
        calc
          _ ≤ (‖iteratedFDeriv ℝ n g₁ x‖ + ‖iteratedFDeriv ℝ n g₂ x‖) +
              ‖iteratedFDeriv ℝ n g₃ x‖ :=
            (n07b_norm_jet_add_le hU (hg₁.add hg₂) hg₃ hx n).trans
              (add_le_add (n07b_norm_jet_add_le hU hg₁ hg₂ hx n) le_rfl)
          _ ≤ L + L + L := add_le_add (add_le_add h₁ h₂) h₃
          _ = 3 * L := by ring
          _ = _ := hstep
      · change ‖iteratedFDeriv ℝ n (a (j + 1) (i, 1)) x‖ ≤
          n07bSourceChainJetConstant b ^ (j + 1) * R ^ (j + 1 + 1)
        have heq : a (j + 1) (i, 1) =ᶠ[𝓝 x] (fun y => v₁ y * a j i y) :=
          Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hradial j i hy)
        rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
        calc
          _ ≤ L := hmul hv₁ (ha j i) (fun t ht => hv₁jet t (ht.trans hnB))
            (fun t ht => hajet t (by omega))
          _ ≤ 3 * L := by linarith
          _ = _ := hstep
      · change ‖iteratedFDeriv ℝ n (a (j + 1) (i, 2)) x‖ ≤
          n07bSourceChainJetConstant b ^ (j + 1) * R ^ (j + 1 + 1)
        have heq : a (j + 1) (i, 2) =ᶠ[𝓝 x] (fun y => v₂ y * a j i y) :=
          Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hangular j i hy)
        rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
        calc
          _ ≤ L := hmul hv₂ (ha j i) (fun t ht => hv₂jet t (ht.trans hnB))
            (fun t ht => hajet t (by omega))
          _ ≤ 3 * L := by linarith
          _ = _ := hstep

/-- A single finite-order constant bounds all path values once the common
primitive bound is at least one. -/
theorem n07b_threeBranch_value_le
    {U : Set PolarPoint} (hU : IsOpen U)
    {a : (j : ℕ) → n07bAngularChainIndex j → PolarPoint → ℝ}
    {v₁ v₂ q : PolarPoint → ℝ}
    (ha : ∀ j i, ContDiffOn ℝ ∞ (a j i) U)
    (hv₁ : ContDiffOn ℝ ∞ v₁ U) (hv₂ : ContDiffOn ℝ ∞ v₂ U) (hq : ContDiffOn ℝ ∞ q U)
    (hstay : ∀ j i, EqOn (a (j + 1) (i, 0))
      (fun y => v₁ y * radialPartial (a j i) y + v₂ y * angularPartial (a j i) y + q y * a j i y) U)
    (hradial : ∀ j i, EqOn (a (j + 1) (i, 1)) (fun y => v₁ y * a j i y) U)
    (hangular : ∀ j i, EqOn (a (j + 1) (i, 2)) (fun y => v₂ y * a j i y) U)
    {x : PolarPoint} (hx : x ∈ U) (b : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (a 0 ()) x‖ ≤ R)
    (hv₁jet : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n v₁ x‖ ≤ R)
    (hv₂jet : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n v₂ x‖ ≤ R)
    (hqjet : ∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n q x‖ ≤ R)
    {j : ℕ} (hj : j ≤ b) (i : n07bAngularChainIndex j) :
    |a j i x| ≤ n07bSourceChainJetConstant b ^ b * R ^ (b + 1) := by
  have hR0 := zero_le_one.trans hR
  have hK := one_le_n07bSourceChainJetConstant b
  have h := n07b_threeBranch_jets_le hU ha hv₁ hv₂ hq hstay hradial hangular hx b hR0
    hinit hv₁jet hv₂jet hqjet j i 0 (by simpa using hj)
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul
    (pow_le_pow_right₀ hK hj) (pow_le_pow_right₀ hR (Nat.add_le_add_right hj 1))
    (pow_nonneg hR0 _) (pow_nonneg (zero_le_one.trans hK) _))

end ContinuousFlexibility.Analysis
