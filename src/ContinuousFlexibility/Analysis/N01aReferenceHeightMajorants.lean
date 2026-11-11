import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Pointwise polynomial majorants for the actual reference equation

The final factor may depend on the evaluation point. Only the coefficient
weight is raised to a larger integer power under products and finite sums.
The differential-equation argument differentiates actual local identities;
it never differentiates the majorizing inequality.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

def N01aPointwiseBound (U : Set ℝ) (E W f : ℝ → ℝ) : Prop :=
  ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, |f x| ≤ C * E x ^ k * W x

section Majorants

variable {U : Set ℝ} {E W f g : ℝ → ℝ}

theorem N01aPointwiseBound.congr (hf : N01aPointwiseBound U E W f)
    (heq : EqOn f g U) : N01aPointwiseBound U E W g := by
  obtain ⟨k, C, hC, hb⟩ := hf
  exact ⟨k, C, hC, fun x hx => by rw [← heq hx]; exact hb x hx⟩

theorem n01aPointwiseBound_of_le (h : ∀ x ∈ U, |f x| ≤ W x) :
    N01aPointwiseBound U E W f :=
  ⟨0, 1, zero_le_one, fun x hx => by simpa using h x hx⟩

theorem n01aPointwiseBound_uniform {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ U, |f x| ≤ C) : N01aPointwiseBound U E (fun _ => 1) f :=
  ⟨0, C, hC, fun x hx => by simpa using h x hx⟩

theorem n01aPointwiseBound_const (c : ℝ) :
    N01aPointwiseBound U E (fun _ => 1) (fun _ => c) :=
  n01aPointwiseBound_uniform (abs_nonneg c) (fun _ _ => le_rfl)

theorem N01aPointwiseBound.add (hf : N01aPointwiseBound U E W f)
    (hg : N01aPointwiseBound U E W g)
    (hE : ∀ x ∈ U, 1 ≤ E x) (hW : ∀ x ∈ U, 0 ≤ W x) :
    N01aPointwiseBound U E W (fun x => f x + g x) := by
  obtain ⟨k, A, hA, ha⟩ := hf
  obtain ⟨l, B, hB, hb⟩ := hg
  refine ⟨k + l, A + B, add_nonneg hA hB, fun x hx => ?_⟩
  have hka : E x ^ k ≤ E x ^ (k + l) := pow_le_pow_right₀ (hE x hx) (by omega)
  have hlb : E x ^ l ≤ E x ^ (k + l) := pow_le_pow_right₀ (hE x hx) (by omega)
  calc
    _ ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ A * E x ^ (k + l) * W x + B * E x ^ (k + l) * W x :=
      add_le_add
        ((ha x hx).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hka hA) (hW x hx)))
        ((hb x hx).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlb hB) (hW x hx)))
    _ = _ := by ring

theorem N01aPointwiseBound.coeff_mul
    (hf : N01aPointwiseBound U E (fun _ => 1) f)
    (hg : N01aPointwiseBound U E W g) (hE : ∀ x ∈ U, 0 ≤ E x) :
    N01aPointwiseBound U E W (fun x => f x * g x) := by
  obtain ⟨k, A, hA, ha⟩ := hf
  obtain ⟨l, B, hB, hb⟩ := hg
  refine ⟨k + l, A * B, mul_nonneg hA hB, fun x hx => ?_⟩
  have ha' : |f x| ≤ A * E x ^ k := by simpa only [mul_one] using ha x hx
  calc
    _ = |f x| * |g x| := abs_mul _ _
    _ ≤ (A * E x ^ k) * (B * E x ^ l * W x) :=
      mul_le_mul ha' (hb x hx) (abs_nonneg _) (mul_nonneg hA (pow_nonneg (hE x hx) _))
    _ = _ := by rw [pow_add]; ring

theorem N01aPointwiseBound.const_mul (hf : N01aPointwiseBound U E W f)
    (hE : ∀ x ∈ U, 0 ≤ E x) (c : ℝ) :
    N01aPointwiseBound U E W (fun x => c * f x) :=
  (n01aPointwiseBound_const c).coeff_mul hf hE

theorem N01aPointwiseBound.mul {V : ℝ → ℝ}
    (hf : N01aPointwiseBound U E V f) (hg : N01aPointwiseBound U E W g)
    (hE : ∀ x ∈ U, 0 ≤ E x) (hV : ∀ x ∈ U, 0 ≤ V x) :
    N01aPointwiseBound U E (fun x => V x * W x) (fun x => f x * g x) := by
  obtain ⟨k, A, hA, ha⟩ := hf
  obtain ⟨l, B, hB, hb⟩ := hg
  refine ⟨k + l, A * B, mul_nonneg hA hB, fun x hx => ?_⟩
  calc
    _ = |f x| * |g x| := abs_mul _ _
    _ ≤ (A * E x ^ k * V x) * (B * E x ^ l * W x) :=
      mul_le_mul (ha x hx) (hb x hx) (abs_nonneg _)
        (mul_nonneg (mul_nonneg hA (pow_nonneg (hE x hx) _)) (hV x hx))
    _ = _ := by rw [pow_add]; ring

theorem n01aPointwiseBound_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hE : ∀ x ∈ U, 1 ≤ E x) (hW : ∀ x ∈ U, 0 ≤ W x)
    (hf : ∀ i ∈ s, N01aPointwiseBound U E W (f i)) :
    N01aPointwiseBound U E W (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact n01aPointwiseBound_of_le (by simpa using hW)
  | @insert i s hi ih =>
      intro hf
      have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).add hsum hE hW

/-- Finitely many jets admit one common polynomial majorant. -/
theorem n01aPointwiseBound_finite {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hE : ∀ x ∈ U, 1 ≤ E x) (hW : ∀ x ∈ U, 0 ≤ W x)
    (hf : ∀ i, N01aPointwiseBound U E W (f i)) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → |f i x| ≤ C * E x ^ k * W x := by
  classical
  choose k C hC hb using hf
  refine ⟨∑ i, k i, ∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i x hx => ?_⟩
  have hk : k i ≤ ∑ j, k j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  have hci : C i ≤ ∑ j, C j := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  exact (hb i x hx).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hci (pow_le_pow_right₀ (hE x hx) hk)
      (pow_nonneg (zero_le_one.trans (hE x hx)) _)
      (Finset.sum_nonneg (fun j _ => hC j))) (hW x hx))

theorem n01aPointwiseBound_iteratedDeriv_mul (k : ℕ)
    (hE : ∀ x ∈ U, 1 ≤ E x) (hW : ∀ x ∈ U, 0 ≤ W x)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x)
    (hfB : ∀ i ≤ k, N01aPointwiseBound U E (fun _ => 1) (iteratedDeriv i f))
    (hgB : ∀ i ≤ k, N01aPointwiseBound U E W (iteratedDeriv i g)) :
    N01aPointwiseBound U E W (iteratedDeriv k (fun x => f x * g x)) := by
  have hsum : N01aPointwiseBound U E W
      (fun x => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x) := by
    apply n01aPointwiseBound_sum _ _ hE hW
    intro i hi
    have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hm := (hfB i hi').coeff_mul (hgB (k - i) (Nat.sub_le _ _))
      (fun x hx => zero_le_one.trans (hE x hx))
    simpa only [mul_assoc] using hm.const_mul
      (fun x hx => zero_le_one.trans (hE x hx)) (k.choose i : ℝ)
  apply hsum.congr
  intro x hx
  exact (iteratedDeriv_mul ((hf x hx).of_le (by simp))
    ((hg x hx).of_le (by simp))).symm

theorem n01aPointwiseBound_iteratedDeriv_weighted_mul {V : ℝ → ℝ} (k : ℕ)
    (hE : ∀ x ∈ U, 1 ≤ E x) (hV : ∀ x ∈ U, 0 ≤ V x) (hW : ∀ x ∈ U, 0 ≤ W x)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x)
    (hfB : ∀ i ≤ k, N01aPointwiseBound U E V (iteratedDeriv i f))
    (hgB : ∀ i ≤ k, N01aPointwiseBound U E W (iteratedDeriv i g)) :
    N01aPointwiseBound U E (fun x => V x * W x)
      (iteratedDeriv k (fun x => f x * g x)) := by
  have hsum : N01aPointwiseBound U E (fun x => V x * W x)
      (fun x => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x) := by
    apply n01aPointwiseBound_sum _ _ hE (fun x hx => mul_nonneg (hV x hx) (hW x hx))
    intro i hi
    have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hm := (hfB i hi').mul (hgB (k - i) (Nat.sub_le _ _))
      (fun x hx => zero_le_one.trans (hE x hx)) hV
    simpa only [mul_assoc] using hm.const_mul
      (fun x hx => zero_le_one.trans (hE x hx)) (k.choose i : ℝ)
  apply hsum.congr
  intro x hx
  exact (iteratedDeriv_mul ((hf x hx).of_le (by simp))
    ((hg x hx).of_le (by simp))).symm

end Majorants

/-- Actual derivatives of a scalar second-order equation retain its
pointwise Cauchy-data factor, at the cost of a polynomial coefficient. -/
theorem n01aPointwiseJets_of_secondOrder {U : Set ℝ} (hU : IsOpen U)
    {E f a b : ℝ → ℝ} (hE : ∀ x ∈ U, 1 ≤ E x)
    (hf : ContDiffOn ℝ ∞ f U) (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (haB : ∀ k, N01aPointwiseBound U E (fun _ => 1) (iteratedDeriv k a))
    (hbB : ∀ k, N01aPointwiseBound U E (fun _ => 1) (iteratedDeriv k b))
    (hode : ∀ x ∈ U, deriv (deriv f) x = a x * f x + b x * deriv f x) :
    ∀ k, N01aPointwiseBound U E (fun x => |f x| + |deriv f x|) (iteratedDeriv k f) := by
  let W : ℝ → ℝ := fun x => |f x| + |deriv f x|
  have hW (x : ℝ) (_ : x ∈ U) : 0 ≤ W x := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hf' : ContDiffOn ℝ ∞ (deriv f) U := hf.deriv_of_isOpen hU (by simp)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          apply n01aPointwiseBound_of_le
          intro x hx
          simpa only [iteratedDeriv_zero] using le_add_of_nonneg_right (abs_nonneg (deriv f x))
      | succ k =>
          cases k with
          | zero =>
              apply n01aPointwiseBound_of_le
              intro x hx
              change |deriv f x| ≤ |f x| + |deriv f x|
              exact le_add_of_nonneg_left (abs_nonneg (f x))
          | succ k =>
              have hfa := n01aPointwiseBound_iteratedDeriv_mul k hE hW
                (fun x hx => (ha x hx).contDiffAt (hU.mem_nhds hx))
                (fun x hx => (hf x hx).contDiffAt (hU.mem_nhds hx))
                (fun i _ => haB i) (fun i hi => ih i (by omega))
              have hfb := n01aPointwiseBound_iteratedDeriv_mul k hE hW
                (fun x hx => (hb x hx).contDiffAt (hU.mem_nhds hx))
                (fun x hx => (hf' x hx).contDiffAt (hU.mem_nhds hx))
                (fun i _ => hbB i) (fun i hi => by
                  simpa only [iteratedDeriv_succ'] using ih (i + 1) (by omega))
              apply (hfa.add hfb hE hW).congr
              intro x hx
              have heq : deriv (deriv f) =ᶠ[𝓝 x]
                  (fun y => a y * f y + b y * deriv f y) := by
                filter_upwards [hU.mem_nhds hx] with y hy
                exact hode y hy
              rw [iteratedDeriv_succ', iteratedDeriv_succ', heq.iteratedDeriv_eq k]
              dsimp only
              exact (iteratedDeriv_fun_add
                (f := fun y => a y * f y) (g := fun y => b y * deriv f y)
                (((ha.mul hf) x hx).contDiffAt (hU.mem_nhds hx) |>.of_le (by simp))
                (((hb.mul hf') x hx).contDiffAt (hU.mem_nhds hx) |>.of_le (by simp))).symm

end ContinuousFlexibility.Statements
