module

public import ContinuousFlexibility.Radial.DeepTailPhysicalWeights
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual derivative bounds for the physical flux system

Fixed coefficient powers are stable under finite sums and products.
Leibniz's rule then propagates a value bound through a genuine first-order
two-component system, with one scalar constant for each derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff BigOperators

/-- A bound on the actual values on the specified cells.  `E` is a
coefficient weight and `H` is the decay weight. -/
def PhysicalCellBound (cells : ℕ → Set ℝ) (E H : ℕ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n x, x ∈ cells n → |f x| ≤ C * E n ^ C * H n

section CellBounds

variable {cells : ℕ → Set ℝ} {E H : ℕ → ℝ}
  {f g : ℝ → ℝ}

theorem PhysicalCellBound.congr (hf : PhysicalCellBound cells E H f)
    (hfg : ∀ n x, x ∈ cells n → f x = g x) : PhysicalCellBound cells E H g := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, fun n x hx => by rw [← hfg n x hx]; exact hb n x hx⟩

theorem physicalCellBound_zero (hE : ∀ n, 1 ≤ E n) (hH : ∀ n, 0 ≤ H n) :
    PhysicalCellBound cells E H (fun _ => 0) := by
  refine ⟨1, zero_lt_one, fun n x hx => ?_⟩
  simp only [abs_zero, rpow_one, one_mul]
  exact mul_nonneg (zero_le_one.trans (hE n)) (hH n)

theorem physicalCellBound_const (hE : ∀ n, 1 ≤ E n) (c : ℝ) :
    PhysicalCellBound cells E (fun _ => 1) (fun _ => c) := by
  let C : ℝ := |c| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun n x hx => ?_⟩
  simp only [mul_one]
  exact (show |c| ≤ C by dsimp [C]; linarith).trans
    (le_mul_of_one_le_right hC.le (one_le_rpow (hE n) hC.le))

theorem PhysicalCellBound.add (hf : PhysicalCellBound cells E H f)
    (hE : ∀ n, 1 ≤ E n) (hH : ∀ n, 0 ≤ H n)
    (hg : PhysicalCellBound cells E H g) :
    PhysicalCellBound cells E H (fun x => f x + g x) := by
  obtain ⟨A, hA, hfa⟩ := hf
  obtain ⟨B, hB, hgb⟩ := hg
  let C : ℝ := A + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hABC : A + B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n x hx => ?_⟩
  have ha : |f x| ≤ A * E n ^ C * H n :=
    (hfa n x hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le (hE n) hAC) hA.le) (hH n))
  have hb : |g x| ≤ B * E n ^ C * H n :=
    (hgb n x hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le (hE n) hBC) hB.le) (hH n))
  calc
    _ ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ A * E n ^ C * H n + B * E n ^ C * H n := add_le_add ha hb
    _ = (A + B) * E n ^ C * H n := by ring
    _ ≤ C * E n ^ C * H n := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hABC (rpow_nonneg (zero_le_one.trans (hE n)) _)) (hH n)

/-- A coefficient bound times a decaying value bound preserves the decay
weight. Only the allowed coefficient power increases. -/
theorem PhysicalCellBound.coeff_mul
    (hf : PhysicalCellBound cells E (fun _ => 1) f)
    (hE : ∀ n, 1 ≤ E n) (hH : ∀ n, 0 ≤ H n)
    (hg : PhysicalCellBound cells E H g) :
    PhysicalCellBound cells E H (fun x => f x * g x) := by
  obtain ⟨A, hA, hfa⟩ := hf
  obtain ⟨B, hB, hgb⟩ := hg
  let C : ℝ := A + B + A * B + 1
  have hAB : 0 < A * B := mul_pos hA hB
  have hC : 0 < C := by dsimp [C]; positivity
  have hprod : A * B ≤ C := by dsimp [C]; linarith
  have hsum : A + B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n x hx => ?_⟩
  have ha : |f x| ≤ A * E n ^ A := by simpa only [mul_one] using hfa n x hx
  calc
    _ = |f x| * |g x| := abs_mul _ _
    _ ≤ (A * E n ^ A) * (B * E n ^ B * H n) :=
      mul_le_mul ha (hgb n x hx) (abs_nonneg _)
        (mul_nonneg hA.le (rpow_nonneg (zero_le_one.trans (hE n)) _))
    _ = (A * B) * E n ^ (A + B) * H n := by
      rw [rpow_add (zero_lt_one.trans_le (hE n))]
      ring
    _ ≤ C * E n ^ C * H n := mul_le_mul_of_nonneg_right
      (mul_le_mul hprod (rpow_le_rpow_of_exponent_le (hE n) hsum)
        (rpow_nonneg (zero_le_one.trans (hE n)) _) hC.le) (hH n)

theorem PhysicalCellBound.const_mul (hf : PhysicalCellBound cells E H f)
    (hE : ∀ n, 1 ≤ E n) (hH : ∀ n, 0 ≤ H n) (c : ℝ) :
    PhysicalCellBound cells E H (fun x => c * f x) :=
  (physicalCellBound_const hE c).coeff_mul hE hH hf

theorem physicalCellBound_sum {ι : Type*} (hE : ∀ n, 1 ≤ E n)
    (hH : ∀ n, 0 ≤ H n) (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, PhysicalCellBound cells E H (f i)) :
    PhysicalCellBound cells E H (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      simpa only [Finset.sum_empty] using (physicalCellBound_zero (cells := cells) hE hH)
  | @insert i s hi ih =>
      intro hf
      have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).add hE hH hs

/-- The actual Leibniz formula gives the derivative bound from the finitely
many coefficient and solution derivatives that occur in that formula. -/
theorem physicalCellBound_iteratedDeriv_mul (hE : ∀ n, 1 ≤ E n)
    (hH : ∀ n, 0 ≤ H n) (k : ℕ)
    (hf : ∀ n x, x ∈ cells n → ContDiffAt ℝ ∞ f x)
    (hg : ∀ n x, x ∈ cells n → ContDiffAt ℝ ∞ g x)
    (hfB : ∀ i ≤ k, PhysicalCellBound cells E (fun _ => 1) (iteratedDeriv i f))
    (hgB : ∀ i ≤ k, PhysicalCellBound cells E H (iteratedDeriv i g)) :
    PhysicalCellBound cells E H (iteratedDeriv k (fun x => f x * g x)) := by
  have hsum : PhysicalCellBound cells E H
      (fun x => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x) := by
    apply physicalCellBound_sum hE hH
    intro i hi
    have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hmul := (hfB i hi').coeff_mul hE hH (hgB (k - i) (Nat.sub_le _ _))
    simpa only [mul_assoc] using hmul.const_mul hE hH (k.choose i : ℝ)
  apply hsum.congr
  intro n x hx
  exact (iteratedDeriv_mul ((hf n x hx).of_le (by simp))
    ((hg n x hx).of_le (by simp))).symm

end CellBounds

/-- The physical flux equations propagate the same decay weight to every
actual derivative. The open cells allow differentiation of the equations
as genuine local identities. -/
theorem physicalJets_of_firstOrderSystem
    {cells : ℕ → Set ℝ} {E H : ℕ → ℝ} {f g a b : ℝ → ℝ}
    (hopen : ∀ n, IsOpen (cells n))
    (hE : ∀ n, 1 ≤ E n) (hH : ∀ n, 0 ≤ H n)
    (hf : ∀ n x, x ∈ cells n → ContDiffAt ℝ ∞ f x)
    (hg : ∀ n x, x ∈ cells n → ContDiffAt ℝ ∞ g x)
    (ha : ∀ n x, x ∈ cells n → ContDiffAt ℝ ∞ a x)
    (hb : ∀ n x, x ∈ cells n → ContDiffAt ℝ ∞ b x)
    (haB : ∀ k, PhysicalCellBound cells E (fun _ => 1) (iteratedDeriv k a))
    (hbB : ∀ k, PhysicalCellBound cells E (fun _ => 1) (iteratedDeriv k b))
    (hf0 : PhysicalCellBound cells E H f) (hg0 : PhysicalCellBound cells E H g)
    (hdf : ∀ n x, x ∈ cells n → deriv f x = a x * g x)
    (hdg : ∀ n x, x ∈ cells n → deriv g x = b x * f x) :
    ∀ k, PhysicalCellBound cells E H (iteratedDeriv k f) ∧
      PhysicalCellBound cells E H (iteratedDeriv k g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => simpa only [iteratedDeriv_zero] using And.intro hf0 hg0
      | succ k =>
          have hfirst := physicalCellBound_iteratedDeriv_mul hE hH k ha hg
            (fun i hi => haB i) (fun i hi => (ih i (Nat.lt_succ_of_le hi)).2)
          have hsecond := physicalCellBound_iteratedDeriv_mul hE hH k hb hf
            (fun i hi => hbB i) (fun i hi => (ih i (Nat.lt_succ_of_le hi)).1)
          constructor
          · apply hfirst.congr
            intro n x hx
            rw [iteratedDeriv_succ']
            have heq : deriv f =ᶠ[𝓝 x] (fun y => a y * g y) := by
              filter_upwards [(hopen n).mem_nhds hx] with y hy
              exact hdf n y hy
            exact (heq.iteratedDeriv_eq k).symm
          · apply hsecond.congr
            intro n x hx
            rw [iteratedDeriv_succ']
            have heq : deriv g =ᶠ[𝓝 x] (fun y => b y * f y) := by
              filter_upwards [(hopen n).mem_nhds hx] with y hy
              exact hdg n y hy
            exact (heq.iteratedDeriv_eq k).symm

end ContinuousFlexibility.Radial
