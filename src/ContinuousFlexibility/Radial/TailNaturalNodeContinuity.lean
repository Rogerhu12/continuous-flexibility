module

public import ContinuousFlexibility.Radial.TailNaturalNodeLine

/-!
# Continuous natural node data

The uniform continued-fraction limit gives continuous exact node ratios.
Finite products of these ratios then select the node solution with value
one at the first node, continuously in the product topology on parameters.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

/-- The exact ratio of consecutive positive natural node values. -/
def tailNaturalNodeRatio (b c : ℕ → ℝ)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) (n : ℕ) : ℝ :=
  c n / b (n + 1) *
    tailFractionLimit (fun j => c j ^ 2 / (b j * b (j + 1))) hε n

theorem tailNaturalNodeRatio_pos {b c : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) (n : ℕ) :
    0 < tailNaturalNodeRatio b c hε n := by
  exact mul_pos (div_pos (hc n) (hb (n + 1)))
    (zero_lt_one.trans_le (tailFractionLimit_mem _ hε n).1)

theorem continuous_tailNaturalNodeRatio {P : Type*} [TopologicalSpace P]
    (b c : P → ℕ → ℝ) (hb : ∀ p n, b p n ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n)) (n : ℕ) :
    Continuous (fun p => tailNaturalNodeRatio (b p) (c p) (hε p) n) := by
  have hcoeff (j : ℕ) :
      Continuous (fun p => c p j ^ 2 / (b p j * b p (j + 1))) :=
    ((hccont j).pow 2).div ((hbcont j).mul (hbcont (j + 1)))
      (fun p => mul_ne_zero (hb p j) (hb p (j + 1)))
  exact ((hccont n).div (hbcont (n + 1)) (fun p => hb p (n + 1))).mul
    (continuous_tailFractionLimit _ hε hcoeff n)

/-- A node sequence is fixed by its first value and its consecutive ratios. -/
def tailNodesFromRatio (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => r n * tailNodesFromRatio r n

@[simp] theorem tailNodesFromRatio_zero (r : ℕ → ℝ) : tailNodesFromRatio r 0 = 1 := rfl

theorem tailNodesFromRatio_succ (r : ℕ → ℝ) (n : ℕ) :
    tailNodesFromRatio r (n + 1) = r n * tailNodesFromRatio r n := rfl

theorem tailNodesFromRatio_pos {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    0 < tailNodesFromRatio r n := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hr n) ih

theorem continuous_tailNodesFromRatio {P : Type*} [TopologicalSpace P]
    (r : P → ℕ → ℝ) (hr : ∀ n, Continuous (fun p => r p n)) (n : ℕ) :
    Continuous (fun p => tailNodesFromRatio (r p) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (hr n).mul ih

theorem tailNodesFromRatio_unique {r y : ℕ → ℝ} (hy₀ : y 0 = 1)
    (hy : ∀ n, y (n + 1) = r n * y n) : y = tailNodesFromRatio r := by
  funext n
  induction n with
  | zero => exact hy₀
  | succ n ih => rw [hy n, ih, tailNodesFromRatio_succ]

/-- In the parameter-dependent Jacobi equation, every fixed node of the
entrance-normalized natural sequence is a continuous scalar function. -/
theorem continuous_tailNaturalNodes {P : Type*} [TopologicalSpace P]
    (b c : P → ℕ → ℝ) (hb : ∀ p n, b p n ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n)) (n : ℕ) :
    Continuous (fun p => tailNodesFromRatio
      (tailNaturalNodeRatio (b p) (c p) (hε p)) n) :=
  continuous_tailNodesFromRatio _
    (continuous_tailNaturalNodeRatio b c hb hε hbcont hccont) n

/-- The continuously selected node sequence is the square-summable
sequence already constructed by the natural-node theorem. -/
theorem tailNaturalNodes_properties {b c μ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n) (hμ : ∀ n, 0 < μ n)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8))
    (hr : ∀ n, Real.sqrt (μ (n + 1)) * (c n / b (n + 1)) ≤
      (1 / 4 : ℝ) * Real.sqrt (μ n)) :
    let y := tailNodesFromRatio (tailNaturalNodeRatio b c hε)
    (∀ n, 0 < y n) ∧
      (∀ n, b (n + 1) * y (n + 1) = c n * y n + c (n + 1) * y (n + 2)) ∧
      (∀ n, Real.sqrt (μ (n + 1)) * y (n + 1) ≤
        (1 / 2 : ℝ) * (Real.sqrt (μ n) * y n)) ∧
      Summable (fun n => μ n * y n ^ 2) := by
  obtain ⟨y, hy₀, hypos, hyratio, hyrec, hydecay, hysum⟩ :=
    exists_tailNaturalNodeLine hb hc hμ hε hr
  have hyEq : y = tailNodesFromRatio (tailNaturalNodeRatio b c hε) := by
    apply tailNodesFromRatio_unique hy₀
    intro n
    exact (div_eq_iff (hypos n).ne').mp (hyratio n)
  rw [hyEq] at hypos hyrec hydecay hysum
  exact ⟨hypos, hyrec, hydecay, hysum⟩

/-- Any normalized choice with the exact natural ratios has the same
continuous coordinate values as the explicit finite-product selection. -/
theorem continuous_tailNaturalNodeChoice {P : Type*} [TopologicalSpace P]
    (b c y : P → ℕ → ℝ) (hb : ∀ p n, b p n ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n))
    (hy₀ : ∀ p, y p 0 = 1) (hyne : ∀ p n, y p n ≠ 0)
    (hyratio : ∀ p n, y p (n + 1) / y p n =
      tailNaturalNodeRatio (b p) (c p) (hε p) n) (n : ℕ) :
    Continuous (fun p => y p n) := by
  have hyEq (p : P) : y p =
      tailNodesFromRatio (tailNaturalNodeRatio (b p) (c p) (hε p)) :=
    tailNodesFromRatio_unique (hy₀ p) fun n => (div_eq_iff (hyne p n)).mp (hyratio p n)
  exact (continuous_tailNaturalNodes b c hb hε hbcont hccont n).congr
    (fun p => (congrFun (hyEq p) n).symm)

/-- Undo sign alternation in the Jacobi recurrence to obtain the flux
matching equation for the original physical node values. -/
theorem tailNaturalNodes_signed_recurrence {b c y : ℕ → ℝ}
    (hy : ∀ n, b (n + 1) * y (n + 1) = c n * y n + c (n + 1) * y (n + 2))
    (n : ℕ) :
    -b (n + 1) * ((-1 : ℝ) ^ (n + 1) * y (n + 1)) =
      c n * ((-1 : ℝ) ^ n * y n) + c (n + 1) * ((-1 : ℝ) ^ (n + 2) * y (n + 2)) := by
  have hh := congrArg (fun x : ℝ => (-1 : ℝ) ^ n * x) (hy n)
  simp only [pow_add, pow_one, neg_one_sq, mul_one]
  nlinarith only [hh]

theorem tailNaturalNodes_signed_summable {μ y : ℕ → ℝ}
    (hy : Summable (fun n => μ n * y n ^ 2)) :
    Summable (fun n => μ n * ((-1 : ℝ) ^ n * y n) ^ 2) := by
  have heq : (fun n => μ n * ((-1 : ℝ) ^ n * y n) ^ 2) =
      (fun n => μ n * y n ^ 2) := by
    funext n
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  rw [heq]
  exact hy

/-- If a resistance edge precedes node zero, flux matching determines its
entrance value when the first natural node is normalized to one. -/
def tailNaturalInitialValue (b c : ℕ → ℝ) (cinit : ℝ)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) : ℝ :=
  (-b 0 + c 0 * tailNaturalNodeRatio b c hε 0) / cinit

/-- Uniform diagonal dominance keeps the initial-edge entrance value
strictly negative.  Thus entrance normalization cannot vanish. -/
theorem tailNaturalInitialValue_neg {b c : ℕ → ℝ} {cinit : ℝ}
    (hb : ∀ n, 0 < b n) (hci : 0 < cinit)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) :
    tailNaturalInitialValue b c cinit hε < 0 := by
  let ε (n : ℕ) : ℝ := c n ^ 2 / (b n * b (n + 1))
  let t := tailFractionLimit ε hε
  have ht : t 0 ∈ Icc 1 2 := tailFractionLimit_mem ε hε 0
  have hprod : ε 0 * t 0 ≤ (1 / 4 : ℝ) := by
    have hh := mul_le_mul (hε 0).2 ht.2 (zero_le_one.trans ht.1)
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    norm_num at hh
    exact hh
  have heq : c 0 * tailNaturalNodeRatio b c hε 0 = b 0 * (ε 0 * t 0) := by
    dsimp only [tailNaturalNodeRatio, ε, t]
    field_simp [(hb 0).ne', (hb 1).ne'] <;> ring
  have hbound := mul_le_mul_of_nonneg_left hprod (hb 0).le
  unfold tailNaturalInitialValue
  apply div_neg_of_neg_of_pos _ hci
  rw [heq]
  linarith [hb 0]

theorem continuous_tailNaturalInitialValue {P : Type*} [TopologicalSpace P]
    (b c : P → ℕ → ℝ) (cinit : P → ℝ) (hb : ∀ p n, b p n ≠ 0)
    (hci : ∀ p, cinit p ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n)) (hicont : Continuous cinit) :
    Continuous (fun p => tailNaturalInitialValue (b p) (c p) (cinit p) (hε p)) := by
  exact ((hbcont 0).neg.add ((hccont 0).mul
    (continuous_tailNaturalNodeRatio b c hb hε hbcont hccont 0))).div hicont hci

/-- The value computed from the initial resistance edge satisfies the
actual flux matching equation at node zero. -/
theorem tailNaturalInitialValue_flux {b c : ℕ → ℝ} {cinit dinit dleft : ℝ}
    (hci : cinit ≠ 0) (hb₀ : b 0 = -dinit - dleft)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) :
    -cinit * tailNaturalInitialValue b c cinit hε + dinit =
      -dleft - c 0 * tailNaturalNodeRatio b c hε 0 := by
  unfold tailNaturalInitialValue
  rw [hb₀]
  field_simp [hci]
  ring

/-- The normalized physical slope at the entrance of an initial edge is
continuous as soon as its two flux coefficients and density are. -/
theorem continuous_tailNaturalInitialSlope {P : Type*} [TopologicalSpace P]
    (b c : P → ℕ → ℝ) (cinit dinit pinit : P → ℝ)
    (hb : ∀ p n, 0 < b p n) (hci : ∀ p, 0 < cinit p) (hpi : ∀ p, pinit p ≠ 0)
    (hε : ∀ p n, c p n ^ 2 / (b p n * b p (n + 1)) ∈ Icc 0 (1 / 8))
    (hbcont : ∀ n, Continuous (fun p => b p n))
    (hccont : ∀ n, Continuous (fun p => c p n))
    (hicont : Continuous cinit) (hdcont : Continuous dinit) (hpcont : Continuous pinit) :
    Continuous (fun p =>
      (cinit p - dinit p * tailNaturalInitialValue (b p) (c p) (cinit p) (hε p)) /
        (pinit p * tailNaturalInitialValue (b p) (c p) (cinit p) (hε p))) := by
  have hA := continuous_tailNaturalInitialValue b c cinit
    (fun p n => (hb p n).ne') (fun p => (hci p).ne') hε hbcont hccont hicont
  exact (hicont.sub (hdcont.mul hA)).div (hpcont.mul hA)
    (fun p => mul_ne_zero (hpi p) (tailNaturalInitialValue_neg (hb p) (hci p) (hε p)).ne)

end ContinuousFlexibility.Radial
