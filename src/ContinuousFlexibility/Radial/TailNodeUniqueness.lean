module

public import ContinuousFlexibility.Radial.TailNaturalNodeLine
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# Uniqueness of the square-summable natural node line

The Casoratian of two solutions of the same three-term recurrence is
constant. A bound on the coupling in mass-normalized coordinates makes
that constant vanish when both normalized solutions tend to zero.
Consequently every square-summable solution is proportional to a
nonvanishing natural solution. The same result applies after any node,
which is the form needed for columns of the inverse matrix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter
open scoped Topology

/-- The conserved determinant of two node solutions. -/
def tailNodeCasoratian (c y z : ℕ → ℝ) (n : ℕ) : ℝ :=
  c n * (y n * z (n + 1) - y (n + 1) * z n)

theorem tailNodeCasoratian_succ {b c y z : ℕ → ℝ}
    (hy : ∀ n, b (n + 1) * y (n + 1) =
      c n * y n + c (n + 1) * y (n + 2))
    (hz : ∀ n, b (n + 1) * z (n + 1) =
      c n * z n + c (n + 1) * z (n + 2)) (n : ℕ) :
    tailNodeCasoratian c y z (n + 1) = tailNodeCasoratian c y z n := by
  simp only [tailNodeCasoratian, Nat.add_assoc]
  linear_combination z (n + 1) * hy n - y (n + 1) * hz n

theorem tailNodeCasoratian_eq {b c y z : ℕ → ℝ}
    (hy : ∀ n, b (n + 1) * y (n + 1) =
      c n * y n + c (n + 1) * y (n + 2))
    (hz : ∀ n, b (n + 1) * z (n + 1) =
      c n * z n + c (n + 1) * z (n + 2)) (n : ℕ) :
    tailNodeCasoratian c y z n = tailNodeCasoratian c y z 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (tailNodeCasoratian_succ hy hz n).trans ih

/-- Bounded normalized coupling and vanishing normalized coordinates force
the Casoratian to tend to zero. The weight can be any positive sequence. -/
theorem tendsto_tailNodeCasoratian_zero {c y z w : ℕ → ℝ} {B : ℝ}
    (hw : ∀ n, 0 < w n)
    (hbound : ∀ n, |c n| ≤ B * (w n * w (n + 1)))
    (hy : Tendsto (fun n => w n * y n) atTop (𝓝 0))
    (hz : Tendsto (fun n => w n * z n) atTop (𝓝 0)) :
    Tendsto (tailNodeCasoratian c y z) atTop (𝓝 0) := by
  let Y : ℕ → ℝ := fun n => w n * y n
  let Z : ℕ → ℝ := fun n => w n * z n
  have hY : Tendsto Y atTop (𝓝 0) := hy
  have hZ : Tendsto Z atTop (𝓝 0) := hz
  have hYnext : Tendsto (fun n => Y (n + 1)) atTop (𝓝 0) :=
    hY.comp (tendsto_add_atTop_nat 1)
  have hZnext : Tendsto (fun n => Z (n + 1)) atTop (𝓝 0) :=
    hZ.comp (tendsto_add_atTop_nat 1)
  have hdet : Tendsto (fun n => Y n * Z (n + 1) - Y (n + 1) * Z n)
      atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using (hY.mul hZnext).sub (hYnext.mul hZ)
  have hmajorant : Tendsto
      (fun n => B * |Y n * Z (n + 1) - Y (n + 1) * Z n|) atTop (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using hdet.abs.const_mul B
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hmajorant
  have hfactor : Y n * Z (n + 1) - Y (n + 1) * Z n =
      (w n * w (n + 1)) * (y n * z (n + 1) - y (n + 1) * z n) := by
    dsimp only [Y, Z]
    ring
  rw [tailNodeCasoratian, abs_mul, hfactor, abs_mul,
    abs_of_pos (mul_pos (hw n) (hw (n + 1)))]
  calc
    |c n| * |y n * z (n + 1) - y (n + 1) * z n| ≤
        (B * (w n * w (n + 1))) *
          |y n * z (n + 1) - y (n + 1) * z n| :=
      mul_le_mul_of_nonneg_right (hbound n) (abs_nonneg _)
    _ = _ := by ring

/-- A nonvanishing solution spans all solutions whose weighted coordinates
tend to zero. The normalized coupling is only required to be bounded. -/
theorem tailNodeLine_eq_mul_of_tendsto {b c y z w : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hc : ∀ n, c n ≠ 0)
    (hbound : ∃ B : ℝ, ∀ n, |c n| ≤ B * (w n * w (n + 1)))
    (hyrec : ∀ n, b (n + 1) * y (n + 1) =
      c n * y n + c (n + 1) * y (n + 2))
    (hzrec : ∀ n, b (n + 1) * z (n + 1) =
      c n * z n + c (n + 1) * z (n + 2))
    (hyne : ∀ n, y n ≠ 0)
    (hy : Tendsto (fun n => w n * y n) atTop (𝓝 0))
    (hz : Tendsto (fun n => w n * z n) atTop (𝓝 0)) :
    ∀ n, z n = (z 0 / y 0) * y n := by
  obtain ⟨B, hB⟩ := hbound
  have hlim := tendsto_tailNodeCasoratian_zero hw hB hy hz
  have hconst : tailNodeCasoratian c y z = fun _ => tailNodeCasoratian c y z 0 :=
    funext (tailNodeCasoratian_eq hyrec hzrec)
  rw [hconst] at hlim
  have hzero₀ : tailNodeCasoratian c y z 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  have hdet (n : ℕ) : y n * z (n + 1) = y (n + 1) * z n := by
    have hzero := (tailNodeCasoratian_eq hyrec hzrec n).trans hzero₀
    change c n * (y n * z (n + 1) - y (n + 1) * z n) = 0 at hzero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (hc n))
  intro n
  induction n with
  | zero => exact (div_mul_cancel₀ (z 0) (hyne 0)).symm
  | succ n ih =>
    apply mul_left_cancel₀ (hyne n)
    calc
      y n * z (n + 1) = y (n + 1) * z n := hdet n
      _ = y n * ((z 0 / y 0) * y (n + 1)) := by rw [ih]; ring

/-- The same uniqueness result on the right tail starting at any node.
The recurrence at the starting node itself is not required. -/
theorem tailNodeLine_eq_mul_from_of_tendsto {b c y z w : ℕ → ℝ} (m : ℕ)
    (hw : ∀ n, m ≤ n → 0 < w n)
    (hc : ∀ n, m ≤ n → c n ≠ 0)
    (hbound : ∃ B : ℝ, ∀ n, m ≤ n → |c n| ≤ B * (w n * w (n + 1)))
    (hyrec : ∀ n, m ≤ n → b (n + 1) * y (n + 1) =
      c n * y n + c (n + 1) * y (n + 2))
    (hzrec : ∀ n, m ≤ n → b (n + 1) * z (n + 1) =
      c n * z n + c (n + 1) * z (n + 2))
    (hyne : ∀ n, m ≤ n → y n ≠ 0)
    (hy : Tendsto (fun n => w n * y n) atTop (𝓝 0))
    (hz : Tendsto (fun n => w n * z n) atTop (𝓝 0)) :
    ∀ n, m ≤ n → z n = (z m / y m) * y n := by
  have hshift : Tendsto (fun n : ℕ => m + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat m
  obtain ⟨B, hB⟩ := hbound
  have h := tailNodeLine_eq_mul_of_tendsto
    (b := fun n => b (m + n)) (c := fun n => c (m + n))
    (y := fun n => y (m + n)) (z := fun n => z (m + n))
    (w := fun n => w (m + n))
    (fun n => hw (m + n) (Nat.le_add_right m n))
    (fun n => hc (m + n) (Nat.le_add_right m n))
    ⟨B, fun n => by
      simpa only [Nat.add_assoc] using hB (m + n) (Nat.le_add_right m n)⟩
    (fun n => by
      simpa only [Nat.add_assoc] using hyrec (m + n) (Nat.le_add_right m n))
    (fun n => by
      simpa only [Nat.add_assoc] using hzrec (m + n) (Nat.le_add_right m n))
    (fun n => hyne (m + n) (Nat.le_add_right m n))
    (hy.comp hshift) (hz.comp hshift)
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_zero] using h k

/-- Square summability of the mass-weighted node values gives the vanishing
coordinates needed by the Casoratian argument. -/
theorem tendsto_tailWeightedNode_zero {μ u : ℕ → ℝ}
    (hμ : ∀ n, 0 ≤ μ n) (hu : Summable (fun n => μ n * u n ^ 2)) :
    Tendsto (fun n => Real.sqrt (μ n) * u n) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => (Real.sqrt (μ n) * u n) ^ 2) atTop (𝓝 0) := by
    convert hu.tendsto_atTop_zero using 1
    funext n
    rw [mul_pow, Real.sq_sqrt (hμ n)]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq

/-- Weighted square-summable solutions are proportional on every right tail.
This applies in particular to an inverse-matrix column to the right of its
source, where the column satisfies the homogeneous node recurrence. -/
theorem tailNodeLine_eq_mul_from_of_summable {b c μ y z : ℕ → ℝ} (m : ℕ)
    (hμ : ∀ n, 0 < μ n)
    (hc : ∀ n, m ≤ n → c n ≠ 0)
    (hbound : ∃ B : ℝ, ∀ n, m ≤ n →
      |c n| ≤ B * (Real.sqrt (μ n) * Real.sqrt (μ (n + 1))))
    (hyrec : ∀ n, m ≤ n → b (n + 1) * y (n + 1) =
      c n * y n + c (n + 1) * y (n + 2))
    (hzrec : ∀ n, m ≤ n → b (n + 1) * z (n + 1) =
      c n * z n + c (n + 1) * z (n + 2))
    (hyne : ∀ n, m ≤ n → y n ≠ 0)
    (hy : Summable (fun n => μ n * y n ^ 2))
    (hz : Summable (fun n => μ n * z n ^ 2)) :
    ∀ n, m ≤ n → z n = (z m / y m) * y n :=
  tailNodeLine_eq_mul_from_of_tendsto m
    (fun n _ => Real.sqrt_pos.mpr (hμ n)) hc hbound hyrec hzrec hyne
    (tendsto_tailWeightedNode_zero (fun n => (hμ n).le) hy)
    (tendsto_tailWeightedNode_zero (fun n => (hμ n).le) hz)

theorem tailNodeLine_eq_mul_of_summable {b c μ y z : ℕ → ℝ}
    (hμ : ∀ n, 0 < μ n) (hc : ∀ n, c n ≠ 0)
    (hbound : ∃ B : ℝ, ∀ n,
      |c n| ≤ B * (Real.sqrt (μ n) * Real.sqrt (μ (n + 1))))
    (hyrec : ∀ n, b (n + 1) * y (n + 1) =
      c n * y n + c (n + 1) * y (n + 2))
    (hzrec : ∀ n, b (n + 1) * z (n + 1) =
      c n * z n + c (n + 1) * z (n + 2))
    (hyne : ∀ n, y n ≠ 0)
    (hy : Summable (fun n => μ n * y n ^ 2))
    (hz : Summable (fun n => μ n * z n ^ 2)) :
    ∀ n, z n = (z 0 / y 0) * y n := by
  obtain ⟨B, hB⟩ := hbound
  exact fun n => tailNodeLine_eq_mul_from_of_summable 0 hμ
    (fun n _ => hc n) ⟨B, fun n _ => hB n⟩
    (fun n _ => hyrec n) (fun n _ => hzrec n) (fun n _ => hyne n)
    hy hz n (Nat.zero_le n)

end ContinuousFlexibility.Radial
