module

public import ContinuousFlexibility.Radial.MatchedWeightBounds
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Schur sums with finitely many cells at each level

The cell enumeration need not agree with the attenuation level. A uniform
bound on the cardinality of each level fiber gives the extra multiplicity
factor in the row and column estimates. Both finiteness and the cardinality
bound are explicit hypotheses; they are not inferred from
`IsAccumulatingProfile`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- A finite sum over cells is bounded by the corresponding level sum,
with the uniform fiber multiplicity. -/
theorem matched_finset_sum_comp_of_bounded_fibers {κ : Type*}
    (level : κ → ℕ) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | level m = n})
    (hcard : ∀ n, Set.ncard {m | level m = n} ≤ N)
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (s : Finset κ) :
    (∑ m ∈ s, g (level m)) ≤ (N : ℝ) * ∑ n ∈ s.image level, g n := by
  classical
  have hc : ∀ n, (s.filter fun m => level m = n).card ≤ N := by
    intro n
    have hsub : (↑(s.filter fun m => level m = n) : Set κ) ⊆
        {m | level m = n} := by
      intro m hm
      exact (Finset.mem_filter.mp hm).2
    have h := (Set.ncard_le_ncard hsub (hfibers n)).trans (hcard n)
    simpa only [Set.ncard_coe_finset] using h
  calc
    (∑ m ∈ s, g (level m)) =
        ∑ n ∈ s.image level, ((s.filter fun m => level m = n).card : ℝ) * g n := by
      simpa only [nsmul_eq_mul] using (Finset.sum_comp (s := s) g level)
    _ ≤ ∑ n ∈ s.image level, (N : ℝ) * g n := by
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hc n)) (hg n)
    _ = (N : ℝ) * ∑ n ∈ s.image level, g n := by rw [Finset.mul_sum]

/-- Repetition along uniformly bounded finite fibers preserves summability
of a nonnegative series. -/
theorem matched_summable_comp_of_bounded_fibers {κ : Type*}
    (level : κ → ℕ) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | level m = n})
    (hcard : ∀ n, Set.ncard {m | level m = n} ≤ N)
    (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    Summable (fun m => g (level m)) ∧
      ∑' m, g (level m) ≤ (N : ℝ) * ∑' n, g n := by
  classical
  have hpartial : ∀ s : Finset κ,
      (∑ m ∈ s, g (level m)) ≤ (N : ℝ) * ∑' n, g n := by
    intro s
    exact (matched_finset_sum_comp_of_bounded_fibers level N hfibers hcard g hg0 s).trans
      (mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum (s.image level) (fun n _ => hg0 n) hg) (Nat.cast_nonneg N))
  exact ⟨summable_of_sum_le (fun m => hg0 (level m)) hpartial,
    Real.tsum_le_of_sum_le (fun m => hg0 (level m)) hpartial⟩

/-- One row estimate, with an arbitrary attenuation center and a cell-level map. -/
theorem matched_level_sequence_sum_of_decay {κ : Type*}
    (level : κ → ℕ) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | level m = n})
    (hcard : ∀ n, Set.ncard {m | level m = n} ≤ N)
    {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (k : ℕ) (f : κ → ℝ) (hf : ∀ m, 0 ≤ f m)
    (hle : ∀ m, f m ≤ C * Real.exp (-(η * |radialS k - radialS (level m)|))) :
    Summable f ∧ ∑' m, f m ≤ C * ((N : ℝ) * matchedSchurFactor η) := by
  obtain ⟨hlevels, hlevels_le⟩ := radialS_row_sum hη k
  obtain ⟨hbase, hbase_le⟩ := matched_summable_comp_of_bounded_fibers level N
    hfibers hcard (fun n => Real.exp (-(η * |radialS k - radialS n|)))
    (fun _ => (Real.exp_pos _).le) hlevels
  have hsum := hbase.mul_left C
  have hsf : Summable f := Summable.of_nonneg_of_le hf hle hsum
  have hb : (∑' m, Real.exp (-(η * |radialS k - radialS (level m)|))) ≤
      (N : ℝ) * matchedSchurFactor η :=
    hbase_le.trans (mul_le_mul_of_nonneg_left hlevels_le (Nat.cast_nonneg N))
  refine ⟨hsf, ?_⟩
  calc
    (∑' m, f m) ≤ ∑' m, C * Real.exp (-(η * |radialS k - radialS (level m)|)) :=
      Summable.tsum_le_tsum hle hsf hsum
    _ = C * ∑' m, Real.exp (-(η * |radialS k - radialS (level m)|)) := tsum_mul_left
    _ ≤ C * ((N : ℝ) * matchedSchurFactor η) := mul_le_mul_of_nonneg_left hb hC

/-- Both orientations are consequences of the same row estimate. -/
theorem matched_level_kernel_sums_of_decay {κ : Type*}
    (level : κ → ℕ) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | level m = n})
    (hcard : ∀ n, Set.ncard {m | level m = n} ≤ N)
    {K : κ → κ → ℝ} {C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (hK : ∀ k m, 0 ≤ K k m)
    (hle : ∀ k m, K k m ≤ C * Real.exp
      (-(η * |radialS (level k) - radialS (level m)|))) :
    (∀ k, Summable (fun m => K k m) ∧
      ∑' m, K k m ≤ C * ((N : ℝ) * matchedSchurFactor η)) ∧
    (∀ m, Summable (fun k => K k m) ∧
      ∑' k, K k m ≤ C * ((N : ℝ) * matchedSchurFactor η)) := by
  refine ⟨fun k => matched_level_sequence_sum_of_decay level N hfibers hcard hC hη
    (level k) (K k) (hK k) (hle k), ?_⟩
  intro m
  apply matched_level_sequence_sum_of_decay level N hfibers hcard hC hη
    (level m) (fun k => K k m) (fun k => hK k m)
  intro k
  simpa only [abs_sub_comm (radialS (level m)) (radialS (level k))] using hle k m

/-- Operator Schur bound on the actual cell enumeration. -/
theorem matched_level_kernel_operator_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (p : ℕ → E → ℝ) (n : ℕ → F → ℝ)
    (level : ℕ → ℕ) (N : ℕ)
    (hfibers : ∀ l, Set.Finite {m | level m = l})
    (hcard : ∀ l, Set.ncard {m | level m = l} ≤ N)
    (K : ℕ → ℕ → ℝ) {C η c₁ c₂ : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hK : ∀ k m, 0 ≤ K k m)
    (hle : ∀ k m, K k m ≤ C * Real.exp
      (-(η * |radialS (level k) - radialS (level m)|)))
    (hp0 : ∀ m x, 0 ≤ p m x) (hn0 : ∀ k y, 0 ≤ n k y)
    (hp : ∀ x, Summable (fun m => p m x ^ 2) ∧ ∑' m, p m x ^ 2 ≤ c₁ * ‖x‖ ^ 2)
    (hn : ∀ y, Summable (fun k => n k y ^ 2) ∧ ∑' k, n k y ^ 2 ≤ c₂ * ‖y‖ ^ 2)
    (hT : ∀ x y, |inner ℝ y (T x)| ≤ ∑' q : ℕ × ℕ, K q.1 q.2 * n q.1 y * p q.2 x) :
    ‖T‖ ≤ (C * ((N : ℝ) * matchedSchurFactor η)) * Real.sqrt (c₁ * c₂) := by
  obtain ⟨hrow, hcol⟩ := matched_level_kernel_sums_of_decay level N hfibers hcard hC hη hK hle
  have hB : 0 ≤ C * ((N : ℝ) * matchedSchurFactor η) :=
    mul_nonneg hC (mul_nonneg (Nat.cast_nonneg N) (matchedSchurFactor_pos hη).le)
  have h := schur_operator_bound T p n K hB hB hc₁ hc₂ hK hrow hcol hp0 hn0 hp hn hT
  have hsqrt : Real.sqrt
      ((C * ((N : ℝ) * matchedSchurFactor η)) * (C * ((N : ℝ) * matchedSchurFactor η)) * c₁ * c₂) =
      (C * ((N : ℝ) * matchedSchurFactor η)) * Real.sqrt (c₁ * c₂) := by
    rw [show (C * ((N : ℝ) * matchedSchurFactor η)) *
        (C * ((N : ℝ) * matchedSchurFactor η)) * c₁ * c₂ =
      (C * ((N : ℝ) * matchedSchurFactor η)) ^ 2 * (c₁ * c₂) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]
  exact h.trans_eq hsqrt

end ContinuousFlexibility.Radial
