module

public import ContinuousFlexibility.Analysis.PeriodicLiftAxisIntervals
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Uniqueness of a degree-one lift with an irrational second translation

A degree-one lift has bounded displacement. Consequently any constant
increment under another translation equals that translation itself.
Two incommensurable periods then force the remaining displacement to
be constant. Reflection or the value at zero removes that constant.
These statements concern genuine continuous functions on the whole
real line and do not assume differentiability or monotonicity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem continuous_eq_const_of_irrational_periods
    {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (ha : Function.Periodic f a) (hb : Function.Periodic f b)
    (hirr : Irrational (a / b)) (x : ℝ) : f x = f 0 := by
  let periods : AddSubgroup ℝ :=
    { carrier := {c | Function.Periodic f c}
      zero_mem' := Function.periodic_with_period_zero f
      add_mem' := fun h₁ h₂ => h₁.add_period h₂
      neg_mem' := fun h => h.neg }
  have hpair : ({a, b} : Set ℝ) ⊆ periods := by
    intro c hc
    rcases mem_insert_iff.mp hc with rfl | hc
    · exact ha
    · have he : c = b := mem_singleton_iff.mp hc
      subst c
      exact hb
  have hgenerated : AddSubgroup.closure ({a, b} : Set ℝ) ≤ periods :=
    (AddSubgroup.closure_le periods).mpr hpair
  have hclosed : IsClosed {t : ℝ | f t = f 0} := isClosed_eq hf continuous_const
  have hlevel : (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) ⊆
      {t : ℝ | f t = f 0} := by
    intro t ht
    have htperiod : Function.Periodic f t := hgenerated ht
    exact htperiod.eq
  have hclosure := hclosed.closure_subset_iff.mpr hlevel
  have hd : Dense (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  rw [hd.closure_eq] at hclosure
  exact hclosure (mem_univ x)

theorem shift_increment_eq_of_bounded_displacement
    {f : ℝ → ℝ} {a b M : ℝ}
    (hbound : ∀ t, |f t - t| ≤ M)
    (hshift : ∀ t, f (t + a) = f t + b) : b = a := by
  have hiter (n : ℕ) : f ((n : ℝ) * a) = f 0 + (n : ℝ) * b := by
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hshift, ih]
      ring
  by_contra hne
  have hc : 0 < |b - a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + |f 0|) / |b - a|)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlarge : M + |f 0| < (n : ℝ) * |b - a| := (div_lt_iff₀ hc).mp hn
  have hsmall : (n : ℝ) * |b - a| ≤ M + |f 0| := by
    calc
      (n : ℝ) * |b - a| = |(n : ℝ) * (b - a)| := by
        rw [abs_mul, abs_of_nonneg hn0]
      _ = |(f ((n : ℝ) * a) - (n : ℝ) * a) - f 0| := by
        rw [hiter]
        congr 1
        ring
      _ ≤ |f ((n : ℝ) * a) - (n : ℝ) * a| + |f 0| := abs_sub _ _
      _ ≤ M + |f 0| := add_le_add (hbound _) (le_refl _)
  exact (not_lt_of_ge hsmall) hlarge

theorem periodicLift_shift_increment_eq
    {f : ℝ → ℝ} {P a b : ℝ} (hP : P ≠ 0) (hf : Continuous f)
    (hperiod : ∀ t, f (t + P) = f t + P)
    (hshift : ∀ t, f (t + a) = f t + b) : b = a := by
  obtain ⟨M, _, hbound⟩ := periodicLift_displacement_bounded hP hf hperiod
  exact shift_increment_eq_of_bounded_displacement hbound hshift

/-- The additional translation determines the whole degree-one lift,
including its additive constant after fixing the value at zero. -/
theorem periodicLift_eq_id_of_irrational_shift
    {f : ℝ → ℝ} {P a b : ℝ} (hP : P ≠ 0) (hf : Continuous f)
    (hperiod : ∀ t, f (t + P) = f t + P)
    (hshift : ∀ t, f (t + a) = f t + b)
    (hirr : Irrational (a / P)) (hzero : f 0 = 0) :
    b = a ∧ ∀ t, f t = t := by
  have hba := periodicLift_shift_increment_eq hP hf hperiod hshift
  refine ⟨hba, ?_⟩
  have hp : Function.Periodic (fun t => f t - t) P := by
    intro t
    change f (t + P) - (t + P) = f t - t
    rw [hperiod]
    ring
  have ha : Function.Periodic (fun t => f t - t) a := by
    intro t
    change f (t + a) - (t + a) = f t - t
    rw [hshift, hba]
    ring
  intro t
  have hh : f t - t = f 0 - 0 := continuous_eq_const_of_irrational_periods
    (hf.sub continuous_id) ha hp hirr t
  simp only [hzero, sub_zero] at hh
  linarith only [hh]

end ContinuousFlexibility.Analysis
