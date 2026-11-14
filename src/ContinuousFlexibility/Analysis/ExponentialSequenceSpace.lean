module

public import ContinuousFlexibility.Analysis.Graded
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# An actual exponential sequence model and its smoothing operators

Each Banach level is the genuine `lp B ∞` space. The adjacent bonding map
multiplies the `k`-th coordinate by `exp (-k)`. Its compatible projective
limit consists precisely of sequences whose exponentially weighted
coordinates `exp (n*k) • u k` are bounded for every natural order `n`.

The finite-frequency projection retains the coordinates `k ≤ N`. Its
forward and tail estimates use the actual `lp` norms of the compatible
levels. Completeness and the Fréchet topology come from the closed
projective-limit construction, not from assumed regularity fields.

This canonical sequence model does not identify the manuscript's weighted
Sobolev spaces with a sequence-space retract, and does not implement a
Nash–Moser iteration.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter TopologicalSpace
open scoped Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The genuine bounded-sequence Banach level. -/
abbrev ExponentialSequenceLevel := lp (fun _ : ℕ => B) ∞

/-- A contractive scalar diagonal on the actual `lp ∞` space. -/
def sequenceDiagonal (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 1) :
    ExponentialSequenceLevel B →L[ℝ] ExponentialSequenceLevel B :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun k => a k • u k, (lp.memℓp u).mono' (fun k => by
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _)).trans_eq (one_mul _) )⟩
      map_add' := by
        intro u v
        apply lp.ext
        funext k
        exact smul_add _ _ _
      map_smul' := by
        intro c u
        apply lp.ext
        funext k
        exact smul_comm _ _ _ }
    1 (fun u => by
      simpa only [one_mul] using lp.norm_le_of_forall_le (norm_nonneg u) (fun k => by
        change ‖a k • u k‖ ≤ ‖u‖
        rw [norm_smul, Real.norm_eq_abs]
        exact ((mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _)).trans_eq
          (one_mul _)).trans (lp.norm_apply_le_norm (by simp) u k)))

@[simp] theorem sequenceDiagonal_apply (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (u : ExponentialSequenceLevel B) (k : ℕ) :
    sequenceDiagonal B a ha u k = a k • u k := rfl

theorem sequenceDiagonal_norm_le (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (u : ExponentialSequenceLevel B) : ‖sequenceDiagonal B a ha u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro k
  rw [sequenceDiagonal_apply, norm_smul, Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _)).trans_eq
    (one_mul _)).trans (lp.norm_apply_le_norm (by simp) u k)

private theorem exp_neg_nat_abs_le_one (k : ℕ) : |Real.exp (-(k : ℝ))| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))

/-- Genuine adjacent maps between the bounded exponentially weighted levels. -/
def exponentialSequenceBond (_ : ℕ) :
    ExponentialSequenceLevel B →L[ℝ] ExponentialSequenceLevel B :=
  sequenceDiagonal B (fun k => Real.exp (-(k : ℝ))) exp_neg_nat_abs_le_one

@[simp] theorem exponentialSequenceBond_apply (n : ℕ)
    (u : ExponentialSequenceLevel B) (k : ℕ) :
    exponentialSequenceBond B n u k = Real.exp (-(k : ℝ)) • u k := rfl

/-- The actual closed projective limit of the exponential Banach levels. -/
abbrev ExponentialSequenceSpace :=
  ProjectiveLimit (fun _ : ℕ => ExponentialSequenceLevel B) (exponentialSequenceBond B)

theorem isClosed_exponentialSequenceSpace :
    IsClosed (compatibleSubmodule (fun _ : ℕ => ExponentialSequenceLevel B)
      (exponentialSequenceBond B) : Set (ℕ → ExponentialSequenceLevel B)) :=
  isClosed_compatibleSubmodule _ _

theorem exponentialSequence_complete [CompleteSpace B] :
    CompleteSpace (ExponentialSequenceSpace B) := inferInstance

theorem exponentialSequence_locallyConvex :
    LocallyConvexSpace ℝ (ExponentialSequenceSpace B) := inferInstance

theorem exponentialSequence_metrizable :
    MetrizableSpace (ExponentialSequenceSpace B) := inferInstance

theorem exponentialSequence_completelyMetrizable [CompleteSpace B] :
    IsCompletelyMetrizableSpace (ExponentialSequenceSpace B) := inferInstance

/-- The original, unweighted sequence is exactly level zero. -/
def exponentialSequenceRaw (u : ExponentialSequenceSpace B) : ℕ → B := u.1 0

/-- The order `n` seminorm is the actual norm of the weighted `lp` level. -/
def exponentialSequenceSeminorm (n : ℕ) : Seminorm ℝ (ExponentialSequenceSpace B) :=
  coordinateSeminorm (fun _ : ℕ => ExponentialSequenceLevel B) (exponentialSequenceBond B) n

@[simp] theorem exponentialSequenceSeminorm_apply (n : ℕ) (u : ExponentialSequenceSpace B) :
    exponentialSequenceSeminorm B n u = ‖u.1 n‖ := rfl

theorem withSeminorms_exponentialSequence : WithSeminorms (exponentialSequenceSeminorm B) :=
  withSeminorms_coordinate _ _

theorem exponentialSequenceSeminorm_monotone : Monotone (exponentialSequenceSeminorm B) := by
  apply monotone_nat_of_le_succ
  intro n u
  change ‖u.1 n‖ ≤ ‖u.1 (n + 1)‖
  rw [← u.2 n]
  exact sequenceDiagonal_norm_le _ _ _ _

/-- Compatibility really identifies every level with exponential weighting
of the same underlying sequence. -/
theorem exponentialSequence_level_eq_weighted_raw (u : ExponentialSequenceSpace B) (n k : ℕ) :
    u.1 n k = Real.exp ((n : ℝ) * k) • exponentialSequenceRaw B u k := by
  induction n with
  | zero => simp [exponentialSequenceRaw]
  | succ n ih =>
    have hc : Real.exp (-(k : ℝ)) • u.1 (n + 1) k = u.1 n k :=
      congrArg (fun v : ExponentialSequenceLevel B => v k) (u.2 n)
    calc
      u.1 (n + 1) k = Real.exp (k : ℝ) • (Real.exp (-(k : ℝ)) • u.1 (n + 1) k) := by
        rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
      _ = Real.exp (k : ℝ) • u.1 n k := by rw [hc]
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * k) • exponentialSequenceRaw B u k := by
        rw [ih, smul_smul, ← Real.exp_add]
        congr 2
        push_cast
        ring

theorem exponentialSequence_weighted_memℓp (u : ExponentialSequenceSpace B) (n : ℕ) :
    Memℓp (fun k : ℕ => Real.exp ((n : ℝ) * k) • exponentialSequenceRaw B u k) ∞ := by
  have heq : (fun k : ℕ => Real.exp ((n : ℝ) * k) • exponentialSequenceRaw B u k) =
      (fun k => u.1 n k) := funext fun k => (exponentialSequence_level_eq_weighted_raw B u n k).symm
  rw [heq]
  exact lp.memℓp (u.1 n)

/-- Conversely, an actual sequence with all exponential `lp` bounds gives
an element of the closed projective model. -/
def exponentialSequenceOfRaw (u : ℕ → B)
    (hu : ∀ n : ℕ, Memℓp (fun k : ℕ => Real.exp ((n : ℝ) * k) • u k) ∞) :
    ExponentialSequenceSpace B :=
  ⟨fun n => ⟨fun k => Real.exp ((n : ℝ) * k) • u k, hu n⟩, by
    intro n
    apply lp.ext
    funext k
    change Real.exp (-(k : ℝ)) • (Real.exp (((n + 1 : ℕ) : ℝ) * k) • u k) =
      Real.exp ((n : ℝ) * k) • u k
    rw [smul_smul, ← Real.exp_add]
    congr 2
    push_cast
    ring⟩

@[simp] theorem exponentialSequenceRaw_ofRaw (u : ℕ → B)
    (hu : ∀ n : ℕ, Memℓp (fun k : ℕ => Real.exp ((n : ℝ) * k) • u k) ∞) :
    exponentialSequenceRaw B (exponentialSequenceOfRaw B u hu) = u := by
  funext k
  simp [exponentialSequenceRaw, exponentialSequenceOfRaw]

theorem exponentialSequenceRaw_injective : Function.Injective (exponentialSequenceRaw B) := by
  intro u v h
  apply Subtype.ext
  funext n
  apply lp.ext
  funext k
  rw [exponentialSequence_level_eq_weighted_raw, exponentialSequence_level_eq_weighted_raw, h]

@[simp] theorem exponentialSequenceOfRaw_raw (u : ExponentialSequenceSpace B) :
    exponentialSequenceOfRaw B (exponentialSequenceRaw B u)
      (exponentialSequence_weighted_memℓp B u) = u := by
  apply exponentialSequenceRaw_injective B
  exact exponentialSequenceRaw_ofRaw B _ _

/-- Exact relation between any two actual levels; no ordering assumption
is needed for this identity. -/
theorem exponentialSequence_level_relation (u : ExponentialSequenceSpace B) (n m k : ℕ) :
    u.1 n k = Real.exp (((n : ℝ) - m) * k) • u.1 m k := by
  rw [exponentialSequence_level_eq_weighted_raw B u n k,
    exponentialSequence_level_eq_weighted_raw B u m k, smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- The actual finite-frequency cutoff at one Banach level. -/
def exponentialSequenceCutLevel (N : ℕ) :
    ExponentialSequenceLevel B →L[ℝ] ExponentialSequenceLevel B :=
  sequenceDiagonal B (fun k => if k ≤ N then 1 else 0) (by intro k; split_ifs <;> norm_num)

@[simp] theorem exponentialSequenceCutLevel_apply (N : ℕ)
    (u : ExponentialSequenceLevel B) (k : ℕ) :
    exponentialSequenceCutLevel B N u k = if k ≤ N then u k else 0 := by
  simp only [exponentialSequenceCutLevel, sequenceDiagonal_apply]
  split_ifs <;> simp

/-- The cutoff commutes with the genuine bonding maps, hence gives an
actual continuous linear smoothing operator on the Fréchet space. -/
def exponentialSequenceSmoothing (N : ℕ) :
    ExponentialSequenceSpace B →L[ℝ] ExponentialSequenceSpace B :=
  projectiveLift (fun _ : ℕ => ExponentialSequenceLevel B) (exponentialSequenceBond B)
    (fun n => (exponentialSequenceCutLevel B N).comp
      (projectiveCoordinate (fun _ : ℕ => ExponentialSequenceLevel B)
        (exponentialSequenceBond B) n)) (by
    intro n
    apply ContinuousLinearMap.ext
    intro u
    apply lp.ext
    funext k
    change Real.exp (-(k : ℝ)) • (exponentialSequenceCutLevel B N (u.1 (n + 1)) k) =
      exponentialSequenceCutLevel B N (u.1 n) k
    rw [exponentialSequenceCutLevel_apply, exponentialSequenceCutLevel_apply]
    split_ifs
    · exact congrArg (fun v : ExponentialSequenceLevel B => v k) (u.2 n)
    · exact smul_zero _)

@[simp] theorem exponentialSequenceSmoothing_apply (N n k : ℕ)
    (u : ExponentialSequenceSpace B) :
    (exponentialSequenceSmoothing B N u).1 n k = if k ≤ N then u.1 n k else 0 :=
  exponentialSequenceCutLevel_apply B N _ k

@[simp] theorem exponentialSequenceSmoothing_raw (N k : ℕ)
    (u : ExponentialSequenceSpace B) :
    exponentialSequenceRaw B (exponentialSequenceSmoothing B N u) k =
      if k ≤ N then exponentialSequenceRaw B u k else 0 :=
  exponentialSequenceSmoothing_apply B N 0 k u

theorem exponentialSequenceSmoothing_support (N : ℕ) (u : ExponentialSequenceSpace B) :
    Function.support (exponentialSequenceRaw B (exponentialSequenceSmoothing B N u)) ⊆ Iic N := by
  intro k hk
  by_contra h
  change ¬k ≤ N at h
  exact hk (by simp [h])

theorem exponentialSequenceSmoothing_finite_support (N : ℕ) (u : ExponentialSequenceSpace B) :
    (Function.support (exponentialSequenceRaw B (exponentialSequenceSmoothing B N u))).Finite :=
  (Set.finite_Iic N).subset (exponentialSequenceSmoothing_support B N u)

@[simp] theorem exponentialSequenceSmoothing_idempotent (N : ℕ) (u : ExponentialSequenceSpace B) :
    exponentialSequenceSmoothing B N (exponentialSequenceSmoothing B N u) =
      exponentialSequenceSmoothing B N u := by
  apply exponentialSequenceRaw_injective B
  funext k
  simp only [exponentialSequenceSmoothing_raw]
  split_ifs <;> rfl

/-- The exact forward Hamilton estimate, with discrete smoothing parameter
`exp N` and the actual order-`m`/order-`n` norms. -/
theorem exponentialSequenceSmoothing_forward {m n : ℕ} (hmn : m ≤ n)
    (N : ℕ) (u : ExponentialSequenceSpace B) :
    exponentialSequenceSeminorm B n (exponentialSequenceSmoothing B N u) ≤
      Real.exp (((n : ℝ) - m) * N) * exponentialSequenceSeminorm B m u := by
  rw [exponentialSequenceSeminorm_apply, exponentialSequenceSeminorm_apply]
  apply lp.norm_le_of_forall_le (mul_nonneg (Real.exp_pos _).le (norm_nonneg (u.1 m)))
  intro k
  rw [exponentialSequenceSmoothing_apply]
  by_cases hk : k ≤ N
  · rw [ite_eq_left hk, exponentialSequence_level_relation B u n m k, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hk)
        (sub_nonneg.mpr (Nat.cast_le.mpr hmn))))
      (lp.norm_apply_le_norm (by simp) (u.1 m) k) (norm_nonneg _) (Real.exp_pos _).le
  · simp only [ite_eq_right hk, norm_zero]
    positivity

/-- The exact tail Hamilton estimate for the same fixed pair of orders. -/
theorem exponentialSequenceSmoothing_tail {m n : ℕ} (hmn : m ≤ n)
    (N : ℕ) (u : ExponentialSequenceSpace B) :
    exponentialSequenceSeminorm B m (u - exponentialSequenceSmoothing B N u) ≤
      Real.exp (-(((n : ℝ) - m) * N)) * exponentialSequenceSeminorm B n u := by
  rw [exponentialSequenceSeminorm_apply, exponentialSequenceSeminorm_apply]
  apply lp.norm_le_of_forall_le (mul_nonneg (Real.exp_pos _).le (norm_nonneg (u.1 n)))
  intro k
  change ‖u.1 m k - (exponentialSequenceSmoothing B N u).1 m k‖ ≤ _
  rw [exponentialSequenceSmoothing_apply]
  by_cases hk : k ≤ N
  · simp only [ite_eq_left hk, sub_self, norm_zero]
    positivity
  · rw [ite_eq_right hk, sub_zero, exponentialSequence_level_relation B u m n k, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hNk : (N : ℝ) ≤ k := Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hk))
    have hmn' : (m : ℝ) - n ≤ 0 := sub_nonpos.mpr (Nat.cast_le.mpr hmn)
    have he : ((m : ℝ) - n) * k ≤ -(((n : ℝ) - m) * N) := by
      calc
        ((m : ℝ) - n) * k ≤ ((m : ℝ) - n) * N := mul_le_mul_of_nonpos_left hNk hmn'
        _ = _ := by ring
    exact mul_le_mul (Real.exp_le_exp.mpr he)
      (lp.norm_apply_le_norm (by simp) (u.1 n) k) (norm_nonneg _) (Real.exp_pos _).le

/-- The genuine cutoffs converge to the identity in the existing projective
Fréchet topology, not just pointwise on the underlying sequences. -/
theorem tendsto_exponentialSequenceSmoothing (u : ExponentialSequenceSpace B) :
    Tendsto (fun N : ℕ => exponentialSequenceSmoothing B N u) atTop (𝓝 u) := by
  rw [tendsto_projectiveLimit_iff]
  intro m
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hzero : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)) * ‖u.1 (m + 1)‖)
      atTop (𝓝 0) := by simpa using he.mul_const ‖u.1 (m + 1)‖
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hzero
  rw [norm_sub_rev]
  have ht := exponentialSequenceSmoothing_tail B (Nat.le_succ m) N u
  change ‖u.1 m - (exponentialSequenceSmoothing B N u).1 m‖ ≤
    Real.exp (-((((m + 1 : ℕ) : ℝ) - m) * N)) * ‖u.1 (m + 1)‖ at ht
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul] using ht

private theorem memℓp_exp_neg_nat_two :
    Memℓp (fun k : ℕ => Real.exp (-(k : ℝ))) 2 := by
  apply memℓp_gen
  have hs := Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-2 : ℝ) < 0)
  have heq : (fun k : ℕ => ‖Real.exp (-(k : ℝ))‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun k : ℕ => Real.exp ((k : ℝ) * (-2))) := by
    funext k
    calc
      _ = Real.exp (-(k : ℝ)) ^ (2 : ℕ) := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        norm_num
      _ = Real.exp ((k : ℝ) * (-2)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  rw [heq]
  exact hs

/-- A fixed, genuinely square-summable exponential sequence. -/
def exponentialDecayL2 : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun k => Real.exp (-(k : ℝ)), memℓp_exp_neg_nat_two⟩

@[simp] theorem exponentialDecayL2_apply (k : ℕ) :
    exponentialDecayL2 k = Real.exp (-(k : ℝ)) := rfl

/-- The same numerical comparison constant at every order. -/
def exponentialL2ComparisonConstant : ℝ := ‖exponentialDecayL2‖

theorem one_le_exponentialL2ComparisonConstant : 1 ≤ exponentialL2ComparisonConstant := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) exponentialDecayL2 0
  simpa [exponentialL2ComparisonConstant] using h

/-- A single additional exponential order gives actual square summability. -/
theorem exponentialSequence_level_memℓp_two (u : ExponentialSequenceSpace B) (n : ℕ) :
    Memℓp (fun k => u.1 n k) 2 := by
  apply (memℓp_exp_neg_nat_two.const_mul ‖u.1 (n + 1)‖).mono
  intro k
  have hc : Real.exp (-(k : ℝ)) • u.1 (n + 1) k = u.1 n k :=
    congrArg (fun v : ExponentialSequenceLevel B => v k) (u.2 n)
  rw [← hc, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (-(k : ℝ)) * ‖u.1 (n + 1) k‖ ≤ Real.exp (-(k : ℝ)) * ‖u.1 (n + 1)‖ :=
      mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) (u.1 (n + 1)) k)
        (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- The actual square-summable weighted level, with exactly the same
underlying sequence as the bounded order-`n` level. -/
def exponentialSequenceL2Level (u : ExponentialSequenceSpace B) (n : ℕ) :
    lp (fun _ : ℕ => B) 2 := ⟨fun k => u.1 n k, exponentialSequence_level_memℓp_two B u n⟩

@[simp] theorem exponentialSequenceL2Level_apply (u : ExponentialSequenceSpace B) (n k : ℕ) :
    exponentialSequenceL2Level B u n k = u.1 n k := rfl

/-- The first direction of the standard `ℓ²`/`ℓ∞` comparison has loss zero. -/
theorem exponentialSequenceSeminorm_le_l2 (u : ExponentialSequenceSpace B) (n : ℕ) :
    exponentialSequenceSeminorm B n u ≤ ‖exponentialSequenceL2Level B u n‖ := by
  rw [exponentialSequenceSeminorm_apply]
  exact lp.norm_le_of_forall_le (norm_nonneg _) (fun k =>
    lp.norm_apply_le_norm (by norm_num) (exponentialSequenceL2Level B u n) k)

/-- The converse direction has the one fixed loss `1`, with an actual
finite constant independent of the order and the sequence. -/
theorem exponentialSequenceL2Level_norm_le (u : ExponentialSequenceSpace B) (n : ℕ) :
    ‖exponentialSequenceL2Level B u n‖ ≤
      exponentialL2ComparisonConstant * exponentialSequenceSeminorm B (n + 1) u := by
  calc
    ‖exponentialSequenceL2Level B u n‖ ≤ ‖‖u.1 (n + 1)‖ • exponentialDecayL2‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      have hc : Real.exp (-(k : ℝ)) • u.1 (n + 1) k = u.1 n k :=
        congrArg (fun v : ExponentialSequenceLevel B => v k) (u.2 n)
      change ‖u.1 n k‖ ≤ ‖‖u.1 (n + 1)‖ * Real.exp (-(k : ℝ))‖
      rw [← hc, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
      calc
        Real.exp (-(k : ℝ)) * ‖u.1 (n + 1) k‖ ≤ Real.exp (-(k : ℝ)) * ‖u.1 (n + 1)‖ :=
          mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) (u.1 (n + 1)) k)
            (Real.exp_pos _).le
        _ = _ := mul_comm _ _
    _ = exponentialL2ComparisonConstant * exponentialSequenceSeminorm B (n + 1) u := by
      rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), exponentialSequenceSeminorm_apply]
      exact mul_comm _ _

/-- The two concrete definitions of exponential rapid decrease agree as
sets of original sequences. The norm comparisons above control the
gradings with the fixed losses zero and one. -/
theorem all_exponential_memℓp_infty_iff_two (v : ℕ → B) :
    (∀ n : ℕ, Memℓp (fun k : ℕ => Real.exp ((n : ℝ) * k) • v k) ∞) ↔
      (∀ n : ℕ, Memℓp (fun k : ℕ => Real.exp ((n : ℝ) * k) • v k) 2) := by
  constructor
  · intro hv n
    let u := exponentialSequenceOfRaw B v hv
    have heq : (fun k : ℕ => Real.exp ((n : ℝ) * k) • v k) = (fun k => u.1 n k) := by
      funext k
      change Real.exp ((n : ℝ) * k) • v k = Real.exp ((n : ℝ) * k) • v k
      rfl
    rw [heq]
    exact exponentialSequence_level_memℓp_two B u n
  · intro hv n
    exact (hv n).of_exponent_ge le_top

end ContinuousFlexibility.Analysis
