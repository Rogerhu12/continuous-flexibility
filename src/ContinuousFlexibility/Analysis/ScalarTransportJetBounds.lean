import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Weighted scalar bounds for finite transport recurrences

The point variable may contain the state, parameter directions, component,
radius and angle. All constants are chosen before that variable. The
integer degree counts spatial derivatives only, and the integer charge
counts occurrences of the independent residual. Multiplication adds
both counts, so a recurrence with exactly one charged factor retains its
original small material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

variable {X : Type*}

/-- An actual scalar estimate, with numerical constants independent of
the point and with the spatial degree and residual weight explicit. -/
def HasWeightedJetBound (W H Q : X → ℝ) (U : Set X) (denom : ℝ)
    (degree charge : ℕ) (f : X → ℝ) : Prop :=
  ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧ ∀ x ∈ U,
    |f x| ≤ C * W x ^ P * H x ^ charge * Q x ^ ((degree : ℝ) / denom)

section Operations

variable {W H Q : X → ℝ} {U : Set X} {denom : ℝ}
  {d e c k : ℕ} {f g : X → ℝ}

theorem HasWeightedJetBound.mono
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (hle : ∀ x ∈ U, |g x| ≤ |f x|) :
    HasWeightedJetBound W H Q U denom d c g := by
  obtain ⟨C, P, hC, hP, hb⟩ := hf
  exact ⟨C, P, hC, hP, fun x hx => (hle x hx).trans (hb x hx)⟩

theorem HasWeightedJetBound.congr
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (heq : ∀ x ∈ U, g x = f x) :
    HasWeightedJetBound W H Q U denom d c g :=
  hf.mono (fun x hx => (congrArg abs (heq x hx)).le)

theorem HasWeightedJetBound.neg
    (hf : HasWeightedJetBound W H Q U denom d c f) :
    HasWeightedJetBound W H Q U denom d c (fun x => -f x) :=
  hf.mono (fun x _ => (abs_neg (f x)).le)

theorem HasWeightedJetBound.abs
    (hf : HasWeightedJetBound W H Q U denom d c f) :
    HasWeightedJetBound W H Q U denom d c (fun x => |f x|) :=
  hf.mono (fun x _ => (abs_abs (f x)).le)

theorem HasWeightedJetBound.const (a : ℝ) :
    HasWeightedJetBound W H Q U denom 0 0 (fun _ => a) := by
  refine ⟨|a|, 0, abs_nonneg _, le_rfl, fun x hx => ?_⟩
  simp only [Real.rpow_zero, pow_zero, Nat.cast_zero, zero_div, mul_one, le_refl]

theorem HasWeightedJetBound.zero
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) :
    HasWeightedJetBound W H Q U denom d c (fun _ => 0) := by
  refine ⟨0, 0, le_rfl, le_rfl, fun x hx => ?_⟩
  simp only [abs_zero, zero_mul, le_refl]

theorem HasWeightedJetBound.monoDegree
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (hdenom : 0 < denom) (hde : d ≤ e) :
    HasWeightedJetBound W H Q U denom e c f := by
  obtain ⟨C, P, hC, hP, hb⟩ := hf
  refine ⟨C, P, hC, hP, fun x hx => (hb x hx).trans ?_⟩
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hQ x hx)
      (div_le_div_of_nonneg_right (by exact_mod_cast hde) hdenom.le))
  exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (hW x hx)) _))
    (pow_nonneg (hH x hx) _)

theorem HasWeightedJetBound.add
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (hg : HasWeightedJetBound W H Q U denom d c g) :
    HasWeightedJetBound W H Q U denom d c (fun x => f x + g x) := by
  obtain ⟨Cf, Pf, hCf, hPf, hfb⟩ := hf
  obtain ⟨Cg, Pg, hCg, hPg, hgb⟩ := hg
  refine ⟨Cf + Cg, Pf + Pg, add_nonneg hCf hCg, add_nonneg hPf hPg, ?_⟩
  intro x hx
  have htail : 0 ≤ H x ^ c * Q x ^ ((d : ℝ) / denom) :=
    mul_nonneg (pow_nonneg (hH x hx) _) (Real.rpow_nonneg (zero_le_one.trans (hQ x hx)) _)
  have hf' : |f x| ≤ Cf * W x ^ (Pf + Pg) * H x ^ c * Q x ^ ((d : ℝ) / denom) := by
    refine (hfb x hx).trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hW x hx) (le_add_of_nonneg_right hPg)) hCf) htail
  have hg' : |g x| ≤ Cg * W x ^ (Pf + Pg) * H x ^ c * Q x ^ ((d : ℝ) / denom) := by
    refine (hgb x hx).trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hW x hx) (le_add_of_nonneg_left hPf)) hCg) htail
  exact (abs_add_le _ _).trans ((add_le_add hf' hg').trans_eq (by ring))

theorem HasWeightedJetBound.sub
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (hg : HasWeightedJetBound W H Q U denom d c g) :
    HasWeightedJetBound W H Q U denom d c (fun x => f x - g x) :=
  (hf.add hW hH hQ hg.neg).congr (fun _ _ => sub_eq_add_neg _ _)

theorem HasWeightedJetBound.mul
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (hg : HasWeightedJetBound W H Q U denom e k g) :
    HasWeightedJetBound W H Q U denom (d + e) (c + k) (fun x => f x * g x) := by
  obtain ⟨Cf, Pf, hCf, hPf, hfb⟩ := hf
  obtain ⟨Cg, Pg, hCg, hPg, hgb⟩ := hg
  refine ⟨Cf * Cg, Pf + Pg, mul_nonneg hCf hCg, add_nonneg hPf hPg, ?_⟩
  intro x hx
  have hWpos : 0 < W x := zero_lt_one.trans_le (hW x hx)
  have hQpos : 0 < Q x := zero_lt_one.trans_le (hQ x hx)
  have hfb0 : 0 ≤ Cf * W x ^ Pf * H x ^ c * Q x ^ ((d : ℝ) / denom) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCf (Real.rpow_nonneg hWpos.le _))
      (pow_nonneg (hH x hx) _)) (Real.rpow_nonneg hQpos.le _)
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (Cf * W x ^ Pf * H x ^ c * Q x ^ ((d : ℝ) / denom)) *
        (Cg * W x ^ Pg * H x ^ k * Q x ^ ((e : ℝ) / denom)) :=
      mul_le_mul (hfb x hx) (hgb x hx) (abs_nonneg _) hfb0
    _ = _ := by
      rw [Real.rpow_add hWpos, pow_add, Nat.cast_add, add_div, Real.rpow_add hQpos]
      ring

theorem HasWeightedJetBound.const_mul
    (hf : HasWeightedJetBound W H Q U denom d c f)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (a : ℝ) :
    HasWeightedJetBound W H Q U denom d c (fun x => a * f x) := by
  simpa only [Nat.zero_add] using
    ((HasWeightedJetBound.const (W := W) (H := H) (Q := Q) (U := U) (denom := denom) a).mul
      hW hH hQ hf)

theorem HasWeightedJetBound.finset_sum
    {ι : Type*} (A : Finset ι) {f : ι → X → ℝ}
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (hf : ∀ i ∈ A, HasWeightedJetBound W H Q U denom d c (f i)) :
    HasWeightedJetBound W H Q U denom d c (fun x => ∑ i ∈ A, f i x) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasWeightedJetBound.zero hW hH hQ
  | @insert i A hi ih =>
      simpa only [Finset.sum_insert hi] using
        ((hf i (Finset.mem_insert_self i A)).add hW hH hQ
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

theorem HasWeightedJetBound.finset_prod
    {ι : Type*} (A : Finset ι) (degree charge : ι → ℕ) {f : ι → X → ℝ}
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (hf : ∀ i ∈ A, HasWeightedJetBound W H Q U denom (degree i) (charge i) (f i)) :
    HasWeightedJetBound W H Q U denom (∑ i ∈ A, degree i) (∑ i ∈ A, charge i)
      (fun x => ∏ i ∈ A, f i x) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty] using
      (HasWeightedJetBound.const (W := W) (H := H) (Q := Q) (U := U) (denom := denom) 1)
  | @insert i A hi ih =>
      simpa only [Finset.sum_insert hi, Finset.prod_insert hi] using
        ((hf i (Finset.mem_insert_self i A)).mul hW hH hQ
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

/-- A majorant by a finite sum of absolute values retains one common
power of the geometric weight and the same degree and charge. -/
theorem weightedJetBound_of_finite_majorant
    {ι : Type*} [Fintype ι] {f : ι → X → ℝ} {g : X → ℝ}
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x)
    (hf : ∀ i, HasWeightedJetBound W H Q U denom d c (f i))
    (hmajorant : ∀ x ∈ U, |g x| ≤ ∑ i, |f i x|) :
    HasWeightedJetBound W H Q U denom d c g := by
  have hs := HasWeightedJetBound.finset_sum Finset.univ hW hH hQ
    (fun i _ => (hf i).abs)
  apply hs.mono
  intro x hx
  simpa only [abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (f i x)))] using
    hmajorant x hx

end Operations

/-- Radial strong induction for an actual finite Leibniz majorant.
The static index may record the field kind, angular order and parameter
order. Only the radial rank must decrease in each unknown factor. -/
theorem weightedJetBound_of_transport_recurrence
    {I : Type*} {W H Q : X → ℝ} {U : Set X} {denom : ℝ} (N : ℕ)
    (hW : ∀ x ∈ U, 1 ≤ W x) (hH : ∀ x ∈ U, 0 ≤ H x)
    (hQ : ∀ x ∈ U, 1 ≤ Q x) (hdenom : 0 < denom)
    (F : ℕ → I → X → ℝ) (degree : ℕ → I → ℕ) (charge : I → ℕ)
    (terms : ℕ → I → ℕ) (factors : ∀ a i, Fin (terms a i) → ℕ)
    (rank : ∀ a i t, Fin (factors a i t) → ℕ)
    (index : ∀ a i t, Fin (factors a i t) → I)
    (known : ∀ a i, Fin (terms a i) → X → ℝ)
    (knownDegree : ∀ a i, Fin (terms a i) → ℕ)
    (hrank : ∀ a i t j, rank a i t j ≤ a)
    (hdegree : ∀ a i t,
      knownDegree a i t + ∑ j, degree (rank a i t j) (index a i t j) ≤ degree (a + 1) i)
    (hcharge : ∀ a i t, (∑ j, charge (index a i t j)) = charge i)
    (hzero : ∀ i, degree 0 i ≤ N →
      HasWeightedJetBound W H Q U denom (degree 0 i) (charge i) (F 0 i))
    (hknown : ∀ a i, degree (a + 1) i ≤ N → ∀ t,
      HasWeightedJetBound W H Q U denom (knownDegree a i t) 0 (known a i t))
    (hrecurrence : ∀ a i, degree (a + 1) i ≤ N → ∀ x ∈ U,
      |F (a + 1) i x| ≤ ∑ t : Fin (terms a i),
        |known a i t x| * ∏ j, |F (rank a i t j) (index a i t j) x|) :
    ∀ a i, degree a i ≤ N →
      HasWeightedJetBound W H Q U denom (degree a i) (charge i) (F a i) := by
  classical
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro i hi
      cases a with
      | zero => exact hzero i hi
      | succ a =>
          have hchild (t : Fin (terms a i)) (j : Fin (factors a i t)) :
              HasWeightedJetBound W H Q U denom
                (degree (rank a i t j) (index a i t j)) (charge (index a i t j))
                (F (rank a i t j) (index a i t j)) := by
            apply ih (rank a i t j) (Nat.lt_succ_of_le (hrank a i t j)) (index a i t j)
            have hj : degree (rank a i t j) (index a i t j) ≤
                ∑ k, degree (rank a i t k) (index a i t k) :=
              Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
            exact hj.trans ((le_add_of_nonneg_left (Nat.zero_le (knownDegree a i t))).trans
              ((hdegree a i t).trans hi))
          have hterm (t : Fin (terms a i)) :
              HasWeightedJetBound W H Q U denom (degree (a + 1) i) (charge i)
                (fun x => known a i t x * ∏ j, F (rank a i t j) (index a i t j) x) := by
            have hprod := HasWeightedJetBound.finset_prod Finset.univ
              (fun j => degree (rank a i t j) (index a i t j))
              (fun j => charge (index a i t j)) hW hH hQ (fun j _ => hchild t j)
            have hm := (hknown a i hi t).mul hW hH hQ hprod
            have hc : HasWeightedJetBound W H Q U denom
                (knownDegree a i t + ∑ j, degree (rank a i t j) (index a i t j)) (charge i)
                (fun x => known a i t x * ∏ j, F (rank a i t j) (index a i t j) x) := by
              simpa only [zero_add, hcharge a i t] using hm
            exact hc.monoDegree hW hH hQ hdenom (hdegree a i t)
          apply weightedJetBound_of_finite_majorant hW hH hQ hterm
          intro x hx
          simpa only [abs_mul, Finset.abs_prod] using hrecurrence a i hi x hx

end ContinuousFlexibility.Analysis
