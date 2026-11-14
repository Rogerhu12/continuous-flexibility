module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Real.Sqrt

/-!
# Angular frequency spaces with arbitrary spectral multiplicities

The Hilbert space is the Hilbert sum of a family `E : ℕ → Type*`.  No
dimension or separability assumption is imposed on its summands.  An
internal orthogonal Hilbert decomposition is transported to this model by
`IsHilbertSum.linearIsometryEquiv`.

The Sobolev weight is exactly the Japanese bracket `sqrt (1 + n²)`.
Weighted norms are defined independently of a membership proof; every
analytic statement about them includes the corresponding domain condition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

/-- The exact frequency weight used in the angular Sobolev norms. -/
def angularWeight (n : ℕ) : ℝ := Real.sqrt (1 + (n : ℝ) ^ 2)

theorem angularWeight_nonneg (n : ℕ) : 0 ≤ angularWeight n :=
  Real.sqrt_nonneg _

theorem one_le_angularWeight (n : ℕ) : 1 ≤ angularWeight n := by
  apply Real.one_le_sqrt.mpr
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem angularWeight_pos (n : ℕ) : 0 < angularWeight n :=
  zero_lt_one.trans_le (one_le_angularWeight n)

theorem natCast_le_angularWeight (n : ℕ) : (n : ℝ) ≤ angularWeight n := by
  apply Real.le_sqrt_of_sq_le
  linarith

theorem angularWeight_le_one_add (n : ℕ) : angularWeight n ≤ 1 + (n : ℝ) := by
  rw [angularWeight]
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem angularWeight_sq (n : ℕ) : angularWeight n ^ 2 = 1 + (n : ℝ) ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Membership in the domain of a real spectral multiplier. -/
def MemAngularWeight (w : ℕ → ℝ) (v : lp E 2) : Prop :=
  Memℓp (fun n => (w n : 𝕜) • v n) 2

/-- The weighted coefficient vector, when it belongs to the Hilbert sum. -/
def angularMultiplierVector (w : ℕ → ℝ) (v : lp E 2)
    (hv : MemAngularWeight (𝕜 := 𝕜) w v) : lp E 2 :=
  ⟨fun n => (w n : 𝕜) • v n, hv⟩

@[simp] theorem angularMultiplierVector_apply (w : ℕ → ℝ) (v : lp E 2)
    (hv : MemAngularWeight (𝕜 := 𝕜) w v) (n : ℕ) :
    angularMultiplierVector w v hv n = (w n : 𝕜) • v n := rfl

/-- The weighted norm; use it together with `MemAngularWeight`. -/
def angularWeightNorm (w : ℕ → ℝ) (v : lp E 2) : ℝ :=
  Real.sqrt (∑' n, ‖(w n : 𝕜) • v n‖ ^ 2)

theorem angularWeightNorm_nonneg (w : ℕ → ℝ) (v : lp E 2) :
    0 ≤ angularWeightNorm (𝕜 := 𝕜) w v := Real.sqrt_nonneg _

theorem angular_tsum_norm_sq (v : lp E 2) :
    ∑' n, ‖v n‖ ^ 2 = ‖v‖ ^ 2 := by
  simpa [Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (by simp : 0 < (2 : ℝ≥0∞).toReal) v).symm

theorem angular_summable_norm_sq (v : lp E 2) :
    Summable (fun n => ‖v n‖ ^ 2) := by
  simpa [Real.rpow_two] using
    (lp.memℓp v).summable (by simp : 0 < (2 : ℝ≥0∞).toReal)

theorem norm_angularMultiplierVector (w : ℕ → ℝ) (v : lp E 2)
    (hv : MemAngularWeight (𝕜 := 𝕜) w v) :
    ‖angularMultiplierVector w v hv‖ = angularWeightNorm (𝕜 := 𝕜) w v := by
  have h := angular_tsum_norm_sq (angularMultiplierVector w v hv)
  simp only [angularMultiplierVector_apply] at h
  rw [angularWeightNorm, h, Real.sqrt_sq (norm_nonneg _)]

theorem MemAngularWeight.zero (w : ℕ → ℝ) :
    MemAngularWeight (𝕜 := 𝕜) w (0 : lp E 2) := by
  simpa only [MemAngularWeight, lp.coeFn_zero, Pi.zero_apply, smul_zero, Pi.zero_def] using
    (zero_memℓp : Memℓp (0 : ∀ n, E n) 2)

theorem MemAngularWeight.add {w : ℕ → ℝ} {u v : lp E 2}
    (hu : MemAngularWeight (𝕜 := 𝕜) w u)
    (hv : MemAngularWeight (𝕜 := 𝕜) w v) :
    MemAngularWeight (𝕜 := 𝕜) w (u + v) := by
  simpa only [MemAngularWeight, lp.coeFn_add, Pi.add_apply, smul_add, Pi.add_def] using
    Memℓp.add hu hv

theorem MemAngularWeight.smul {w : ℕ → ℝ} {v : lp E 2}
    (hv : MemAngularWeight (𝕜 := 𝕜) w v) (c : 𝕜) :
    MemAngularWeight (𝕜 := 𝕜) w (c • v) := by
  have heq : (fun n => (w n : 𝕜) • (c • v n)) =
      (fun n => c • ((w n : 𝕜) • v n)) := by
    funext n
    exact smul_comm _ _ _
  simpa only [MemAngularWeight, lp.coeFn_smul, Pi.smul_apply, Pi.smul_def, heq] using
    Memℓp.const_smul hv c

theorem MemAngularWeight.sub {w : ℕ → ℝ} {u v : lp E 2}
    (hu : MemAngularWeight (𝕜 := 𝕜) w u)
    (hv : MemAngularWeight (𝕜 := 𝕜) w v) :
    MemAngularWeight (𝕜 := 𝕜) w (u - v) := by
  simpa only [MemAngularWeight, lp.coeFn_sub, Pi.sub_apply, smul_sub, Pi.sub_def] using
    Memℓp.sub hu hv

theorem MemAngularWeight.mono {w z : ℕ → ℝ} {v : lp E 2}
    (hz : MemAngularWeight (𝕜 := 𝕜) z v) (hwz : ∀ n, |w n| ≤ |z n|) :
    MemAngularWeight (𝕜 := 𝕜) w v := by
  apply Memℓp.mono' hz
  intro n
  simp only [norm_smul, RCLike.norm_ofReal]
  exact mul_le_mul_of_nonneg_right (hwz n) (norm_nonneg _)

theorem angularWeightNorm_mono {w z : ℕ → ℝ} {v : lp E 2}
    (hz : MemAngularWeight (𝕜 := 𝕜) z v) (hwz : ∀ n, |w n| ≤ |z n|) :
    angularWeightNorm (𝕜 := 𝕜) w v ≤ angularWeightNorm (𝕜 := 𝕜) z v := by
  rw [← norm_angularMultiplierVector w v (hz.mono hwz),
    ← norm_angularMultiplierVector z v hz]
  apply lp.norm_mono (by norm_num)
  intro n
  simp only [angularMultiplierVector_apply, norm_smul, RCLike.norm_ofReal]
  exact mul_le_mul_of_nonneg_right (hwz n) (norm_nonneg _)

/-- Integer angular Sobolev domains. -/
def MemAngularSobolev (p : ℕ) (v : lp E 2) : Prop :=
  MemAngularWeight (𝕜 := 𝕜) (fun n => angularWeight n ^ p) v

/-- The coefficient vector defining the order `p` Sobolev norm. -/
def angularWeightedVector (p : ℕ) (v : lp E 2)
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) : lp E 2 :=
  angularMultiplierVector (fun n => angularWeight n ^ p) v hv

@[simp] theorem angularWeightedVector_apply (p : ℕ) (v : lp E 2)
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) (n : ℕ) :
    angularWeightedVector p v hv n = ((angularWeight n ^ p : ℝ) : 𝕜) • v n := rfl

/-- The exact Japanese-bracket Sobolev norm. -/
def angularSobolevNorm (p : ℕ) (v : lp E 2) : ℝ :=
  angularWeightNorm (𝕜 := 𝕜) (fun n => angularWeight n ^ p) v

theorem norm_angularWeightedVector (p : ℕ) (v : lp E 2)
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    ‖angularWeightedVector p v hv‖ = angularSobolevNorm (𝕜 := 𝕜) p v :=
  norm_angularMultiplierVector _ _ hv

theorem angularSobolevNorm_nonneg (p : ℕ) (v : lp E 2) :
    0 ≤ angularSobolevNorm (𝕜 := 𝕜) p v := angularWeightNorm_nonneg _ _

@[simp] theorem memAngularSobolev_zero (v : lp E 2) :
    MemAngularSobolev (𝕜 := 𝕜) 0 v := by
  simpa [MemAngularSobolev, MemAngularWeight] using lp.memℓp v

@[simp] theorem angularSobolevNorm_zero (v : lp E 2) :
    angularSobolevNorm (𝕜 := 𝕜) 0 v = ‖v‖ := by
  simp only [angularSobolevNorm, angularWeightNorm, pow_zero, RCLike.ofReal_one,
    one_smul, angular_tsum_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem MemAngularSobolev.of_le {p q : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) q v) (hpq : p ≤ q) :
    MemAngularSobolev (𝕜 := 𝕜) p v := by
  apply MemAngularWeight.mono hv
  intro n
  simp only [abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) _)]
  exact pow_le_pow_right₀ (one_le_angularWeight n) hpq

theorem angularSobolevNorm_mono {p q : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) q v) (hpq : p ≤ q) :
    angularSobolevNorm (𝕜 := 𝕜) p v ≤ angularSobolevNorm (𝕜 := 𝕜) q v := by
  apply angularWeightNorm_mono hv
  intro n
  simp only [abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) _)]
  exact pow_le_pow_right₀ (one_le_angularWeight n) hpq

/-- Weighted domains are linear subspaces of the original Hilbert space. -/
def angularWeightDomain (w : ℕ → ℝ) : Submodule 𝕜 (lp E 2) where
  carrier := {v | MemAngularWeight (𝕜 := 𝕜) w v}
  zero_mem' := MemAngularWeight.zero w
  add_mem' := MemAngularWeight.add
  smul_mem' c _ hv := hv.smul c

private def angularDiagonalLinear (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ n, |w n| ≤ C) : lp E 2 →ₗ[𝕜] lp E 2 where
  toFun v := ⟨fun n => (w n : 𝕜) • v n,
    (lp.memℓp v).norm.const_mul C |>.mono (fun n => by
      rw [norm_smul, RCLike.norm_ofReal]
      exact mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _))⟩
  map_add' u v := by ext n; exact smul_add _ _ _
  map_smul' c v := by ext n; exact smul_comm _ _ _

private theorem angularDiagonalLinear_bound (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ n, |w n| ≤ C) (v : lp E 2) :
    ‖angularDiagonalLinear (𝕜 := 𝕜) w C hw v‖ ≤ C * ‖v‖ := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw 0)
  calc
    _ ≤ ‖(C : 𝕜) • v‖ := lp.norm_mono (by norm_num) (fun n => by
      change ‖(w n : 𝕜) • v n‖ ≤ ‖(C : 𝕜) • v n‖
      simp only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _))
    _ = C * ‖v‖ := by rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC]

/-- A bounded real spectral multiplier on a Hilbert sum. -/
def angularBoundedDiagonal (w : ℕ → ℝ) (hw : ∃ C : ℝ, ∀ n, |w n| ≤ C) :
    lp E 2 →L[𝕜] lp E 2 :=
  (angularDiagonalLinear w hw.choose hw.choose_spec).mkContinuous hw.choose
    (angularDiagonalLinear_bound w hw.choose hw.choose_spec)

@[simp] theorem angularBoundedDiagonal_apply (w : ℕ → ℝ)
    (hw : ∃ C : ℝ, ∀ n, |w n| ≤ C) (v : lp E 2) (n : ℕ) :
    angularBoundedDiagonal (𝕜 := 𝕜) w hw v n = (w n : 𝕜) • v n := rfl

theorem angularBoundedDiagonal_norm_le (w : ℕ → ℝ)
    (hw : ∃ C : ℝ, ∀ n, |w n| ≤ C) {C : ℝ} (hC : ∀ n, |w n| ≤ C) :
    ‖angularBoundedDiagonal (𝕜 := 𝕜) (E := E) w hw‖ ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  intro v
  calc
    _ ≤ ‖(C : 𝕜) • v‖ := lp.norm_mono (by norm_num) (fun n => by
      simp only [angularBoundedDiagonal_apply, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    _ = C * ‖v‖ := by rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC0]

/-- The domain of the unbounded angular frequency operator. -/
def angularFrequencyDomain : Submodule 𝕜 (lp E 2) :=
  angularWeightDomain (fun n => (n : ℝ))

/-- Multiplication by the integer frequency, with its maximal Hilbert-space domain. -/
def angularFrequency : lp E 2 →ₗ.[𝕜] lp E 2 where
  domain := angularFrequencyDomain
  toFun :=
    { toFun := fun v => angularMultiplierVector (fun n => (n : ℝ)) v v.property
      map_add' := by intro u v; ext n; exact smul_add _ _ _
      map_smul' := by intro c v; ext n; exact smul_comm _ _ _ }

@[simp] theorem angularFrequency_apply
    (v : (angularFrequency (𝕜 := 𝕜) (E := E)).domain)
    (n : ℕ) : angularFrequency v n = ((n : ℝ) : 𝕜) • (v : lp E 2) n := rfl

theorem mem_angularFrequencyDomain_of_sobolev {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) 1 v) :
    v ∈ angularFrequencyDomain (𝕜 := 𝕜) := by
  apply MemAngularWeight.mono hv
  intro n
  simpa [abs_of_nonneg (angularWeight_nonneg n),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using natCast_le_angularWeight n

end ContinuousFlexibility.Analysis
