import ContinuousFlexibility.Analysis.AngularInverseRegularity

/-!
# Higher angular powers and the commuted equation

The powers below are iterates of the maximal frequency operator.  Their
coordinate formulas and all linearity assertions are proved on the actual
Sobolev domains, including the intermediate domains in the commutator sum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

/-- The `p`th power of the frequency operator.  Its intended domain is
`MemAngularSobolev p`; formulas below retain that hypothesis. -/
def angularDerivativePower (p : ℕ) (v : lp E 2) : lp E 2 :=
  (angularDerivative (𝕜 := 𝕜))^[p] v

@[simp] theorem angularDerivativePower_zero (v : lp E 2) :
    angularDerivativePower (𝕜 := 𝕜) 0 v = v :=
  Function.iterate_zero_apply _ _

theorem angularDerivativePower_succ (p : ℕ) (v : lp E 2) :
    angularDerivativePower (𝕜 := 𝕜) (p + 1) v =
      angularDerivativePower (𝕜 := 𝕜) p (angularDerivative (𝕜 := 𝕜) v) :=
  Function.iterate_succ_apply _ _ _

theorem angularDerivativePower_add_order (p q : ℕ) (v : lp E 2) :
    angularDerivativePower (𝕜 := 𝕜) (p + q) v =
      angularDerivativePower (𝕜 := 𝕜) p (angularDerivativePower (𝕜 := 𝕜) q v) :=
  Function.iterate_add_apply _ _ _ _

theorem MemAngularSobolev.derivative_power {p q : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) (p + q) v) :
    MemAngularSobolev (𝕜 := 𝕜) p (angularDerivativePower (𝕜 := 𝕜) q v) := by
  induction q generalizing v with
  | zero => simpa only [Nat.add_zero, angularDerivativePower_zero] using hv
  | succ q ih =>
      rw [angularDerivativePower_succ]
      apply ih
      apply MemAngularSobolev.derivative
      simpa only [Nat.add_assoc] using hv

@[simp] theorem angularDerivativePower_apply (p : ℕ) (v : lp E 2)
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) (n : ℕ) :
    angularDerivativePower (𝕜 := 𝕜) p v n = (((n : ℝ) ^ p : ℝ) : 𝕜) • v n := by
  induction p generalizing v with
  | zero => simp only [angularDerivativePower_zero, pow_zero, RCLike.ofReal_one, one_smul]
  | succ p ih =>
      have hd : v ∈ angularFrequencyDomain (𝕜 := 𝕜) :=
        mem_angularFrequencyDomain_of_sobolev (hv.of_le (by omega))
      rw [angularDerivativePower_succ, ih _ hv.derivative, angularDerivative_apply hd]
      simp only [pow_succ, RCLike.ofReal_mul, mul_smul]

theorem angularDerivativePower_add (p : ℕ) {u v : lp E 2}
    (hu : MemAngularSobolev (𝕜 := 𝕜) p u)
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    angularDerivativePower (𝕜 := 𝕜) p (u + v) =
      angularDerivativePower (𝕜 := 𝕜) p u + angularDerivativePower (𝕜 := 𝕜) p v := by
  ext n
  rw [angularDerivativePower_apply p _ (MemAngularWeight.add hu hv)]
  simp only [lp.coeFn_add, Pi.add_apply, angularDerivativePower_apply p u hu,
    angularDerivativePower_apply p v hv, smul_add]

theorem norm_angularDerivativePower_le (p : ℕ) {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    ‖angularDerivativePower (𝕜 := 𝕜) p v‖ ≤ angularSobolevNorm (𝕜 := 𝕜) p v := by
  rw [← norm_angularWeightedVector p v hv]
  apply lp.norm_mono (by norm_num)
  intro n
  rw [angularDerivativePower_apply p v hv, angularWeightedVector_apply]
  simp only [norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) _),
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (natCast_le_angularWeight n) p

theorem angularSobolevNorm_derivativePower_le (p q : ℕ) {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) (p + q) v) :
    angularSobolevNorm (𝕜 := 𝕜) p (angularDerivativePower (𝕜 := 𝕜) q v) ≤
      angularSobolevNorm (𝕜 := 𝕜) (p + q) v := by
  have hq : MemAngularSobolev (𝕜 := 𝕜) q v := hv.of_le (Nat.le_add_left q p)
  rw [← norm_angularWeightedVector p _ hv.derivative_power,
    ← norm_angularWeightedVector (p + q) v hv]
  apply lp.norm_mono (by norm_num)
  intro n
  rw [angularWeightedVector_apply, angularDerivativePower_apply q v hq,
    angularWeightedVector_apply]
  simp only [norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) q),
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p),
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) (p + q))]
  rw [pow_add]
  calc
    angularWeight n ^ p * ((n : ℝ) ^ q * ‖v n‖) ≤
        angularWeight n ^ p * (angularWeight n ^ q * ‖v n‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (natCast_le_angularWeight n) q) (norm_nonneg _))
        (pow_nonneg (angularWeight_nonneg n) p)
    _ = angularWeight n ^ p * angularWeight n ^ q * ‖v n‖ := by ring

/-- The full order-`p` commutator formula, including arbitrary spectral
multiplicities and every intermediate Sobolev domain. -/
theorem angularDerivativePower_commutator (R K : lp E 2 →L[𝕜] lp E 2)
    (hR : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (R v))
    (hK : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (K v))
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (R v) = R (angularDerivative (𝕜 := 𝕜) v) + K v)
    (p : ℕ) (v : lp E 2) (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    angularDerivativePower (𝕜 := 𝕜) p (R v) =
      R (angularDerivativePower (𝕜 := 𝕜) p v) +
        ∑ k ∈ Finset.range p,
          angularDerivativePower (𝕜 := 𝕜) k (K (angularDerivativePower (𝕜 := 𝕜) (p - 1 - k) v)) := by
  induction p generalizing v with
  | zero => simp only [angularDerivativePower_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ p ih =>
      have hd : v ∈ angularFrequencyDomain (𝕜 := 𝕜) :=
        mem_angularFrequencyDomain_of_sobolev (hv.of_le (by omega))
      have hDv : MemAngularSobolev (𝕜 := 𝕜) p (angularDerivative (𝕜 := 𝕜) v) := hv.derivative
      rw [angularDerivativePower_succ, hcomm v hd,
        angularDerivativePower_add p (hR p _ hDv) (hK p v (hv.of_le (by omega))), ih _ hDv]
      have hsum : (∑ k ∈ Finset.range p,
          angularDerivativePower (𝕜 := 𝕜) k
            (K (angularDerivativePower (𝕜 := 𝕜) (p - 1 - k) (angularDerivative (𝕜 := 𝕜) v)))) =
          ∑ k ∈ Finset.range p,
            angularDerivativePower (𝕜 := 𝕜) k (K (angularDerivativePower (𝕜 := 𝕜) (p - k) v)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < p := Finset.mem_range.mp hk
        have hind : p - 1 - k + 1 = p - k := by omega
        rw [← angularDerivativePower_succ, hind]
      rw [hsum, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, angularDerivativePower_zero,
        angularDerivativePower_succ]
      abel

/-- The exact commuted equation used to estimate the inverse. -/
theorem angularInverse_commuted_equation (R K B : lp E 2 →L[𝕜] lp E 2)
    (hR : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (R v))
    (hK : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (K v))
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (R v) = R (angularDerivative (𝕜 := 𝕜) v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f)
    (p : ℕ) (f : lp E 2) (hf : MemAngularSobolev (𝕜 := 𝕜) p f) :
    angularDerivativePower (𝕜 := 𝕜) p (B f) + R (angularDerivativePower (𝕜 := 𝕜) p (B f)) =
      angularDerivativePower (𝕜 := 𝕜) p f -
        ∑ k ∈ Finset.range p,
          angularDerivativePower (𝕜 := 𝕜) k (K (angularDerivativePower (𝕜 := 𝕜) (p - 1 - k) (B f))) := by
  have hRdom : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      R v ∈ angularFrequencyDomain (𝕜 := 𝕜) := by
    intro v hv
    exact (memAngularSobolev_one_iff_frequency _).mp
      (hR 1 v ((memAngularSobolev_one_iff_frequency _).mpr hv))
  have hu := angularInverse_preserves_sobolev R K B hRdom hK hcomm hleft hright p f hf
  have h := congrArg (angularDerivativePower (𝕜 := 𝕜) p) (hright f)
  rw [angularDerivativePower_add p hu (hR p _ hu),
    angularDerivativePower_commutator R K hR hK hcomm p _ hu] at h
  apply eq_sub_of_add_eq
  simpa only [add_assoc] using h

end ContinuousFlexibility.Analysis
