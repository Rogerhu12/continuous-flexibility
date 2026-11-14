module

public import ContinuousFlexibility.Analysis.AngularWeightBounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Domains and bounded Yosida approximations of angular frequency

The regularizers are `(N+1) / (N+1+Λ)`.  They map the entire Hilbert
space into the maximal domain of `Λ`.  Their commutator identity is
proved on that domain before any inverse regularity is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped ENNReal Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

theorem memAngularSobolev_one_iff_frequency (v : lp E 2) :
    MemAngularSobolev (𝕜 := 𝕜) 1 v ↔ v ∈ angularFrequencyDomain (𝕜 := 𝕜) := by
  refine ⟨mem_angularFrequencyDomain_of_sobolev, fun hv => ?_⟩
  apply MemAngularWeight.of_le_add (memAngularWeight_const 1 v) hv
  intro n
  simpa only [pow_one, abs_of_nonneg (angularWeight_nonneg n)] using
    angularWeight_le_one_add n

/-- The partial frequency operator extended by zero outside its domain.
Every identity involving this extension has an explicit domain hypothesis. -/
def angularDerivative (v : lp E 2) : lp E 2 := by
  classical
  exact if hv : v ∈ angularFrequencyDomain (𝕜 := 𝕜) then
    angularFrequency (𝕜 := 𝕜) ⟨v, hv⟩ else 0

@[simp] theorem angularDerivative_apply {v : lp E 2}
    (hv : v ∈ angularFrequencyDomain (𝕜 := 𝕜)) (n : ℕ) :
    angularDerivative (𝕜 := 𝕜) v n = ((n : ℝ) : 𝕜) • v n := by
  simp only [angularDerivative, dif_pos hv, angularFrequency_apply]

theorem angularDerivative_add {u v : lp E 2}
    (hu : u ∈ angularFrequencyDomain (𝕜 := 𝕜))
    (hv : v ∈ angularFrequencyDomain (𝕜 := 𝕜)) :
    angularDerivative (𝕜 := 𝕜) (u + v) = angularDerivative (𝕜 := 𝕜) u + angularDerivative (𝕜 := 𝕜) v := by
  ext n
  simp only [angularDerivative_apply ((angularFrequencyDomain (𝕜 := 𝕜)).add_mem hu hv),
    angularDerivative_apply hu, angularDerivative_apply hv, lp.coeFn_add, Pi.add_apply, smul_add]

theorem MemAngularSobolev.derivative {p : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) (p + 1) v) :
    MemAngularSobolev (𝕜 := 𝕜) p (angularDerivative (𝕜 := 𝕜) v) := by
  have hd : v ∈ angularFrequencyDomain (𝕜 := 𝕜) :=
    mem_angularFrequencyDomain_of_sobolev (hv.of_le (by omega))
  apply Memℓp.mono' hv
  intro n
  rw [angularDerivative_apply hd]
  simp only [norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p),
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) (p + 1)),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  rw [pow_succ]
  calc
    angularWeight n ^ p * ((n : ℝ) * ‖v n‖) ≤
        angularWeight n ^ p * (angularWeight n * ‖v n‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (natCast_le_angularWeight n) (norm_nonneg _))
        (pow_nonneg (angularWeight_nonneg n) p)
    _ = angularWeight n ^ p * angularWeight n * ‖v n‖ := by ring

theorem memAngularSobolev_succ_of_derivative {p : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v)
    (hd : v ∈ angularFrequencyDomain (𝕜 := 𝕜))
    (hderiv : MemAngularSobolev (𝕜 := 𝕜) p (angularDerivative (𝕜 := 𝕜) v)) :
    MemAngularSobolev (𝕜 := 𝕜) (p + 1) v := by
  have hmul : MemAngularWeight (𝕜 := 𝕜)
      (fun n => angularWeight n ^ p * (n : ℝ)) v := by
    simpa only [MemAngularSobolev, MemAngularWeight, angularDerivative_apply hd,
      RCLike.ofReal_mul, mul_smul] using hderiv
  apply MemAngularWeight.of_le_add hv hmul
  intro n
  rw [abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) _), pow_succ]
  calc
    angularWeight n ^ p * angularWeight n ≤
        angularWeight n ^ p * (1 + (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (angularWeight_le_one_add n)
        (pow_nonneg (angularWeight_nonneg n) p)
    _ = angularWeight n ^ p + angularWeight n ^ p * (n : ℝ) := by ring

theorem norm_angularDerivative_le {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) 1 v) :
    ‖angularDerivative (𝕜 := 𝕜) v‖ ≤ angularSobolevNorm (𝕜 := 𝕜) 1 v := by
  rw [← norm_angularWeightedVector 1 v hv]
  apply lp.norm_mono (by norm_num)
  intro n
  rw [angularDerivative_apply (mem_angularFrequencyDomain_of_sobolev hv),
    angularWeightedVector_apply]
  simp only [norm_smul, RCLike.norm_ofReal, pow_one,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), abs_of_nonneg (angularWeight_nonneg n)]
  exact mul_le_mul_of_nonneg_right (natCast_le_angularWeight n) (norm_nonneg _)

/-- The scalar multiplier of the `N`th Yosida regularization. -/
def angularYosidaWeight (N n : ℕ) : ℝ :=
  ((N : ℝ) + 1) / ((N : ℝ) + 1 + (n : ℝ))

theorem angularYosidaWeight_nonneg (N n : ℕ) : 0 ≤ angularYosidaWeight N n := by
  unfold angularYosidaWeight
  positivity

theorem angularYosidaWeight_le_one (N n : ℕ) : angularYosidaWeight N n ≤ 1 := by
  unfold angularYosidaWeight
  apply (div_le_one (by positivity)).mpr
  exact le_add_of_nonneg_right (Nat.cast_nonneg n)

theorem abs_angularYosidaWeight_le_one (N n : ℕ) : |angularYosidaWeight N n| ≤ 1 := by
  rw [abs_of_nonneg (angularYosidaWeight_nonneg N n)]
  exact angularYosidaWeight_le_one N n

theorem angularYosidaWeight_identity (N n : ℕ) :
    ((N : ℝ) + 1) * (1 - angularYosidaWeight N n) =
      (n : ℝ) * angularYosidaWeight N n := by
  have h : (N : ℝ) + 1 + (n : ℝ) ≠ 0 := by positivity
  unfold angularYosidaWeight
  field_simp [h]
  <;> ring

theorem angularYosidaWeight_tendsto (n : ℕ) :
    Tendsto (fun N => angularYosidaWeight N n) atTop (𝓝 1) := by
  simpa only [angularYosidaWeight, Nat.cast_add, Nat.cast_one] using
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_natCast_div_add_atTop (n : ℝ))

/-- A contractive bounded resolvent of the frequency operator. -/
def angularYosida (N : ℕ) : lp E 2 →L[𝕜] lp E 2 :=
  angularBoundedDiagonal (angularYosidaWeight N)
    ⟨1, abs_angularYosidaWeight_le_one N⟩

@[simp] theorem angularYosida_apply (N : ℕ) (v : lp E 2) (n : ℕ) :
    angularYosida (𝕜 := 𝕜) N v n = (angularYosidaWeight N n : 𝕜) • v n :=
  angularBoundedDiagonal_apply _ _ _ _

theorem angularYosida_norm_le_one (N : ℕ) :
    ‖angularYosida (𝕜 := 𝕜) (E := E) N‖ ≤ 1 :=
  angularBoundedDiagonal_norm_le _ _ (abs_angularYosidaWeight_le_one N)

theorem norm_angularYosida_le (N : ℕ) (v : lp E 2) :
    ‖angularYosida (𝕜 := 𝕜) N v‖ ≤ ‖v‖ := by
  simpa only [one_mul] using
    (angularYosida (𝕜 := 𝕜) (E := E) N).le_of_opNorm_le (angularYosida_norm_le_one N) v

/-- The bounded operator `Λ (N+1)/(N+1+Λ)`. -/
def angularYosidaDerivative (N : ℕ) : lp E 2 →L[𝕜] lp E 2 :=
  (((N : ℝ) + 1 : ℝ) : 𝕜) •
    (ContinuousLinearMap.id 𝕜 (lp E 2) - angularYosida (𝕜 := 𝕜) N)

theorem angularYosidaDerivative_eq (N : ℕ) (v : lp E 2) :
    angularYosidaDerivative (𝕜 := 𝕜) N v =
      (((N : ℝ) + 1 : ℝ) : 𝕜) • (v - angularYosida (𝕜 := 𝕜) N v) := by
  simp only [angularYosidaDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]

@[simp] theorem angularYosidaDerivative_apply (N : ℕ) (v : lp E 2) (n : ℕ) :
    angularYosidaDerivative (𝕜 := 𝕜) N v n =
      (((n : ℝ) * angularYosidaWeight N n : ℝ) : 𝕜) • v n := by
  have h := congrArg (fun c : ℝ => (c : 𝕜) • v n) (angularYosidaWeight_identity N n)
  simpa only [angularYosidaDerivative_eq, lp.coeFn_smul, Pi.smul_apply,
    lp.coeFn_sub, Pi.sub_apply, angularYosida_apply, RCLike.ofReal_mul,
    RCLike.ofReal_sub, RCLike.ofReal_one, mul_smul, sub_smul, one_smul] using h

theorem angularYosida_mem_frequency (N : ℕ) (v : lp E 2) :
    angularYosida (𝕜 := 𝕜) N v ∈ angularFrequencyDomain (𝕜 := 𝕜) := by
  change Memℓp (fun n : ℕ => ((n : ℝ) : 𝕜) • angularYosida (𝕜 := 𝕜) N v n) 2
  convert lp.memℓp (angularYosidaDerivative (𝕜 := 𝕜) N v) using 1
  funext n
  simp only [angularYosidaDerivative_apply, angularYosida_apply,
    RCLike.ofReal_mul, mul_smul]

theorem angularDerivative_yosida (N : ℕ) (v : lp E 2) :
    angularDerivative (𝕜 := 𝕜) (angularYosida (𝕜 := 𝕜) N v) = angularYosidaDerivative (𝕜 := 𝕜) N v := by
  ext n
  simp only [angularDerivative_apply (angularYosida_mem_frequency N v),
    angularYosida_apply, angularYosidaDerivative_apply, RCLike.ofReal_mul, mul_smul]

theorem angularYosida_derivative (N : ℕ) {v : lp E 2}
    (hv : v ∈ angularFrequencyDomain (𝕜 := 𝕜)) :
    angularYosida (𝕜 := 𝕜) N (angularDerivative (𝕜 := 𝕜) v) = angularYosidaDerivative (𝕜 := 𝕜) N v := by
  ext n
  simp only [angularYosida_apply, angularDerivative_apply hv,
    angularYosidaDerivative_apply, RCLike.ofReal_mul, mul_smul]
  exact smul_comm _ _ _

theorem norm_angularYosidaDerivative_le (N : ℕ) {v : lp E 2}
    (hv : v ∈ angularFrequencyDomain (𝕜 := 𝕜)) :
    ‖angularYosidaDerivative (𝕜 := 𝕜) N v‖ ≤ ‖angularDerivative (𝕜 := 𝕜) v‖ := by
  rw [← angularYosida_derivative N hv]
  exact norm_angularYosida_le _ _

theorem angularYosida_resolvent (N : ℕ) (v : lp E 2) :
    (((N : ℝ) + 1 : ℝ) : 𝕜) • angularYosida (𝕜 := 𝕜) N v +
      angularYosidaDerivative (𝕜 := 𝕜) N v = (((N : ℝ) + 1 : ℝ) : 𝕜) • v := by
  rw [angularYosidaDerivative_eq, smul_sub]
  abel

/-- The resolvent commutator is an identity of bounded operators. -/
theorem angularYosidaDerivative_commutator (R K : lp E 2 →L[𝕜] lp E 2)
    (hR : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      R v ∈ angularFrequencyDomain (𝕜 := 𝕜))
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (R v) = R (angularDerivative (𝕜 := 𝕜) v) + K v)
    (N : ℕ) (v : lp E 2) :
    angularYosidaDerivative (𝕜 := 𝕜) N (R v) =
      R (angularYosidaDerivative (𝕜 := 𝕜) N v) + angularYosida (𝕜 := 𝕜) N (K (angularYosida (𝕜 := 𝕜) N v)) := by
  let t : 𝕜 := (((N : ℝ) + 1 : ℝ) : 𝕜)
  have hJ := congrArg (angularYosida (𝕜 := 𝕜) N)
    (hcomm (angularYosida (𝕜 := 𝕜) N v) (angularYosida_mem_frequency N v))
  rw [angularYosida_derivative N (hR _ (angularYosida_mem_frequency N v)),
    angularDerivative_yosida, map_add] at hJ
  have hRJ := congrArg (fun x => angularYosida (𝕜 := 𝕜) N (R x))
    (angularYosida_resolvent (𝕜 := 𝕜) N v)
  simp only [R.map_add, R.map_smul,
    (angularYosida (𝕜 := 𝕜) N).map_add, (angularYosida (𝕜 := 𝕜) N).map_smul] at hRJ
  have hres := angularYosida_resolvent (𝕜 := 𝕜) N (R (angularYosida (𝕜 := 𝕜) N v))
  rw [hJ, ← add_assoc, hRJ] at hres
  change t • angularYosida (𝕜 := 𝕜) N (R v) + angularYosida (𝕜 := 𝕜) N (K (angularYosida (𝕜 := 𝕜) N v)) =
    t • R (angularYosida (𝕜 := 𝕜) N v) at hres
  rw [angularYosidaDerivative_eq, angularYosidaDerivative_eq, map_smul, map_sub, smul_sub]
  change t • R v - t • angularYosida (𝕜 := 𝕜) N (R v) =
    t • (R v - R (angularYosida (𝕜 := 𝕜) N v)) + angularYosida (𝕜 := 𝕜) N (K (angularYosida (𝕜 := 𝕜) N v))
  rw [smul_sub, ← hres]
  abel

end ContinuousFlexibility.Analysis
