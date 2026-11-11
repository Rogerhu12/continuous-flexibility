import ContinuousFlexibility.Analysis.AngularFrequency

/-!
# Self-adjointness of the maximal angular frequency operator

Testing the adjoint against a vector in one spectral summand determines
each of its coefficients.  Consequently its domain is precisely the
maximal square-summability domain of the integer-frequency multiplier.
The proof permits arbitrary Hilbert spaces as spectral summands.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped ENNReal Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

theorem angularFrequency_single_mem (n : ℕ) (x : E n) :
    lp.single 2 n x ∈ angularFrequencyDomain (𝕜 := 𝕜) := by
  change Memℓp (fun m : ℕ => ((m : ℝ) : 𝕜) • lp.single 2 n x m) 2
  convert lp.memℓp (lp.single 2 n (((n : ℝ) : 𝕜) • x)) using 1
  funext m
  by_cases hmn : m = n
  · subst m
    simp only [lp.single_apply_self]
  · simp only [lp.single_apply_ne _ _ _ hmn, smul_zero]

theorem angularFrequency_single (n : ℕ) (x : E n) :
    angularFrequency (𝕜 := 𝕜) ⟨lp.single 2 n x, angularFrequency_single_mem n x⟩ =
      lp.single 2 n (((n : ℝ) : 𝕜) • x) := by
  ext m
  rw [angularFrequency_apply]
  by_cases hmn : m = n
  · subst m
    simp only [lp.single_apply_self]
  · simp only [lp.single_apply_ne _ _ _ hmn, smul_zero]

theorem angularFrequencyDomain_dense :
    Dense (angularFrequencyDomain (𝕜 := 𝕜) (E := E) : Set (lp E 2)) := by
  intro v
  have hmem : v ∈ (angularFrequencyDomain (𝕜 := 𝕜) (E := E)).topologicalClosure := by
    apply (angularFrequencyDomain (𝕜 := 𝕜) (E := E)).isClosed_topologicalClosure.mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v)
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro n _
    exact (angularFrequencyDomain (𝕜 := 𝕜) (E := E)).le_topologicalClosure
      (angularFrequency_single_mem n (v n))
  have hmem' : v ∈ ((angularFrequencyDomain (𝕜 := 𝕜) (E := E)).topologicalClosure :
      Set (lp E 2)) := hmem
  rw [Submodule.topologicalClosure_coe] at hmem'
  exact hmem'

theorem angularFrequency_isFormalAdjoint :
    (angularFrequency (𝕜 := 𝕜) (E := E)).IsFormalAdjoint
      (angularFrequency (𝕜 := 𝕜) (E := E)) := by
  intro x y
  calc
    inner 𝕜 (angularFrequency (𝕜 := 𝕜) x) (y : lp E 2) =
        ∑' n, inner 𝕜 (angularFrequency (𝕜 := 𝕜) x n) ((y : lp E 2) n) :=
      lp.inner_eq_tsum _ _
    _ = ∑' n, inner 𝕜 ((x : lp E 2) n) (angularFrequency (𝕜 := 𝕜) y n) := by
      apply tsum_congr
      intro n
      rw [angularFrequency_apply, angularFrequency_apply]
      simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    _ = inner 𝕜 (x : lp E 2) (angularFrequency (𝕜 := 𝕜) y) :=
      (lp.inner_eq_tsum _ _).symm

variable [∀ n, CompleteSpace (E n)]

theorem angularFrequency_adjoint_apply
    (x : (angularFrequency (𝕜 := 𝕜) (E := E)).adjoint.domain) (n : ℕ) :
    (angularFrequency (𝕜 := 𝕜) (E := E)).adjoint x n =
      ((n : ℝ) : 𝕜) • (x : lp E 2) n := by
  apply ext_inner_right 𝕜
  intro y
  have h := LinearPMap.adjoint_isFormalAdjoint
    (T := angularFrequency (𝕜 := 𝕜) (E := E)) angularFrequencyDomain_dense
    x ⟨lp.single 2 n y, angularFrequency_single_mem n y⟩
  simpa only [angularFrequency_single, lp.inner_single_right,
    inner_smul_left, inner_smul_right, RCLike.conj_ofReal] using h

theorem angularFrequency_adjoint_domain_le :
    (angularFrequency (𝕜 := 𝕜) (E := E)).adjoint.domain ≤
      angularFrequencyDomain (𝕜 := 𝕜) (E := E) := by
  intro x hx
  change Memℓp (fun n : ℕ => ((n : ℝ) : 𝕜) • x n) 2
  convert lp.memℓp ((angularFrequency (𝕜 := 𝕜) (E := E)).adjoint ⟨x, hx⟩) using 1
  funext n
  exact (angularFrequency_adjoint_apply ⟨x, hx⟩ n).symm

/-- The integer-frequency diagonal is genuinely self-adjoint as an
unbounded `LinearPMap`, on its maximal weighted Hilbert-space domain. -/
theorem angularFrequency_isSelfAdjoint :
    IsSelfAdjoint (angularFrequency (𝕜 := 𝕜) (E := E)) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.ext
  · apply Submodule.ext
    intro x
    constructor
    · exact angularFrequency_adjoint_domain_le
    · intro hx
      apply LinearPMap.mem_adjoint_domain_of_exists
        (T := angularFrequency (𝕜 := 𝕜) (E := E))
      refine ⟨angularFrequency (𝕜 := 𝕜) ⟨x, hx⟩, ?_⟩
      intro y
      exact angularFrequency_isFormalAdjoint ⟨x, hx⟩ y
  · intro x hxadj hx
    ext n
    rw [angularFrequency_adjoint_apply, angularFrequency_apply]

theorem angularFrequency_isClosed :
    (angularFrequency (𝕜 := 𝕜) (E := E)).IsClosed :=
  angularFrequency_isSelfAdjoint.isClosed

end ContinuousFlexibility.Analysis
