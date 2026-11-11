import ContinuousFlexibility.Analysis.AngularYosida
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Angular regularity of a bounded inverse

The first derivative is obtained from bounded Yosida approximations and
the lower semicontinuity of the Hilbert-sum norm.  Higher regularity then
follows by applying the already proved inverse regularity to the first
commuted equation.  No domain preservation of the inverse is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter Set
open scoped ENNReal Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

/-- Yosida regularization proves that the bounded inverse preserves the
first angular domain. -/
theorem angularInverse_mem_sobolev_one (R K B : lp E 2 →L[𝕜] lp E 2)
    (hR : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      R v ∈ angularFrequencyDomain (𝕜 := 𝕜))
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (R v) = R (angularDerivative (𝕜 := 𝕜) v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f)
    {f : lp E 2} (hf : MemAngularSobolev (𝕜 := 𝕜) 1 f) :
    MemAngularSobolev (𝕜 := 𝕜) 1 (B f) := by
  let u : lp E 2 := B f
  have hfdom := mem_angularFrequencyDomain_of_sobolev hf
  have heq (N : ℕ) : angularYosidaDerivative (𝕜 := 𝕜) N u =
      B (angularYosidaDerivative (𝕜 := 𝕜) N f - angularYosida (𝕜 := 𝕜) N (K (angularYosida (𝕜 := 𝕜) N u))) := by
    have h := congrArg (angularYosidaDerivative (𝕜 := 𝕜) N) (hright f)
    rw [map_add, angularYosidaDerivative_commutator R K hR hcomm] at h
    have h' : angularYosidaDerivative (𝕜 := 𝕜) N u +
        R (angularYosidaDerivative (𝕜 := 𝕜) N u) =
        angularYosidaDerivative (𝕜 := 𝕜) N f - angularYosida (𝕜 := 𝕜) N (K (angularYosida (𝕜 := 𝕜) N u)) := by
      apply eq_sub_of_add_eq
      simpa only [u, add_assoc] using h
    rw [← h', hleft]
  have hbound (N : ℕ) : ‖angularYosidaDerivative (𝕜 := 𝕜) N u‖ ≤
      ‖B‖ * (‖angularDerivative (𝕜 := 𝕜) f‖ + ‖K‖ * ‖u‖) := by
    rw [heq N]
    apply (B.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
    apply (norm_sub_le _ _).trans
    apply add_le_add (norm_angularYosidaDerivative_le N hfdom)
    calc
      ‖angularYosida (𝕜 := 𝕜) N (K (angularYosida (𝕜 := 𝕜) N u))‖ ≤
          ‖K (angularYosida (𝕜 := 𝕜) N u)‖ := norm_angularYosida_le _ _
      _ ≤ ‖K‖ * ‖angularYosida (𝕜 := 𝕜) N u‖ := K.le_opNorm _
      _ ≤ ‖K‖ * ‖u‖ := mul_le_mul_of_nonneg_left (norm_angularYosida_le _ _) (norm_nonneg K)
  have hbdd : Bornology.IsBounded
      (Set.range (fun N => angularYosidaDerivative (𝕜 := 𝕜) N u)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖B‖ * (‖angularDerivative (𝕜 := 𝕜) f‖ + ‖K‖ * ‖u‖), ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hbound N
  have hlim : Tendsto (fun N => (angularYosidaDerivative (𝕜 := 𝕜) N u : ∀ n, E n))
      atTop (𝓝 (fun n => ((n : ℝ) : 𝕜) • u n)) := by
    apply tendsto_pi_nhds.mpr
    intro n
    have hreal : Tendsto (fun N => (n : ℝ) * angularYosidaWeight N n)
        atTop (𝓝 (n : ℝ)) := by
      simpa only [mul_one] using
        (tendsto_const_nhds (x := (n : ℝ))).mul (angularYosidaWeight_tendsto n)
    have hscalar : Tendsto (fun N => (((n : ℝ) * angularYosidaWeight N n : ℝ) : 𝕜))
        atTop (𝓝 ((n : ℝ) : 𝕜)) :=
      RCLike.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [angularYosidaDerivative_apply] using
      hscalar.smul (tendsto_const_nhds (x := u n))
  exact (memAngularSobolev_one_iff_frequency (B f)).mpr
    (lp.memℓp_of_tendsto hbdd hlim)

/-- The first commuted inverse equation, once the first domain has been
obtained by the preceding theorem. -/
theorem angularInverse_derivative_eq (R K B : lp E 2 →L[𝕜] lp E 2)
    (hR : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      R v ∈ angularFrequencyDomain (𝕜 := 𝕜))
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (R v) = R (angularDerivative (𝕜 := 𝕜) v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f)
    {f : lp E 2} (hu : B f ∈ angularFrequencyDomain (𝕜 := 𝕜)) :
    angularDerivative (𝕜 := 𝕜) (B f) =
      B (angularDerivative (𝕜 := 𝕜) f - K (B f)) := by
  have h := congrArg (angularDerivative (𝕜 := 𝕜)) (hright f)
  rw [angularDerivative_add hu (hR _ hu), hcomm _ hu] at h
  have h' : angularDerivative (𝕜 := 𝕜) (B f) + R (angularDerivative (𝕜 := 𝕜) (B f)) =
      angularDerivative (𝕜 := 𝕜) f - K (B f) := by
    apply eq_sub_of_add_eq
    simpa only [add_assoc] using h
  rw [← h', hleft]

/-- A bounded inverse preserves every angular Sobolev domain if the
commutator does so.  The only assumption on `R` needed in this proof is
preservation of the first frequency domain. -/
theorem angularInverse_preserves_sobolev (R K B : lp E 2 →L[𝕜] lp E 2)
    (hR : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      R v ∈ angularFrequencyDomain (𝕜 := 𝕜))
    (hK : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (K v))
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (R v) = R (angularDerivative (𝕜 := 𝕜) v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    ∀ p f, MemAngularSobolev (𝕜 := 𝕜) p f → MemAngularSobolev (𝕜 := 𝕜) p (B f) := by
  intro p
  induction p with
  | zero =>
      intro f _
      exact memAngularSobolev_zero _
  | succ p ih =>
      intro f hf
      have hu : MemAngularSobolev (𝕜 := 𝕜) p (B f) := ih f (hf.of_le (by omega))
      have hu1 : MemAngularSobolev (𝕜 := 𝕜) 1 (B f) :=
        angularInverse_mem_sobolev_one R K B hR hcomm hleft hright (hf.of_le (by omega))
      have hudom := mem_angularFrequencyDomain_of_sobolev hu1
      have hsource : MemAngularSobolev (𝕜 := 𝕜) p
          (angularDerivative (𝕜 := 𝕜) f - K (B f)) :=
        MemAngularWeight.sub hf.derivative (hK p (B f) hu)
      apply memAngularSobolev_succ_of_derivative hu hudom
      rw [angularInverse_derivative_eq R K B hR hcomm hleft hright hudom]
      exact ih _ hsource

end ContinuousFlexibility.Analysis
