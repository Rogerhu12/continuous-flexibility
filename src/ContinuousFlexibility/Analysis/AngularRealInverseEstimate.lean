module

public import ContinuousFlexibility.Analysis.AngularComplexificationLp
public import ContinuousFlexibility.Analysis.AngularInverseEstimate

/-!
# The angular inverse estimate over the reals

Complexification preserves every norm and coefficient in the hypotheses.
The commutator and inverse identities transfer by their two real
components.  Applying the complex theorem to the real-axis embedding
therefore gives the same tame constant for arbitrary real Hilbert fibers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped NNReal

namespace AngularComplexification

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℝ (E n)]

theorem lp_eq_of_re_im {u v : lp (fun n => AngularComplexification (E n)) 2}
    (hre : lpRe u = lpRe v) (him : lpIm u = lpIm v) : u = v := by
  rw [← lpMk_re_im u, ← lpMk_re_im v, hre, him]

@[simp] theorem lpRe_add (u v : lp (fun n => AngularComplexification (E n)) 2) :
    lpRe (u + v) = lpRe u + lpRe v := by
  apply lp.ext
  funext n
  simp only [lpRe_apply, lp.coeFn_add, Pi.add_apply, re_add]

@[simp] theorem lpIm_add (u v : lp (fun n => AngularComplexification (E n)) 2) :
    lpIm (u + v) = lpIm u + lpIm v := by
  apply lp.ext
  funext n
  simp only [lpIm_apply, lp.coeFn_add, Pi.add_apply, im_add]

/-- The real-axis embedding preserves every real multiplier domain. -/
theorem memAngularWeight_lpOfReal {w : ℕ → ℝ} {x : lp E 2} :
    MemAngularWeight (𝕜 := ℂ) w (lpOfReal x) ↔
      MemAngularWeight (𝕜 := ℝ) w x := by
  rw [memAngularWeight_iff, lpRe_lpOfReal, lpIm_lpOfReal]
  exact ⟨fun h => h.1, fun h => ⟨h, MemAngularWeight.zero w⟩⟩

/-- Weighted norms of real-axis vectors are unchanged, including their
values before imposing a weighted-domain hypothesis. -/
@[simp] theorem angularWeightNorm_lpOfReal (w : ℕ → ℝ) (x : lp E 2) :
    angularWeightNorm (𝕜 := ℂ) w (lpOfReal x) =
      angularWeightNorm (𝕜 := ℝ) w x := by
  unfold angularWeightNorm
  congr 1
  apply tsum_congr
  intro n
  simp only [norm_smul, RCLike.norm_ofReal, lpOfReal_apply, lpMk_apply,
    lp.coeFn_zero, Pi.zero_apply, ← ofReal_apply, norm_ofReal]

theorem memAngularSobolev_lpOfReal {p : ℕ} {x : lp E 2} :
    MemAngularSobolev (𝕜 := ℂ) p (lpOfReal x) ↔
      MemAngularSobolev (𝕜 := ℝ) p x := memAngularWeight_lpOfReal

@[simp] theorem angularSobolevNorm_lpOfReal (p : ℕ) (x : lp E 2) :
    angularSobolevNorm (𝕜 := ℂ) p (lpOfReal x) =
      angularSobolevNorm (𝕜 := ℝ) p x := angularWeightNorm_lpOfReal _ _

/-- Real parts commute with the angular derivative on its domain. -/
theorem lpRe_angularDerivative {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : v ∈ angularFrequencyDomain (𝕜 := ℂ)) :
    lpRe (angularDerivative (𝕜 := ℂ) v) =
      angularDerivative (𝕜 := ℝ) (lpRe v) := by
  have hre : lpRe v ∈ angularFrequencyDomain (𝕜 := ℝ) :=
    memAngularWeight_lpRe hv
  apply lp.ext
  funext n
  simp only [lpRe_apply, angularDerivative_apply hv, angularDerivative_apply hre,
    RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id, id_eq,
    ofReal_smul, re_real_smul]

/-- Imaginary parts commute with the angular derivative on its domain. -/
theorem lpIm_angularDerivative {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : v ∈ angularFrequencyDomain (𝕜 := ℂ)) :
    lpIm (angularDerivative (𝕜 := ℂ) v) =
      angularDerivative (𝕜 := ℝ) (lpIm v) := by
  have him : lpIm v ∈ angularFrequencyDomain (𝕜 := ℝ) :=
    memAngularWeight_lpIm hv
  apply lp.ext
  funext n
  simp only [lpIm_apply, angularDerivative_apply hv, angularDerivative_apply him,
    RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id, id_eq,
    ofReal_smul, im_real_smul]

end AngularComplexification

open AngularComplexification

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℝ (E n)]

/-- The angular commutator inverse lemma on an arbitrary real Hilbert
spectral sum.  Its constant is exactly the one in the complex theorem,
and in particular is independent of the high-order error coefficient. -/
theorem angular_inverse_tame_real (R K B : lp E 2 →L[ℝ] lp E 2)
    (a c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, MemAngularSobolev (𝕜 := ℝ) p v →
      MemAngularSobolev (𝕜 := ℝ) p (R v))
    (hK : ∀ p v, MemAngularSobolev (𝕜 := ℝ) p v →
      MemAngularSobolev (𝕜 := ℝ) p (K v))
    (hbound : ∀ p v, MemAngularSobolev (𝕜 := ℝ) p v →
      angularSobolevNorm (𝕜 := ℝ) p (K v) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := ℝ) p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := ℝ) →
      angularDerivative (𝕜 := ℝ) (R v) = R (angularDerivative (𝕜 := ℝ) v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, MemAngularSobolev (𝕜 := ℝ) p f →
      MemAngularSobolev (𝕜 := ℝ) p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, MemAngularSobolev (𝕜 := ℝ) p f →
      angularSobolevNorm (𝕜 := ℝ) p (B f) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (angularSobolevNorm (𝕜 := ℝ) p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) := by
  have hRC : ∀ p v, MemAngularSobolev (𝕜 := ℂ) p v →
      MemAngularSobolev (𝕜 := ℂ) p (lpExtend R v) := by
    intro p v hv
    exact memAngularWeight_lpExtend R (hR p) hv
  have hKC : ∀ p v, MemAngularSobolev (𝕜 := ℂ) p v →
      MemAngularSobolev (𝕜 := ℂ) p (lpExtend K v) := by
    intro p v hv
    exact memAngularWeight_lpExtend K (hK p) hv
  have hboundC : ∀ p v, MemAngularSobolev (𝕜 := ℂ) p v →
      angularSobolevNorm (𝕜 := ℂ) p (lpExtend K v) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := ℂ) p v + (c p : ℝ) * ‖v‖ := by
    intro p v hv
    exact angularWeightNorm_lpExtend_le K (a p).coe_nonneg (c p).coe_nonneg
      (hK p) (hbound p) hv
  have hcommC : ∀ v, v ∈ angularFrequencyDomain (𝕜 := ℂ) →
      angularDerivative (𝕜 := ℂ) (lpExtend R v) =
        lpExtend R (angularDerivative (𝕜 := ℂ) v) + lpExtend K v := by
    intro v hv
    have hRv : lpExtend R v ∈ angularFrequencyDomain (𝕜 := ℂ) :=
      (memAngularSobolev_one_iff_frequency (𝕜 := ℂ) _).mp
        (hRC 1 v ((memAngularSobolev_one_iff_frequency (𝕜 := ℂ) _).mpr hv))
    apply lp_eq_of_re_im
    · simpa only [lpRe_angularDerivative hRv, lpRe_angularDerivative hv,
        lpRe_lpExtend, lpRe_add] using hcomm (lpRe v) (memAngularWeight_lpRe hv)
    · simpa only [lpIm_angularDerivative hRv, lpIm_angularDerivative hv,
        lpIm_lpExtend, lpIm_add] using hcomm (lpIm v) (memAngularWeight_lpIm hv)
  have hleftC : ∀ v, lpExtend B (v + lpExtend R v) = v := by
    intro v
    apply lp_eq_of_re_im <;>
      simp only [lpRe_lpExtend, lpIm_lpExtend, lpRe_add, lpIm_add, hleft]
  have hrightC : ∀ f, lpExtend B f + lpExtend R (lpExtend B f) = f := by
    intro f
    apply lp_eq_of_re_im <;>
      simp only [lpRe_lpExtend, lpIm_lpExtend, lpRe_add, lpIm_add, hright]
  obtain ⟨hreg, hestimate⟩ := angular_inverse_tame_complex
    (lpExtend R) (lpExtend K) (lpExtend B) a c ha hc hRC hKC hboundC hcommC hleftC hrightC
  constructor
  · intro p f hf
    simpa only [lpExtend_lpOfReal, memAngularSobolev_lpOfReal] using
      hreg p (lpOfReal f) (memAngularSobolev_lpOfReal.mpr hf)
  · intro p hp f hf
    simpa only [lpExtend_lpOfReal, angularSobolevNorm_lpOfReal, norm_lpOfReal,
      norm_lpExtend] using
      hestimate p hp (lpOfReal f) (memAngularSobolev_lpOfReal.mpr hf)

end ContinuousFlexibility.Analysis
