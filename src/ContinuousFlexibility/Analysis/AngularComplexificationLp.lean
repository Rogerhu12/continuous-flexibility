module

public import ContinuousFlexibility.Analysis.AngularComplexification
public import ContinuousFlexibility.Analysis.AngularFrequency

/-!
# Complexification commutes with angular Hilbert sums

Complexifying a Hilbert sum is isometrically equivalent to taking the
Hilbert sum of the complexified fibers.  Real spectral multipliers commute
with this identification.  In particular their domains are characterized
by the two real components and their squared norms add exactly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.AngularComplexification

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℝ (E n)]

/-- Real parts of a vector in the Hilbert sum of complexifications. -/
def lpRe (v : lp (fun n => AngularComplexification (E n)) 2) : lp E 2 :=
  ⟨fun n => (v n).re, (lp.memℓp v).mono' (fun n => norm_re_le (v n))⟩

/-- Imaginary parts of a vector in the Hilbert sum of complexifications. -/
def lpIm (v : lp (fun n => AngularComplexification (E n)) 2) : lp E 2 :=
  ⟨fun n => (v n).im, (lp.memℓp v).mono' (fun n => norm_im_le (v n))⟩

@[simp] theorem lpRe_apply (v : lp (fun n => AngularComplexification (E n)) 2) (n : ℕ) :
    lpRe v n = (v n).re := rfl

@[simp] theorem lpIm_apply (v : lp (fun n => AngularComplexification (E n)) 2) (n : ℕ) :
    lpIm v n = (v n).im := rfl

/-- Pair two real Hilbert-sum vectors coordinate by coordinate. -/
def lpMk (x y : lp E 2) : lp (fun n => AngularComplexification (E n)) 2 :=
  ⟨fun n => mk (x n) (y n), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_sq, re_mk, im_mk] using
      (angular_summable_norm_sq x).add (angular_summable_norm_sq y)⟩

@[simp] theorem lpMk_apply (x y : lp E 2) (n : ℕ) : lpMk x y n = mk (x n) (y n) := rfl

@[simp] theorem lpRe_lpMk (x y : lp E 2) : lpRe (lpMk x y) = x := by
  apply lp.ext
  funext n
  simp only [lpRe_apply, lpMk_apply, re_mk]

@[simp] theorem lpIm_lpMk (x y : lp E 2) : lpIm (lpMk x y) = y := by
  apply lp.ext
  funext n
  simp only [lpIm_apply, lpMk_apply, im_mk]

@[simp] theorem lpMk_re_im (v : lp (fun n => AngularComplexification (E n)) 2) :
    lpMk (lpRe v) (lpIm v) = v := by
  apply lp.ext
  funext n
  simp only [lpMk_apply, lpRe_apply, lpIm_apply, mk_re_im]

/-- The norm-square identity for coordinatewise complexification. -/
theorem norm_lpMk_sq (x y : lp E 2) : ‖lpMk x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [← angular_tsum_norm_sq (lpMk x y)]
  simp only [lpMk_apply, norm_sq, re_mk, im_mk]
  rw [Summable.tsum_add (angular_summable_norm_sq x) (angular_summable_norm_sq y),
    angular_tsum_norm_sq, angular_tsum_norm_sq]

theorem norm_lpMk (x y : lp E 2) : ‖lpMk x y‖ = ‖mk x y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_lpMk_sq, norm_sq, re_mk, im_mk]

@[simp] theorem norm_lpMk_zero (x : lp E 2) : ‖lpMk x 0‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_lpMk_sq, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

/-- Complexification commutes with a Hilbert sum, with no change of norm. -/
def lpEquiv : AngularComplexification (lp E 2) ≃ₗᵢ[ℂ]
    lp (fun n => AngularComplexification (E n)) 2 where
  toFun u := lpMk u.re u.im
  invFun v := mk (lpRe v) (lpIm v)
  left_inv u := by
    apply AngularComplexification.ext
    · simp only [re_mk, lpRe_lpMk]
    · simp only [im_mk, lpIm_lpMk]
  right_inv v := by
    simpa only [re_mk, im_mk] using lpMk_re_im v
  map_add' u v := by
    apply lp.ext
    funext n
    apply AngularComplexification.ext <;>
      simp only [lpMk_apply, re_mk, im_mk, re_add, im_add, lp.coeFn_add, Pi.add_apply]
  map_smul' z u := by
    apply lp.ext
    funext n
    apply AngularComplexification.ext <;>
      simp only [lpMk_apply, re_mk, im_mk, re_smul, im_smul,
        lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
        RingHom.id_apply]
  norm_map' u := by
    change ‖lpMk u.re u.im‖ = ‖u‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_lpMk_sq, norm_sq]

@[simp] theorem lpEquiv_apply (u : AngularComplexification (lp E 2)) :
    lpEquiv u = lpMk u.re u.im := rfl

@[simp] theorem lpEquiv_symm_apply (v : lp (fun n => AngularComplexification (E n)) 2) :
    lpEquiv.symm v = mk (lpRe v) (lpIm v) := by
  apply lpEquiv.symm_apply_eq.mpr
  simp only [lpEquiv_apply, re_mk, im_mk, lpMk_re_im]

/-- A real spectral domain on the real component follows from the complex domain. -/
theorem memAngularWeight_lpRe {w : ℕ → ℝ}
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    MemAngularWeight (𝕜 := ℝ) w (lpRe v) := by
  apply Memℓp.mono' hv
  intro n
  simpa only [lpRe_apply, RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id,
    id_eq, ofReal_smul, re_real_smul] using
    norm_re_le ((w n : ℂ) • v n)

/-- A real spectral domain on the imaginary component follows from the complex domain. -/
theorem memAngularWeight_lpIm {w : ℕ → ℝ}
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    MemAngularWeight (𝕜 := ℝ) w (lpIm v) := by
  apply Memℓp.mono' hv
  intro n
  simpa only [lpIm_apply, RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id,
    id_eq, ofReal_smul, im_real_smul] using
    norm_im_le ((w n : ℂ) • v n)

/-- Pairing two real weighted vectors gives a complex weighted vector. -/
theorem memAngularWeight_lpMk {w : ℕ → ℝ} {x y : lp E 2}
    (hx : MemAngularWeight (𝕜 := ℝ) w x) (hy : MemAngularWeight (𝕜 := ℝ) w y) :
    MemAngularWeight (𝕜 := ℂ) w (lpMk x y) := by
  have hpair := lp.memℓp
    (lpMk (angularMultiplierVector w x hx) (angularMultiplierVector w y hy))
  have heq : (fun n => (w n : ℂ) • lpMk x y n) =
      fun n => lpMk (angularMultiplierVector w x hx) (angularMultiplierVector w y hy) n := by
    funext n
    apply AngularComplexification.ext <;>
      simp only [lpMk_apply, re_mk, im_mk, ofReal_smul, re_real_smul, im_real_smul,
        angularMultiplierVector_apply, RCLike.ofReal_real_eq_id, id_eq]
  change Memℓp (fun n => (w n : ℂ) • lpMk x y n) 2
  rw [heq]
  exact hpair

/-- Complex spectral-domain membership is exactly membership of both real components. -/
theorem memAngularWeight_iff {w : ℕ → ℝ}
    {v : lp (fun n => AngularComplexification (E n)) 2} :
    MemAngularWeight (𝕜 := ℂ) w v ↔
      MemAngularWeight (𝕜 := ℝ) w (lpRe v) ∧
      MemAngularWeight (𝕜 := ℝ) w (lpIm v) := by
  refine ⟨fun hv => ⟨memAngularWeight_lpRe hv, memAngularWeight_lpIm hv⟩, ?_⟩
  rintro ⟨hre, him⟩
  simpa only [lpMk_re_im] using memAngularWeight_lpMk hre him

/-- A real multiplier commutes with pairing the two real components. -/
theorem angularMultiplierVector_eq_lpMk {w : ℕ → ℝ}
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    angularMultiplierVector w v hv =
      lpMk (angularMultiplierVector w (lpRe v) (memAngularWeight_lpRe hv))
        (angularMultiplierVector w (lpIm v) (memAngularWeight_lpIm hv)) := by
  apply lp.ext
  funext n
  apply AngularComplexification.ext <;>
    simp only [angularMultiplierVector_apply, lpMk_apply, re_mk, im_mk,
      lpRe_apply, lpIm_apply, RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_real_eq_id,
      id_eq, ofReal_smul, re_real_smul, im_real_smul]

/-- The exact squared weighted norm splits into the two real squared norms. -/
theorem angularWeightNorm_sq_eq {w : ℕ → ℝ}
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    angularWeightNorm (𝕜 := ℂ) w v ^ 2 =
      angularWeightNorm (𝕜 := ℝ) w (lpRe v) ^ 2 +
      angularWeightNorm (𝕜 := ℝ) w (lpIm v) ^ 2 := by
  rw [← norm_angularMultiplierVector w v hv, angularMultiplierVector_eq_lpMk hv,
    norm_lpMk_sq, norm_angularMultiplierVector, norm_angularMultiplierVector]

theorem memAngularSobolev_iff {p : ℕ}
    {v : lp (fun n => AngularComplexification (E n)) 2} :
    MemAngularSobolev (𝕜 := ℂ) p v ↔
      MemAngularSobolev (𝕜 := ℝ) p (lpRe v) ∧
      MemAngularSobolev (𝕜 := ℝ) p (lpIm v) := memAngularWeight_iff

theorem angularSobolevNorm_sq_eq {p : ℕ}
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularSobolev (𝕜 := ℂ) p v) :
    angularSobolevNorm (𝕜 := ℂ) p v ^ 2 =
      angularSobolevNorm (𝕜 := ℝ) p (lpRe v) ^ 2 +
      angularSobolevNorm (𝕜 := ℝ) p (lpIm v) ^ 2 := angularWeightNorm_sq_eq hv

/-- The original real Hilbert sum embeds isometrically in the complex sum. -/
def lpOfReal : lp E 2 →ₗᵢ[ℝ] lp (fun n => AngularComplexification (E n)) 2 where
  toFun x := lpMk x 0
  map_add' x y := by
    apply lp.ext
    funext n
    apply AngularComplexification.ext <;>
      simp only [lpMk_apply, lp.coeFn_add, lp.coeFn_zero, Pi.add_apply, Pi.zero_apply,
        re_mk, im_mk, re_add, im_add, add_zero]
  map_smul' r x := by
    apply lp.ext
    funext n
    apply AngularComplexification.ext <;>
      simp only [lpMk_apply, lp.coeFn_smul, lp.coeFn_zero, Pi.smul_apply, Pi.zero_apply,
        re_mk, im_mk, re_real_smul, im_real_smul, smul_zero, RingHom.id_apply]
  norm_map' := norm_lpMk_zero

@[simp] theorem lpOfReal_apply (x : lp E 2) : lpOfReal x = lpMk x 0 := rfl
@[simp] theorem lpRe_lpOfReal (x : lp E 2) : lpRe (lpOfReal x) = x := lpRe_lpMk x 0
@[simp] theorem lpIm_lpOfReal (x : lp E 2) : lpIm (lpOfReal x) = 0 := lpIm_lpMk x 0
@[simp] theorem norm_lpOfReal (x : lp E 2) : ‖lpOfReal x‖ = ‖x‖ := lpOfReal.norm_map x

section Operators

variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
  [∀ n, InnerProductSpace ℝ (F n)]
variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]

/-- Extension of an operator directly to the complexified spectral fibers. -/
def lpExtend (T : lp E 2 →L[ℝ] lp F 2) :
    lp (fun n => AngularComplexification (E n)) 2 →L[ℂ]
      lp (fun n => AngularComplexification (F n)) 2 :=
  (lpEquiv (E := F)).toLinearIsometry.toContinuousLinearMap.comp
    ((extend T).comp (lpEquiv (E := E)).symm.toLinearIsometry.toContinuousLinearMap)

@[simp] theorem lpExtend_apply (T : lp E 2 →L[ℝ] lp F 2)
    (v : lp (fun n => AngularComplexification (E n)) 2) :
    lpExtend T v = lpMk (T (lpRe v)) (T (lpIm v)) := by
  unfold lpExtend
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, lpEquiv_apply, lpEquiv_symm_apply,
    extend_apply, re_mk, im_mk]

@[simp] theorem lpRe_lpExtend (T : lp E 2 →L[ℝ] lp F 2)
    (v : lp (fun n => AngularComplexification (E n)) 2) :
    lpRe (lpExtend T v) = T (lpRe v) := by rw [lpExtend_apply, lpRe_lpMk]

@[simp] theorem lpIm_lpExtend (T : lp E 2 →L[ℝ] lp F 2)
    (v : lp (fun n => AngularComplexification (E n)) 2) :
    lpIm (lpExtend T v) = T (lpIm v) := by rw [lpExtend_apply, lpIm_lpMk]

@[simp] theorem lpExtend_lpOfReal (T : lp E 2 →L[ℝ] lp F 2) (x : lp E 2) :
    lpExtend T (lpOfReal x) = lpOfReal (T x) := by
  rw [lpExtend_apply, lpRe_lpOfReal, lpIm_lpOfReal, map_zero, lpOfReal_apply]

/-- Extending an operator to the complex spectral sum preserves its norm. -/
@[simp] theorem norm_lpExtend (T : lp E 2 →L[ℝ] lp F 2) : ‖lpExtend T‖ = ‖T‖ := by
  apply le_antisymm
  · apply (lpExtend T).opNorm_le_bound (norm_nonneg T)
    intro v
    have h := (extend T).le_opNorm ((lpEquiv (E := E)).symm v)
    simpa only [lpEquiv_symm_apply, extend_apply, re_mk, im_mk,
      norm_extend, ← norm_lpMk, lpMk_re_im, lpExtend_apply] using h
  · apply T.opNorm_le_bound (norm_nonneg (lpExtend T))
    intro x
    simpa only [lpExtend_lpOfReal, norm_lpOfReal] using
      (lpExtend T).le_opNorm (lpOfReal x)

@[simp] theorem lpExtend_id :
    lpExtend (ContinuousLinearMap.id ℝ (lp E 2)) =
      ContinuousLinearMap.id ℂ (lp (fun n => AngularComplexification (E n)) 2) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [lpExtend_apply, ContinuousLinearMap.id_apply, lpMk_re_im]

@[simp] theorem lpExtend_comp (S : lp F 2 →L[ℝ] lp G 2) (T : lp E 2 →L[ℝ] lp F 2) :
    lpExtend (S.comp T) = (lpExtend S).comp (lpExtend T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [lpExtend_apply, ContinuousLinearMap.comp_apply, lpRe_lpMk, lpIm_lpMk]

@[simp] theorem lpExtend_add (S T : lp E 2 →L[ℝ] lp F 2) :
    lpExtend (S + T) = lpExtend S + lpExtend T := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  apply AngularComplexification.ext <;>
    simp only [lpExtend_apply, ContinuousLinearMap.add_apply, lpMk_apply, lp.coeFn_add,
      Pi.add_apply, re_mk, im_mk, re_add, im_add]

@[simp] theorem lpExtend_sub (S T : lp E 2 →L[ℝ] lp F 2) :
    lpExtend (S - T) = lpExtend S - lpExtend T := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  apply AngularComplexification.ext <;>
    simp only [lpExtend_apply, ContinuousLinearMap.sub_apply, lpMk_apply, lp.coeFn_sub,
      Pi.sub_apply, re_mk, im_mk, re_sub, im_sub]

/-- Preservation of a real multiplier domain transfers to the complex sum. -/
theorem memAngularWeight_lpExtend (T : lp E 2 →L[ℝ] lp F 2) {w z : ℕ → ℝ}
    (hT : ∀ x, MemAngularWeight (𝕜 := ℝ) w x → MemAngularWeight (𝕜 := ℝ) z (T x))
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    MemAngularWeight (𝕜 := ℂ) z (lpExtend T v) := by
  rw [lpExtend_apply]
  exact memAngularWeight_lpMk (hT _ (memAngularWeight_lpRe hv))
    (hT _ (memAngularWeight_lpIm hv))

/-- A two-term estimate for weighted real operators transfers without changing
either coefficient, including the coefficient of the unweighted norm. -/
theorem angularWeightNorm_lpExtend_le (T : lp E 2 →L[ℝ] lp F 2) {w z : ℕ → ℝ}
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hT : ∀ x, MemAngularWeight (𝕜 := ℝ) w x → MemAngularWeight (𝕜 := ℝ) z (T x))
    (hbound : ∀ x, MemAngularWeight (𝕜 := ℝ) w x →
      angularWeightNorm (𝕜 := ℝ) z (T x) ≤ a * angularWeightNorm (𝕜 := ℝ) w x + c * ‖x‖)
    {v : lp (fun n => AngularComplexification (E n)) 2}
    (hv : MemAngularWeight (𝕜 := ℂ) w v) :
    angularWeightNorm (𝕜 := ℂ) z (lpExtend T v) ≤
      a * angularWeightNorm (𝕜 := ℂ) w v + c * ‖v‖ := by
  have hre := memAngularWeight_lpRe hv
  have him := memAngularWeight_lpIm hv
  have hout := memAngularWeight_lpExtend T hT hv
  have hleft := hbound (lpRe v) hre
  have hright := hbound (lpIm v) him
  rw [← norm_angularMultiplierVector z _ (hT _ hre),
    ← norm_angularMultiplierVector w _ hre] at hleft
  rw [← norm_angularMultiplierVector z _ (hT _ him),
    ← norm_angularMultiplierVector w _ him] at hright
  have h := norm_mk_le_two_term ha hc hleft hright
  rw [← norm_angularMultiplierVector z _ hout, angularMultiplierVector_eq_lpMk hout,
    norm_lpMk]
  simp only [lpRe_lpExtend, lpIm_lpExtend]
  rw [← norm_angularMultiplierVector w _ hv, angularMultiplierVector_eq_lpMk hv, norm_lpMk]
  simpa only [← norm_lpMk, lpMk_re_im] using h

end Operators

end ContinuousFlexibility.Analysis.AngularComplexification
