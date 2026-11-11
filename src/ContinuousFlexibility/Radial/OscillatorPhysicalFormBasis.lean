import ContinuousFlexibility.Radial.OscillatorWeakEnergy

/-!
# Hermite coordinates in the actual physical energy space

The ambient space is defined by a genuine weak derivative and actual
almost-everywhere multiplication by `jX`, before any spectral coordinates
are introduced. The positive weights here correspond to `Hosc + 1`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

def physicalHermiteWeight (j : ℝ) (n : ℕ) : ℝ := j * (2 * (n : ℝ) + 1) + 1

theorem physicalHermiteWeight_pos {j : ℝ} (hj : 0 < j) (n : ℕ) :
    0 < physicalHermiteWeight j n := by
  unfold physicalHermiteWeight
  positivity

theorem memLp_sq_mul_normalizedHermite {j : ℝ} (hj : 0 < j) (n : ℕ) :
    MemLp (fun x : ℝ => x ^ 2 * normalizedOscillatorHermite j n x) 2 volume := by
  convert (memLp_polynomialGaussian hj
    (Polynomial.X ^ 2 * oscillatorHermitePolynomial j n)).const_mul
      (oscillatorHermiteNorm j n)⁻¹ using 1
  funext x
  simp only [polynomialGaussian, normalizedOscillatorHermite, oscillatorHermiteMode,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv]
  ring

theorem memLp_second_deriv_normalizedHermite {j : ℝ} (hj : 0 < j) (n : ℕ) :
    MemLp (deriv (deriv (normalizedOscillatorHermite j n))) 2 volume := by
  convert ((memLp_sq_mul_normalizedHermite hj n).const_mul (j ^ 2)).sub
    ((normalizedOscillatorHermite_energyDomain hj n).2.1.const_mul
      (j * (2 * (n : ℝ) + 1))) using 1
  funext x
  simp only [Pi.sub_apply]
  have he := normalizedOscillatorHermite_equation hj n x
  unfold oscillatorExpression at he
  linear_combination -he

theorem physicalEnergy_inner_coordinates (j : ℝ) (u v : PhysicalEnergySpace j) :
    ⟪u, v⟫_ℝ =
      ⟪physicalEnergyBase j u, physicalEnergyBase j v⟫_ℝ +
      ⟪physicalEnergyDerivative j u, physicalEnergyDerivative j v⟫_ℝ +
      ⟪physicalEnergyPosition j u, physicalEnergyPosition j v⟫_ℝ := by
  change ⟪u.val, v.val⟫_ℝ = _
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_three]
  rfl

private theorem physical_inner_toLp {φ ψ : ℝ → ℝ}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    ⟪hφ.toLp φ, hψ.toLp ψ⟫_ℝ = ∫ x : ℝ, φ x * ψ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ, MemLp.coeFn_toLp hψ] with x hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The Hilbert norm on the physically defined space is exactly the
actual differential energy, not a spectral definition of that energy. -/
theorem physicalEnergyLift_inner (j : ℝ) {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ) :
    ⟪physicalEnergyLift j hφ, physicalEnergyLift j hψ⟫_ℝ =
      shiftedCentralEnergyPairing j φ ψ := by
  rw [physicalEnergy_inner_coordinates, physicalEnergyLift_base, physicalEnergyLift_base,
    physicalEnergyLift_derivative, physicalEnergyLift_derivative,
    physicalEnergyLift_position, physicalEnergyLift_position,
    physical_inner_toLp, physical_inner_toLp, physical_inner_toLp]
  have hw : (∫ x : ℝ, (j * x * φ x) * (j * x * ψ x)) =
      j ^ 2 * (∫ x : ℝ, (x * φ x) * (x * ψ x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  rw [hw]
  unfold shiftedCentralEnergyPairing oscillatorEnergyPairing
  ring

theorem physicalEnergyLift_norm_sq (j : ℝ) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) :
    ‖physicalEnergyLift j hψ‖ ^ 2 = shiftedCentralEnergyPairing j ψ ψ := by
  rw [← real_inner_self_eq_norm_sq, physicalEnergyLift_inner]

theorem physicalEnergyLift_inner_operator (j : ℝ) {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hHψ : MemLp (liouvilleSchrodinger (j ^ 2)
      centralRadius centralDensityRoot ψ) 2 volume) :
    ⟪physicalEnergyLift j hφ, physicalEnergyLift j hψ⟫_ℝ =
      ⟪hφ.2.1.toLp φ,
        hHψ.toLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) +
          centralEnergyShift j • hψ.2.1.toLp ψ⟫_ℝ := by
  rw [physicalEnergyLift_inner, ← central_shifted_form_pairing hφ hψ hHψ,
    inner_add_right, real_inner_smul_right, physical_inner_toLp, physical_inner_toLp]

theorem physicalEnergyLift_norm_sub_sq (j : ℝ) {φ ψ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ) (hψ : OscillatorEnergyDomain ψ)
    (hHφ : MemLp (liouvilleSchrodinger (j ^ 2)
      centralRadius centralDensityRoot φ) 2 volume)
    (hHψ : MemLp (liouvilleSchrodinger (j ^ 2)
      centralRadius centralDensityRoot ψ) 2 volume) :
    ‖physicalEnergyLift j hφ - physicalEnergyLift j hψ‖ ^ 2 =
      ⟪hφ.2.1.toLp φ - hψ.2.1.toLp ψ,
        (hHφ.toLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ) +
          centralEnergyShift j • hφ.2.1.toLp φ) -
        (hHψ.toLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ) +
          centralEnergyShift j • hψ.2.1.toLp ψ)⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    physicalEnergyLift_inner_operator j hφ hφ hHφ,
    physicalEnergyLift_inner_operator j hφ hψ hHψ,
    physicalEnergyLift_inner_operator j hψ hφ hHφ,
    physicalEnergyLift_inner_operator j hψ hψ hHψ]
  simp only [inner_sub_left, inner_sub_right]
  ring

theorem centralHermiteImage_memLp {j : ℝ} (hj : 0 < j) (n : ℕ) :
    MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (normalizedOscillatorHermite j n)) 2 volume := by
  convert ((normalizedOscillatorHermite_energyDomain hj n).2.1.const_mul
    (centralSpectralLevel j n)) using 1
  funext x
  exact central_normalizedHermite_spectralLevel hj n x

theorem centralHermiteImage_toLp {j : ℝ} (hj : 0 < j) (n : ℕ) :
    (centralHermiteImage_memLp hj n).toLp
      (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
        (normalizedOscillatorHermite j n)) =
      centralSpectralLevel j n • hermiteL2Vector hj n := by
  calc
    _ = ((normalizedOscillatorHermite_energyDomain hj n).2.1.const_smul
        (centralSpectralLevel j n)).toLp
        (centralSpectralLevel j n • normalizedOscillatorHermite j n) := by
      apply MemLp.toLp_congr
      exact Eventually.of_forall (fun x => central_normalizedHermite_spectralLevel hj n x)
    _ = _ := by rw [MemLp.toLp_const_smul]; rfl

def physicalHermiteLift {j : ℝ} (hj : 0 < j) (n : ℕ) : PhysicalEnergySpace j :=
  physicalEnergyLift j (normalizedOscillatorHermite_energyDomain hj n)

theorem physicalHermiteLift_inner {j : ℝ} (hj : 0 < j) (m n : ℕ) :
    ⟪physicalHermiteLift hj m, physicalHermiteLift hj n⟫_ℝ =
      if m = n then physicalHermiteWeight j n else 0 := by
  unfold physicalHermiteLift
  rw [physicalEnergyLift_inner_operator j _ _ (centralHermiteImage_memLp hj n),
    centralHermiteImage_toLp]
  change ⟪hermiteL2Vector hj m, centralSpectralLevel j n • hermiteL2Vector hj n +
    centralEnergyShift j • hermiteL2Vector hj n⟫_ℝ = _
  rw [← add_smul, real_inner_smul_right, hermiteL2Vector_inner, centralEnergyShift_level]
  simp only [physicalHermiteWeight, mul_ite, mul_one, mul_zero]

@[simp] theorem physicalHermiteLift_base {j : ℝ} (hj : 0 < j) (n : ℕ) :
    physicalEnergyBase j (physicalHermiteLift hj n) = hermiteL2Vector hj n := rfl

def physicalHermiteVector {j : ℝ} (hj : 0 < j) (n : ℕ) : PhysicalEnergySpace j :=
  (sqrt (physicalHermiteWeight j n))⁻¹ • physicalHermiteLift hj n

theorem physicalHermiteVector_inner {j : ℝ} (hj : 0 < j) (m n : ℕ) :
    ⟪physicalHermiteVector hj m, physicalHermiteVector hj n⟫_ℝ =
      if m = n then 1 else 0 := by
  unfold physicalHermiteVector
  rw [real_inner_smul_left, real_inner_smul_right, physicalHermiteLift_inner]
  by_cases hmn : m = n
  · subst m
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have hs := sq_sqrt (physicalHermiteWeight_pos hj n).le
    have hn := (sqrt_pos.mpr (physicalHermiteWeight_pos hj n)).ne'
    field_simp [hn]
    nlinarith only [hs]
  · simp [hmn]

theorem physicalHermiteVector_orthonormal {j : ℝ} (hj : 0 < j) :
    Orthonormal ℝ (physicalHermiteVector hj) :=
  orthonormal_iff_ite.mpr (physicalHermiteVector_inner hj)

@[simp] theorem physicalHermiteVector_base {j : ℝ} (hj : 0 < j) (n : ℕ) :
    physicalEnergyBase j (physicalHermiteVector hj n) =
      (sqrt (physicalHermiteWeight j n))⁻¹ • hermiteL2Vector hj n := by
  rw [physicalHermiteVector, map_smul, physicalHermiteLift_base]

private theorem physical_inner_toLp_right (u : HermiteL2)
    {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    ⟪u, hφ.toLp φ⟫_ℝ = ∫ x : ℝ, u x * φ x :=
  (real_inner_comm _ _).trans (physicalTestPairing_apply φ hφ u)

theorem physicalEnergy_position_pairing (j : ℝ) (z : PhysicalEnergySpace j)
    {φ : ℝ → ℝ} (hφ : OscillatorEnergyDomain φ) :
    Integrable (fun x : ℝ => physicalEnergyBase j z x * (j ^ 2 * x ^ 2 * φ x)) volume ∧
      (∫ x : ℝ, physicalEnergyPosition j z x * (j * x * φ x)) =
        ∫ x : ℝ, physicalEnergyBase j z x * (j ^ 2 * x ^ 2 * φ x) := by
  have hP : (physicalEnergyPosition j z : ℝ → ℝ) =ᵐ[volume]
      (fun x => j * x * physicalEnergyBase j z x) := z.property.2
  have hleft : Integrable (fun x : ℝ =>
      physicalEnergyPosition j z x * (j * x * φ x)) volume :=
    (Lp.memLp (physicalEnergyPosition j z)).integrable_mul
      (physicalEnergy_weighted_memLp j hφ)
  have heq : (fun x : ℝ => physicalEnergyPosition j z x * (j * x * φ x)) =ᵐ[volume]
      (fun x => physicalEnergyBase j z x * (j ^ 2 * x ^ 2 * φ x)) := by
    filter_upwards [hP] with x hx
    rw [hx]
    ring
  exact ⟨hleft.congr heq, integral_congr_ae heq⟩

/-- Only genuine compact tests are used: the weak derivative is tested
against the actual compactly supported first derivative of `φ`. -/
theorem physicalEnergy_inner_compact_operator (j : ℝ) (z : PhysicalEnergySpace j)
    (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ⟪z, physicalEnergyLift j (compactSmooth_energyDomain hs hc)⟫_ℝ =
      ⟪physicalEnergyBase j z,
        (compactSmooth_centralImage_memLp hs hc j).toLp
          (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ)⟫_ℝ +
      centralEnergyShift j * ⟪physicalEnergyBase j z,
        (compactSmooth_energyDomain hs hc).2.1.toLp φ⟫_ℝ := by
  let hφ := compactSmooth_energyDomain hs hc
  have hs' := (contDiff_infty_iff_deriv.mp hs).2
  have hφ'' : MemLp (deriv (deriv φ)) 2 volume :=
    (compactSmooth_energyDomain hs' hc.deriv).2.2.1
  have hD : (∫ x : ℝ, physicalEnergyDerivative j z x * deriv φ x) =
      -(∫ x : ℝ, physicalEnergyBase j z x * deriv (deriv φ) x) :=
    z.property.1 (deriv φ) hs' hc.deriv
  have hP := physicalEnergy_position_pairing j z hφ
  have hu := Lp.memLp (physicalEnergyBase j z)
  have huφ : Integrable (fun x : ℝ => physicalEnergyBase j z x * φ x) volume :=
    hu.integrable_mul hφ.2.1
  have huφ'' : Integrable (fun x : ℝ =>
      physicalEnergyBase j z x * deriv (deriv φ) x) volume := hu.integrable_mul hφ''
  have huH : Integrable (fun x : ℝ => physicalEnergyBase j z x *
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x) volume :=
    hu.integrable_mul (compactSmooth_centralImage_memLp hs hc j)
  have hshift : Integrable (fun x : ℝ =>
      centralEnergyShift j * (physicalEnergyBase j z x * φ x)) volume := huφ.const_mul _
  have hdiff : Integrable (fun x : ℝ => physicalEnergyBase j z x * φ x -
      physicalEnergyBase j z x * deriv (deriv φ) x) volume := huφ.sub huφ''
  have hHsum :
      (∫ x : ℝ, physicalEnergyBase j z x *
        liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x) +
        centralEnergyShift j * (∫ x : ℝ, physicalEnergyBase j z x * φ x) =
      (∫ x : ℝ, physicalEnergyBase j z x * φ x) -
        (∫ x : ℝ, physicalEnergyBase j z x * deriv (deriv φ) x) +
        (∫ x : ℝ, physicalEnergyBase j z x * (j ^ 2 * x ^ 2 * φ x)) := by
    calc
      _ = ∫ x : ℝ, physicalEnergyBase j z x *
          liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot φ x +
          centralEnergyShift j * (physicalEnergyBase j z x * φ x) := by
        rw [integral_add huH hshift, integral_const_mul]
      _ = ∫ x : ℝ, (physicalEnergyBase j z x * φ x -
          physicalEnergyBase j z x * deriv (deriv φ) x) +
          physicalEnergyBase j z x * (j ^ 2 * x ^ 2 * φ x) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only
        rw [central_liouvilleSchrodinger]
        unfold centralEnergyShift
        ring
      _ = _ := by rw [integral_add hdiff hP.1, integral_sub huφ huφ'']
  rw [physicalEnergy_inner_coordinates, physicalEnergyLift_base,
    physicalEnergyLift_derivative, physicalEnergyLift_position]
  simp only [physical_inner_toLp_right]
  rw [hD, hP.2]
  linarith [hHsum]

def physicalHermiteCutoffLift (j : ℝ) (n N : ℕ) : PhysicalEnergySpace j :=
  physicalEnergyLift j (compactSmooth_energyDomain
    (contDiff_compactHermiteFunction j n N) (compactHermiteFunction_hasCompactSupport j n N))

/-- Actual graph-norm cutoff convergence implies convergence in the
physically defined form norm through the proved differential energy. -/
theorem physicalHermiteCutoffLift_tendsto {j : ℝ} (hj : 0 < j) (n : ℕ) :
    Tendsto (physicalHermiteCutoffLift j n) atTop (𝓝 (physicalHermiteLift hj n)) := by
  have hu := compactHermiteFunction_tendsto_L2 hj n
  have hv := compactHermiteImage_tendsto_L2 hj n
  have hz := (hu.sub_const (hermiteL2Vector hj n)).inner (𝕜 := ℝ)
    ((hv.add (hu.const_smul (centralEnergyShift j))).sub_const
      (centralSpectralLevel j n • hermiteL2Vector hj n +
        centralEnergyShift j • hermiteL2Vector hj n))
  have heq : (fun N => ‖physicalHermiteCutoffLift j n N - physicalHermiteLift hj n‖ ^ 2) =
      (fun N => ⟪(compactHermiteFunction_memLp j n N).toLp
          (compactHermiteFunction j n N) - hermiteL2Vector hj n,
        ((compactHermiteImage_memLp j n N).toLp
          (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
            (compactHermiteFunction j n N)) +
          centralEnergyShift j • (compactHermiteFunction_memLp j n N).toLp
            (compactHermiteFunction j n N)) -
        (centralSpectralLevel j n • hermiteL2Vector hj n +
          centralEnergyShift j • hermiteL2Vector hj n)⟫_ℝ) := by
    funext N
    unfold physicalHermiteCutoffLift physicalHermiteLift
    rw [physicalEnergyLift_norm_sub_sq j _ _ (compactHermiteImage_memLp j n N)
      (centralHermiteImage_memLp hj n), centralHermiteImage_toLp]
    rfl
  have hnormsq : Tendsto
      (fun N => ‖physicalHermiteCutoffLift j n N - physicalHermiteLift hj n‖ ^ 2)
      atTop (𝓝 0) := by
    rw [heq]
    simpa only [sub_self, inner_zero_left] using hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm

/-- The pairing with every actual Hermite lift follows by a limit of
genuine compact tests in the physical energy norm. -/
theorem physicalEnergy_inner_hermite {j : ℝ} (hj : 0 < j)
    (z : PhysicalEnergySpace j) (n : ℕ) :
    ⟪z, physicalHermiteLift hj n⟫_ℝ =
      physicalHermiteWeight j n * hermiteCoefficient j (physicalEnergyBase j z) n := by
  have hleft : Tendsto (fun N => ⟪z, physicalHermiteCutoffLift j n N⟫_ℝ) atTop
      (𝓝 ⟪z, physicalHermiteLift hj n⟫_ℝ) :=
    tendsto_const_nhds.inner (physicalHermiteCutoffLift_tendsto hj n)
  have hH : Tendsto (fun N => ⟪physicalEnergyBase j z,
      (compactHermiteImage_memLp j n N).toLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
          (compactHermiteFunction j n N))⟫_ℝ) atTop
      (𝓝 ⟪physicalEnergyBase j z, centralSpectralLevel j n • hermiteL2Vector hj n⟫_ℝ) :=
    tendsto_const_nhds.inner (compactHermiteImage_tendsto_L2 hj n)
  have hu : Tendsto (fun N => ⟪physicalEnergyBase j z,
      (compactHermiteFunction_memLp j n N).toLp (compactHermiteFunction j n N)⟫_ℝ) atTop
      (𝓝 ⟪physicalEnergyBase j z, hermiteL2Vector hj n⟫_ℝ) :=
    tendsto_const_nhds.inner (compactHermiteFunction_tendsto_L2 hj n)
  have hright := hH.add (hu.const_mul (centralEnergyShift j))
  have hsame : ∀ N, ⟪z, physicalHermiteCutoffLift j n N⟫_ℝ =
      ⟪physicalEnergyBase j z, (compactHermiteImage_memLp j n N).toLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
          (compactHermiteFunction j n N))⟫_ℝ +
      centralEnergyShift j * ⟪physicalEnergyBase j z,
        (compactHermiteFunction_memLp j n N).toLp (compactHermiteFunction j n N)⟫_ℝ := by
    intro N
    exact physicalEnergy_inner_compact_operator j z (compactHermiteFunction j n N)
      (contDiff_compactHermiteFunction j n N) (compactHermiteFunction_hasCompactSupport j n N)
  have he := tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun N => (hsame N).symm))
  rw [real_inner_smul_right, inner_hermiteL2Vector_right] at he
  rw [he]
  unfold physicalHermiteWeight
  rw [← add_mul, centralEnergyShift_level]

theorem physicalHermiteVector_inner_left {j : ℝ} (hj : 0 < j)
    (z : PhysicalEnergySpace j) (n : ℕ) :
    ⟪physicalHermiteVector hj n, z⟫_ℝ =
      sqrt (physicalHermiteWeight j n) * hermiteCoefficient j (physicalEnergyBase j z) n := by
  rw [real_inner_comm, physicalHermiteVector, real_inner_smul_right, physicalEnergy_inner_hermite]
  have hs := sq_sqrt (physicalHermiteWeight_pos hj n).le
  have hn := (sqrt_pos.mpr (physicalHermiteWeight_pos hj n)).ne'
  have hscalar : (sqrt (physicalHermiteWeight j n))⁻¹ * physicalHermiteWeight j n =
      sqrt (physicalHermiteWeight j n) := by
    field_simp [hn]
    nlinarith only [hs]
  rw [← mul_assoc, hscalar]

theorem physicalHermiteVector_inner_right {j : ℝ} (hj : 0 < j)
    (z : PhysicalEnergySpace j) (n : ℕ) :
    ⟪z, physicalHermiteVector hj n⟫_ℝ =
      sqrt (physicalHermiteWeight j n) * hermiteCoefficient j (physicalEnergyBase j z) n := by
  rw [real_inner_comm]
  exact physicalHermiteVector_inner_left hj z n

theorem physicalHermiteVector_span_orthogonal {j : ℝ} (hj : 0 < j) :
    (Submodule.span ℝ (Set.range (physicalHermiteVector hj)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  rw [Submodule.mem_bot]
  apply physicalEnergyBase_injective j
  rw [map_zero]
  apply normalizedHermite_complete_Lp hj (physicalEnergyBase j z)
  intro n
  have hn : physicalHermiteVector hj n ∈
      Submodule.span ℝ (Set.range (physicalHermiteVector hj)) := Submodule.subset_span ⟨n, rfl⟩
  have hh := (Submodule.mem_orthogonal _ z).mp hz (physicalHermiteVector hj n) hn
  rw [physicalHermiteVector_inner_left] at hh
  exact (mul_eq_zero.mp hh).resolve_left (sqrt_pos.mpr (physicalHermiteWeight_pos hj n)).ne'

/-- A genuine Hilbert basis in the space defined first by weak
derivatives and almost-everywhere position multiplication. -/
def physicalHermiteBasis {j : ℝ} (hj : 0 < j) :
    HilbertBasis ℕ ℝ (PhysicalEnergySpace j) :=
  HilbertBasis.mkOfOrthogonalEqBot (physicalHermiteVector_orthonormal hj)
    (physicalHermiteVector_span_orthogonal hj)

@[simp] theorem physicalHermiteBasis_apply {j : ℝ} (hj : 0 < j) (n : ℕ) :
    physicalHermiteBasis hj n = physicalHermiteVector hj n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (physicalHermiteVector_orthonormal hj) (physicalHermiteVector_span_orthogonal hj)) n

theorem physicalHermiteBasis_repr {j : ℝ} (hj : 0 < j)
    (z : PhysicalEnergySpace j) (n : ℕ) :
    (physicalHermiteBasis hj).repr z n =
      sqrt (physicalHermiteWeight j n) * hermiteCoefficient j (physicalEnergyBase j z) n := by
  rw [(physicalHermiteBasis hj).repr_apply_apply, physicalHermiteBasis_apply,
    physicalHermiteVector_inner_left]

theorem physicalEnergy_weighted_parseval {j : ℝ} (hj : 0 < j) (z : PhysicalEnergySpace j) :
    HasSum (fun n => physicalHermiteWeight j n *
      hermiteCoefficient j (physicalEnergyBase j z) n ^ 2) (‖z‖ ^ 2) := by
  have hh := (physicalHermiteBasis hj).hasSum_inner_mul_inner z z
  convert hh using 1
  · funext n
    rw [physicalHermiteBasis_apply, physicalHermiteVector_inner_right,
      physicalHermiteVector_inner_left, ← pow_two, mul_pow,
      sq_sqrt (physicalHermiteWeight_pos hj n).le]
  · exact (real_inner_self_eq_norm_sq z).symm

/-- Both directions identify the physically defined domain, rather than
introducing a spectral definition of weak differentiation. -/
theorem physicalEnergy_domain_iff {j : ℝ} (hj : 0 < j) (u : HermiteL2) :
    (∃ z : PhysicalEnergySpace j, physicalEnergyBase j z = u) ↔
      Memℓp (fun n => sqrt (physicalHermiteWeight j n) * hermiteCoefficient j u n) 2 := by
  constructor
  · rintro ⟨z, rfl⟩
    have heq : (fun n => sqrt (physicalHermiteWeight j n) *
        hermiteCoefficient j (physicalEnergyBase j z) n) =
        ((physicalHermiteBasis hj).repr z : ℕ → ℝ) :=
      funext (fun n => (physicalHermiteBasis_repr hj z n).symm)
    rw [heq]
    exact lp.memℓp _
  · intro hu
    let c : lp (fun _ : ℕ => ℝ) 2 := ⟨_, hu⟩
    refine ⟨(physicalHermiteBasis hj).repr.symm c, ?_⟩
    apply (hermiteCoefficientTransform hj).injective
    apply lp.ext
    funext n
    rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
    have h := physicalHermiteBasis_repr hj ((physicalHermiteBasis hj).repr.symm c) n
    rw [(physicalHermiteBasis hj).repr.apply_symm_apply] at h
    change sqrt (physicalHermiteWeight j n) * hermiteCoefficient j u n =
      sqrt (physicalHermiteWeight j n) *
        hermiteCoefficient j (physicalEnergyBase j ((physicalHermiteBasis hj).repr.symm c)) n at h
    exact (mul_left_cancel₀ (sqrt_pos.mpr (physicalHermiteWeight_pos hj n)).ne' h).symm

/-- The carrier is actual compact smooth lifts, not a spectral substitute. -/
def physicalCompactSmoothCore (j : ℝ) : Submodule ℝ (PhysicalEnergySpace j) where
  carrier := {z | ∃ (φ : ℝ → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
    z = physicalEnergyLift j (compactSmooth_energyDomain hs hc)}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    apply physicalEnergyBase_injective j
    rw [map_zero, physicalEnergyLift_base]
    rfl
  add_mem' := by
    rintro z w ⟨φ, hsφ, hcφ, rfl⟩ ⟨ψ, hsψ, hcψ, rfl⟩
    refine ⟨φ + ψ, hsφ.add hsψ, hcφ.add hcψ, ?_⟩
    apply physicalEnergyBase_injective j
    rw [map_add, physicalEnergyLift_base, physicalEnergyLift_base, physicalEnergyLift_base]
    rfl
  smul_mem' := by
    rintro a z ⟨φ, hs, hc, rfl⟩
    have hsa : ContDiff ℝ ∞ (a • φ) := contDiff_const.smul hs
    have hca : HasCompactSupport (a • φ) := by
      convert hc.smul_left (f := fun _ : ℝ => a) using 1
    refine ⟨a • φ, hsa, hca, ?_⟩
    apply physicalEnergyBase_injective j
    rw [map_smul, physicalEnergyLift_base, physicalEnergyLift_base]
    rfl

theorem physicalCompactSmoothCore_dense {j : ℝ} (hj : 0 < j) :
    (physicalCompactSmoothCore j).topologicalClosure = ⊤ := by
  have hmode (n : ℕ) : physicalHermiteLift hj n ∈
      (physicalCompactSmoothCore j).topologicalClosure := by
    change physicalHermiteLift hj n ∈ closure
      (physicalCompactSmoothCore j : Set (PhysicalEnergySpace j))
    apply mem_closure_of_tendsto (physicalHermiteCutoffLift_tendsto hj n)
    exact Eventually.of_forall (fun N => ⟨compactHermiteFunction j n N,
      contDiff_compactHermiteFunction j n N, compactHermiteFunction_hasCompactSupport j n N, rfl⟩)
  have hspan : Submodule.span ℝ (Set.range (physicalHermiteVector hj)) ≤
      (physicalCompactSmoothCore j).topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro z ⟨n, rfl⟩
    exact ((physicalCompactSmoothCore j).topologicalClosure).smul_mem _ (hmode n)
  have hcl := (Submodule.span ℝ (Set.range (physicalHermiteVector hj))).topologicalClosure_minimal
    hspan (physicalCompactSmoothCore j).isClosed_topologicalClosure
  have heq : (Submodule.span ℝ (Set.range (physicalHermiteVector hj))).topologicalClosure = ⊤ := by
    have hf : ⇑(physicalHermiteBasis hj) = physicalHermiteVector hj :=
      funext (physicalHermiteBasis_apply hj)
    simpa only [hf] using (physicalHermiteBasis hj).dense_span
  rw [heq] at hcl
  exact top_unique hcl

end ContinuousFlexibility.Radial
