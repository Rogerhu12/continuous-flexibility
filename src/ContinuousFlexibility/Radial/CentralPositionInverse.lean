module

public import ContinuousFlexibility.Radial.OscillatorClosedForm
public import ContinuousFlexibility.Radial.CentralSpectralInverse
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual position-weighted central inverse

For every other even frequency, the genuine inverse has a physical weak
energy lift. Its third coordinate is the actual function `jXGf` in L².
An energy estimate, beyond the unweighted spectral gap, proves a uniform
bound for the actual `XGf`. This is the position weight `X`, not the
geometric weight `nu = R'/R`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem position_frequency_ge_four (n : ℕ) (hn : 2 ≤ n) :
    (4 : ℝ) ≤ 2 * (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem position_frequency_pos (n : ℕ) (hn : 2 ≤ n) :
    (0 : ℝ) < 2 * (n : ℝ) := by
  linarith [position_frequency_ge_four n hn]

private theorem position_inverse_constant_ge_one : (1 : ℝ) ≤ 2 / centralGapDelta := by
  apply (le_div_iff₀ centralGapDelta_pos).mpr
  linarith [centralGapDelta_lt_one]

private theorem position_central_coefficient_upper : centralOscillatorA ≤ (3 / 4 : ℝ) := by
  rw [centralOscillatorA_eq_sqrt_half]
  nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]

private theorem position_shift_upper (j : ℝ) :
    centralEnergyShift j ≤ 1 + (3 / 4 : ℝ) * j ^ 2 := by
  have hA := mul_le_mul_of_nonneg_left position_central_coefficient_upper (sq_nonneg j)
  unfold centralEnergyShift
  nlinarith only [hA, sq_nonneg centralRadiusA]

/-- The actual physical energy representative of the already constructed
central inverse, supplied by the proved closed-form association. -/
def centralInverseEnergyLift (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    PhysicalEnergySpace (2 * (n : ℝ)) :=
  physicalFormRepresentative (2 * (n : ℝ))
    (f + centralEnergyShift (2 * (n : ℝ)) • centralHilbertInverse n hn f)

theorem centralInverseEnergyLift_base (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    physicalEnergyBase (2 * (n : ℝ)) (centralInverseEnergyLift n hn f) =
      centralHilbertInverse n hn f := by
  apply (physicalClosedFormEquation_iff_representative _ _ _).mp
  exact physicalClosedFormEquation_of_mem_centralClosedGraph
    (position_frequency_pos n hn) _ _ (centralHilbertInverse_graph n hn f)

theorem centralInverseEnergyLift_pairing (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2)
    (V : PhysicalEnergySpace (2 * (n : ℝ))) :
    ⟪centralInverseEnergyLift n hn f, V⟫_ℝ =
      ⟪f + centralEnergyShift (2 * (n : ℝ)) • centralHilbertInverse n hn f,
        physicalEnergyBase (2 * (n : ℝ)) V⟫_ℝ :=
  physicalFormRepresentative_pairing _ _ V

theorem centralInverseEnergyLift_energy (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralInverseEnergyLift n hn f‖ ^ 2 =
      ⟪f, centralHilbertInverse n hn f⟫_ℝ +
        centralEnergyShift (2 * (n : ℝ)) * ‖centralHilbertInverse n hn f‖ ^ 2 := by
  have h := centralInverseEnergyLift_pairing n hn f (centralInverseEnergyLift n hn f)
  rw [real_inner_self_eq_norm_sq, centralInverseEnergyLift_base,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  exact h

theorem centralInverseEnergyLift_norm_bound (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralInverseEnergyLift n hn f‖ ≤
      (2 * (n : ℝ)) * (2 / centralGapDelta) * ‖f‖ := by
  let j : ℝ := 2 * (n : ℝ)
  let C : ℝ := 2 / centralGapDelta
  let F : ℝ := ‖f‖
  let u := centralHilbertInverse n hn f
  let B : ℝ := 1 + (3 / 4 : ℝ) * j ^ 2
  have hj : 4 ≤ j := position_frequency_ge_four n hn
  have hj0 : 0 < j := position_frequency_pos n hn
  have hj2 : (16 : ℝ) ≤ j ^ 2 := by nlinarith only [hj]
  have hC : 1 ≤ C := position_inverse_constant_ge_one
  have hC0 : 0 ≤ C := by linarith
  have hF0 : 0 ≤ F := norm_nonneg f
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hu : ‖u‖ ≤ C * F := centralHilbertInverse_bound n hn f
  have husq : ‖u‖ ^ 2 ≤ C ^ 2 * F ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hfirst : F * ‖u‖ ≤ C * F ^ 2 := by
    calc
      _ ≤ F * (C * F) := mul_le_mul_of_nonneg_left hu hF0
      _ = _ := by ring
  have hC2 : C ≤ C ^ 2 := by
    nlinarith only [mul_nonneg hC0 (sub_nonneg.mpr hC)]
  have hcoef : C + B * C ^ 2 ≤ j ^ 2 * C ^ 2 := by
    calc
      _ ≤ C ^ 2 + B * C ^ 2 := add_le_add hC2 le_rfl
      _ = (2 + (3 / 4 : ℝ) * j ^ 2) * C ^ 2 := by dsimp [B]; ring
      _ ≤ j ^ 2 * C ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hj2]) (sq_nonneg C)
  have henergy : ‖centralInverseEnergyLift n hn f‖ ^ 2 =
      ⟪f, u⟫_ℝ + centralEnergyShift j * ‖u‖ ^ 2 := centralInverseEnergyLift_energy n hn f
  have hsq : ‖centralInverseEnergyLift n hn f‖ ^ 2 ≤ j ^ 2 * C ^ 2 * F ^ 2 := by
    calc
      _ = ⟪f, u⟫_ℝ + centralEnergyShift j * ‖u‖ ^ 2 := henergy
      _ ≤ F * ‖u‖ + B * ‖u‖ ^ 2 :=
        add_le_add (real_inner_le_norm f u)
          (mul_le_mul_of_nonneg_right (position_shift_upper j) (sq_nonneg ‖u‖))
      _ ≤ C * F ^ 2 + B * (C ^ 2 * F ^ 2) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left husq hB0)
      _ = (C + B * C ^ 2) * F ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg F)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hj0.le hC0) hF0)).mp
  simpa only [mul_pow] using hsq

/-- The actual L² value of `XGf`, obtained by removing the frequency from
the genuine physical third coordinate. -/
def centralPositionInverseValue (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) : HermiteL2 :=
  (2 * (n : ℝ))⁻¹ • physicalEnergyPosition (2 * (n : ℝ))
    (centralInverseEnergyLift n hn f)

theorem centralPositionInverseValue_ae (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    (centralPositionInverseValue n hn f : ℝ → ℝ) =ᵐ[volume]
      (fun x : ℝ => x * centralHilbertInverse n hn f x) := by
  let j : ℝ := 2 * (n : ℝ)
  let U := centralInverseEnergyLift n hn f
  have hw : (physicalEnergyPosition j U : ℝ → ℝ) =ᵐ[volume]
      (fun x => j * x * physicalEnergyBase j U x) := U.property.2
  rw [centralInverseEnergyLift_base] at hw
  filter_upwards [hw, Lp.coeFn_smul j⁻¹ (physicalEnergyPosition j U)] with x hx hsmul
  change (j⁻¹ • physicalEnergyPosition j U) x = _
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx]
  have hj : j ≠ 0 := (position_frequency_pos n hn).ne'
  field_simp

theorem centralPositionInverseValue_norm_bound (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralPositionInverseValue n hn f‖ ≤ (2 / centralGapDelta) * ‖f‖ := by
  let j : ℝ := 2 * (n : ℝ)
  have hj : 0 < j := position_frequency_pos n hn
  have hpos : ‖physicalEnergyPosition j (centralInverseEnergyLift n hn f)‖ ≤
      j * (2 / centralGapDelta) * ‖f‖ :=
    (physicalEnergyCoordinate_norm_le j 2 _).trans (centralInverseEnergyLift_norm_bound n hn f)
  calc
    _ = j⁻¹ * ‖physicalEnergyPosition j (centralInverseEnergyLift n hn f)‖ := by
      rw [centralPositionInverseValue, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hj]
    _ ≤ j⁻¹ * (j * (2 / centralGapDelta) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hpos (inv_nonneg.mpr hj.le)
    _ = _ := by field_simp

/-- No position-weighted membership is assumed: it follows from the
constructed physical energy lift for every actual L² source. -/
theorem centralHilbertInverse_position_memLp (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    MemLp (fun x : ℝ => x * centralHilbertInverse n hn f x) 2 volume :=
  (memLp_congr_ae (centralPositionInverseValue_ae n hn f)).mp
    (Lp.memLp (centralPositionInverseValue n hn f))

private def centralPositionInverseLinearMap (n : ℕ) (hn : 2 ≤ n) :
    HermiteL2 →ₗ[ℝ] HermiteL2 where
  toFun := centralPositionInverseValue n hn
  map_add' f g := by
    apply Lp.ext
    have hsum := centralPositionInverseValue_ae n hn (f + g)
    rw [(centralHilbertInverse n hn).map_add] at hsum
    filter_upwards [hsum, centralPositionInverseValue_ae n hn f,
      centralPositionInverseValue_ae n hn g,
      Lp.coeFn_add (centralHilbertInverse n hn f) (centralHilbertInverse n hn g),
      Lp.coeFn_add (centralPositionInverseValue n hn f) (centralPositionInverseValue n hn g)]
      with x hs hf hg hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' a f := by
    change centralPositionInverseValue n hn (a • f) = a • centralPositionInverseValue n hn f
    apply Lp.ext
    have hscale := centralPositionInverseValue_ae n hn (a • f)
    rw [(centralHilbertInverse n hn).map_smul] at hscale
    filter_upwards [hscale, centralPositionInverseValue_ae n hn f,
      Lp.coeFn_smul a (centralHilbertInverse n hn f),
      Lp.coeFn_smul a (centralPositionInverseValue n hn f)] with x hs hf hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

/-- A genuine bounded operator on all actual L² sources representing
`XG`, with its norm established from the physical energy estimate. -/
def centralPositionInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  (centralPositionInverseLinearMap n hn).mkContinuous (2 / centralGapDelta)
    (centralPositionInverseValue_norm_bound n hn)

@[simp] theorem centralPositionInverse_apply (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    centralPositionInverse n hn f = centralPositionInverseValue n hn f := rfl

theorem centralPositionInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralPositionInverse n hn‖ ≤ 2 / centralGapDelta :=
  LinearMap.mkContinuous_norm_le _
    (div_nonneg (by norm_num) centralGapDelta_pos.le)
    (centralPositionInverseValue_norm_bound n hn)

theorem centralPositionInverse_ae (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    (centralPositionInverse n hn f : ℝ → ℝ) =ᵐ[volume]
      (fun x : ℝ => x * centralHilbertInverse n hn f x) :=
  centralPositionInverseValue_ae n hn f

/-- Actual membership in the domain of multiplication by the real
position coordinate, including the specified L² image. -/
def HasPositionL2 (u xu : HermiteL2) : Prop :=
  (xu : ℝ → ℝ) =ᵐ[volume] (fun x : ℝ => x * u x)

theorem HasPositionL2.unique {u xu yu : HermiteL2}
    (hx : HasPositionL2 u xu) (hy : HasPositionL2 u yu) : xu = yu := by
  apply Lp.ext
  exact hx.trans hy.symm

theorem positionL2_pairing_swap {u xu v xv : HermiteL2}
    (hu : HasPositionL2 u xu) (hv : HasPositionL2 v xv) :
    ⟪xu, v⟫_ℝ = ⟪u, xv⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy]
  ring

theorem centralHilbertInverse_inner_swap (n : ℕ) (hn : 2 ≤ n) (f g : HermiteL2) :
    ⟪centralHilbertInverse n hn f, g⟫_ℝ =
      ⟪f, centralHilbertInverse n hn g⟫_ℝ :=
  (centralClosedGraph_symmetric (position_frequency_pos n hn)
    (centralHilbertInverse n hn f) f (centralHilbertInverse n hn g) g
    (centralHilbertInverse_graph n hn f) (centralHilbertInverse_graph n hn g)).symm

/-- The genuine bounded extension of the right-weighted inverse `GX`,
constructed as the adjoint of the already proved actual `XG`. -/
def centralRightPositionInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  ContinuousLinearMap.adjoint (centralPositionInverse n hn)

theorem centralRightPositionInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralRightPositionInverse n hn‖ ≤ 2 / centralGapDelta :=
  (ContinuousLinearMap.adjoint.norm_map (centralPositionInverse n hn)).trans_le
    (centralPositionInverse_norm_le n hn)

theorem centralRightPositionInverse_bound (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralRightPositionInverse n hn f‖ ≤ (2 / centralGapDelta) * ‖f‖ :=
  (centralRightPositionInverse n hn).le_of_opNorm_le (centralRightPositionInverse_norm_le n hn) f

/-- On the real multiplication domain, the adjoint extension agrees
with the actual inverse applied to the actual position-weighted source. -/
theorem centralRightPositionInverse_eq (n : ℕ) (hn : 2 ≤ n)
    (f xf : HermiteL2) (hf : HasPositionL2 f xf) :
    centralRightPositionInverse n hn f = centralHilbertInverse n hn xf := by
  apply ext_inner_right ℝ
  intro g
  change ⟪ContinuousLinearMap.adjoint (centralPositionInverse n hn) f, g⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = ⟪xf, centralHilbertInverse n hn g⟫_ℝ :=
      (positionL2_pairing_swap hf (centralPositionInverse_ae n hn g)).symm
    _ = _ := (centralHilbertInverse_inner_swap n hn xf g).symm

theorem HasPositionL2.smul {u xu : HermiteL2} (hu : HasPositionL2 u xu) (a : ℝ) :
    HasPositionL2 (a • u) (a • xu) := by
  filter_upwards [hu, Lp.coeFn_smul a xu, Lp.coeFn_smul a u] with x hx hxu hu'
  rw [hxu, hu']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx]
  ring

theorem physicalEnergy_scaledPosition_ae {j : ℝ} (hj : 0 < j)
    (U : PhysicalEnergySpace j) :
    HasPositionL2 (physicalEnergyBase j U) (j⁻¹ • physicalEnergyPosition j U) := by
  have hw : (physicalEnergyPosition j U : ℝ → ℝ) =ᵐ[volume]
      (fun x => j * x * physicalEnergyBase j U x) := U.property.2
  filter_upwards [hw, Lp.coeFn_smul j⁻¹ (physicalEnergyPosition j U)] with x hx hsmul
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx]
  field_simp

def centralHermitePositionVector {j : ℝ} (hj : 0 < j) (m : ℕ) : HermiteL2 :=
  (normalizedOscillatorHermite_energyDomain hj m).2.2.2.toLp
    (fun x : ℝ => x * normalizedOscillatorHermite j m x)

theorem centralHermitePositionVector_ae {j : ℝ} (hj : 0 < j) (m : ℕ) :
    HasPositionL2 (hermiteL2Vector hj m) (centralHermitePositionVector hj m) := by
  filter_upwards [hermiteL2Vector_coeFn hj m,
    MemLp.coeFn_toLp (normalizedOscillatorHermite_energyDomain hj m).2.2.2] with x he hx
  change ((normalizedOscillatorHermite_energyDomain hj m).2.2.2.toLp
    (fun y : ℝ => y * normalizedOscillatorHermite j m y)) x = x * hermiteL2Vector hj m x
  rw [he, hx]

theorem centralHilbertInverse_mode (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    centralHilbertInverse n hn (hermiteL2Vector (position_frequency_pos n hn) m) =
      (centralSpectralLevel (2 * (n : ℝ)) m)⁻¹ •
        hermiteL2Vector (position_frequency_pos n hn) m :=
  hermiteBoundedMultiplier_vector _ _ _ _ _ m

theorem centralPositionInverse_mode (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    centralPositionInverse n hn (hermiteL2Vector (position_frequency_pos n hn) m) =
      (centralSpectralLevel (2 * (n : ℝ)) m)⁻¹ •
        centralHermitePositionVector (position_frequency_pos n hn) m := by
  have hX : HasPositionL2
      (centralHilbertInverse n hn (hermiteL2Vector (position_frequency_pos n hn) m))
      (centralPositionInverse n hn (hermiteL2Vector (position_frequency_pos n hn) m)) :=
    centralPositionInverse_ae n hn _
  rw [centralHilbertInverse_mode] at hX
  exact hX.unique ((centralHermitePositionVector_ae (position_frequency_pos n hn) m).smul _)

theorem physicalHermiteLift_scaledPosition {j : ℝ} (hj : 0 < j) (m : ℕ) :
    j⁻¹ • physicalEnergyPosition j (physicalHermiteLift hj m) =
      centralHermitePositionVector hj m := by
  have h := physicalEnergy_scaledPosition_ae hj (physicalHermiteLift hj m)
  rw [physicalHermiteLift_base] at h
  exact h.unique (centralHermitePositionVector_ae hj m)

theorem centralRightPositionInverse_coefficient_energy (n : ℕ) (hn : 2 ≤ n)
    (f : HermiteL2) (m : ℕ) :
    centralSpectralLevel (2 * (n : ℝ)) m *
        hermiteCoefficient (2 * (n : ℝ)) (centralRightPositionInverse n hn f) m =
      ⟪f, centralHermitePositionVector (position_frequency_pos n hn) m⟫_ℝ := by
  have hp : hermiteCoefficient (2 * (n : ℝ)) (centralRightPositionInverse n hn f) m =
      (centralSpectralLevel (2 * (n : ℝ)) m)⁻¹ *
        ⟪f, centralHermitePositionVector (position_frequency_pos n hn) m⟫_ℝ := by
    rw [← inner_hermiteL2Vector_right (position_frequency_pos n hn)]
    change ⟪ContinuousLinearMap.adjoint (centralPositionInverse n hn) f,
      hermiteL2Vector (position_frequency_pos n hn) m⟫_ℝ = _
    rw [ContinuousLinearMap.adjoint_inner_left, centralPositionInverse_mode,
      real_inner_smul_right]
  rw [hp]
  have he : centralSpectralLevel (2 * (n : ℝ)) m ≠ 0 := by
    intro hz
    have hgap := centralSpectralLevel_even_gap n m hn
    rw [hz, abs_zero] at hgap
    linarith [centralGapDelta_pos]
  field_simp

def centralRightEnergyFunctional (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    StrongDual ℝ (PhysicalEnergySpace (2 * (n : ℝ))) :=
  ((innerSL ℝ f).comp ((2 * (n : ℝ))⁻¹ • physicalEnergyPosition (2 * (n : ℝ)))) +
    centralEnergyShift (2 * (n : ℝ)) •
      ((innerSL ℝ (centralRightPositionInverse n hn f)).comp (physicalEnergyBase (2 * (n : ℝ))))

def centralRightInverseEnergyLift (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    PhysicalEnergySpace (2 * (n : ℝ)) :=
  (InnerProductSpace.toDual ℝ (PhysicalEnergySpace (2 * (n : ℝ)))).symm
    (centralRightEnergyFunctional n hn f)

theorem centralRightInverseEnergyLift_pairing (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2)
    (V : PhysicalEnergySpace (2 * (n : ℝ))) :
    ⟪centralRightInverseEnergyLift n hn f, V⟫_ℝ =
      ⟪f, (2 * (n : ℝ))⁻¹ • physicalEnergyPosition (2 * (n : ℝ)) V⟫_ℝ +
        centralEnergyShift (2 * (n : ℝ)) *
          ⟪centralRightPositionInverse n hn f, physicalEnergyBase (2 * (n : ℝ)) V⟫_ℝ :=
  InnerProductSpace.toDual_symm_apply

/-- The bounded right-weighted extension itself lies in the genuine
physical energy domain, proved by real Riesz/Hermite testing. -/
theorem centralRightInverseEnergyLift_base (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    physicalEnergyBase (2 * (n : ℝ)) (centralRightInverseEnergyLift n hn f) =
      centralRightPositionInverse n hn f := by
  apply (hermiteCoefficientTransform (position_frequency_pos n hn)).injective
  apply lp.ext
  funext m
  rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
  have h := centralRightInverseEnergyLift_pairing n hn f
    (physicalHermiteLift (position_frequency_pos n hn) m)
  rw [physicalEnergy_inner_hermite, physicalHermiteLift_scaledPosition, physicalHermiteLift_base,
    inner_hermiteL2Vector_right,
    ← centralRightPositionInverse_coefficient_energy n hn f m] at h
  have hw : centralSpectralLevel (2 * (n : ℝ)) m + centralEnergyShift (2 * (n : ℝ)) =
      physicalHermiteWeight (2 * (n : ℝ)) m := centralEnergyShift_level _ _
  rw [← add_mul, hw] at h
  exact mul_left_cancel₀ (physicalHermiteWeight_pos (position_frequency_pos n hn) m).ne' h

def centralDoublePositionInverseValue (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) : HermiteL2 :=
  (2 * (n : ℝ))⁻¹ • physicalEnergyPosition (2 * (n : ℝ))
    (centralRightInverseEnergyLift n hn f)

theorem centralDoublePositionInverseValue_ae (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    HasPositionL2 (centralRightPositionInverse n hn f)
      (centralDoublePositionInverseValue n hn f) := by
  have h := physicalEnergy_scaledPosition_ae (position_frequency_pos n hn)
    (centralRightInverseEnergyLift n hn f)
  rwa [centralRightInverseEnergyLift_base] at h

theorem centralRightInverseEnergyLift_energy (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralRightInverseEnergyLift n hn f‖ ^ 2 =
      ⟪f, centralDoublePositionInverseValue n hn f⟫_ℝ +
        centralEnergyShift (2 * (n : ℝ)) * ‖centralRightPositionInverse n hn f‖ ^ 2 := by
  have h := centralRightInverseEnergyLift_pairing n hn f (centralRightInverseEnergyLift n hn f)
  rw [real_inner_self_eq_norm_sq, centralRightInverseEnergyLift_base,
    real_inner_self_eq_norm_sq] at h
  exact h

private theorem physicalEnergy_scaledPosition_sq_le {j : ℝ} (hj : 0 < j)
    (U : PhysicalEnergySpace j) :
    j ^ 2 * ‖j⁻¹ • physicalEnergyPosition j U‖ ^ 2 ≤ ‖U‖ ^ 2 := by
  have hpos : j • (j⁻¹ • physicalEnergyPosition j U) = physicalEnergyPosition j U := by
    rw [smul_smul, mul_inv_cancel₀ hj.ne', one_smul]
  have hnorm := congrArg (fun v : HermiteL2 => ‖v‖ ^ 2) hpos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hj, mul_pow] at hnorm
  have hcoor : ‖physicalEnergyPosition j U‖ ≤ ‖U‖ := physicalEnergyCoordinate_norm_le j 2 U
  exact hnorm.trans_le (pow_le_pow_left₀ (norm_nonneg _) hcoor 2)

/-- Actual energy absorption gives the two-sided position bound. The
right-weighted image is not assumed to have an extra moment. -/
theorem centralDoublePositionInverseValue_norm_bound (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralDoublePositionInverseValue n hn f‖ ≤ (2 / centralGapDelta) * ‖f‖ := by
  let j : ℝ := 2 * (n : ℝ)
  let C : ℝ := 2 / centralGapDelta
  let F : ℝ := ‖f‖
  let p : ℝ := ‖centralDoublePositionInverseValue n hn f‖
  let U := centralRightInverseEnergyLift n hn f
  let B : ℝ := 1 + (3 / 4 : ℝ) * j ^ 2
  have hj : 4 ≤ j := position_frequency_ge_four n hn
  have hj0 : 0 < j := position_frequency_pos n hn
  have hj2 : (16 : ℝ) ≤ j ^ 2 := by nlinarith only [hj]
  have hC : 1 ≤ C := position_inverse_constant_ge_one
  have hC0 : 0 ≤ C := by linarith
  have hF0 : 0 ≤ F := norm_nonneg f
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hu : ‖centralRightPositionInverse n hn f‖ ≤ C * F := centralRightPositionInverse_bound n hn f
  have husq : ‖centralRightPositionInverse n hn f‖ ^ 2 ≤ C ^ 2 * F ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hleft : j ^ 2 * p ^ 2 ≤ ‖U‖ ^ 2 := physicalEnergy_scaledPosition_sq_le hj0 U
  have hmain : j ^ 2 * p ^ 2 ≤ F * p + B * (C ^ 2 * F ^ 2) := by
    calc
      _ ≤ ‖U‖ ^ 2 := hleft
      _ = ⟪f, centralDoublePositionInverseValue n hn f⟫_ℝ +
          centralEnergyShift j * ‖centralRightPositionInverse n hn f‖ ^ 2 :=
        centralRightInverseEnergyLift_energy n hn f
      _ ≤ F * p + B * ‖centralRightPositionInverse n hn f‖ ^ 2 :=
        add_le_add (real_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_right (position_shift_upper j) (sq_nonneg _))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left husq hB0)
  change p ≤ C * F
  by_contra h
  have hpgt : C * F < p := lt_of_not_ge h
  have hp : 0 < p := lt_of_le_of_lt (mul_nonneg hC0 hF0) hpgt
  have hFC : F ≤ C * F := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hF0
  have hFp : F * p < p ^ 2 := by
    simpa only [pow_two] using mul_lt_mul_of_pos_right (hFC.trans_lt hpgt) hp
  have hCFsq : C ^ 2 * F ^ 2 ≤ p ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hC0 hF0) hpgt.le 2
  have hBterm := mul_le_mul_of_nonneg_left hCFsq hB0
  have hcoeff : (1 + B) * p ^ 2 ≤ j ^ 2 * p ^ 2 :=
    mul_le_mul_of_nonneg_right (by dsimp [B]; nlinarith only [hj2]) (sq_nonneg p)
  have hstrict : F * p + B * (C ^ 2 * F ^ 2) < (1 + B) * p ^ 2 := by
    calc
      _ < p ^ 2 + B * (C ^ 2 * F ^ 2) := add_lt_add_of_lt_of_le hFp le_rfl
      _ ≤ p ^ 2 + B * p ^ 2 := add_le_add le_rfl hBterm
      _ = _ := by ring
  exact (lt_irrefl (j ^ 2 * p ^ 2)) ((hmain.trans_lt hstrict).trans_le hcoeff)

private def centralDoublePositionInverseLinearMap (n : ℕ) (hn : 2 ≤ n) :
    HermiteL2 →ₗ[ℝ] HermiteL2 where
  toFun := centralDoublePositionInverseValue n hn
  map_add' f g := by
    apply Lp.ext
    have hsum := centralDoublePositionInverseValue_ae n hn (f + g)
    rw [(centralRightPositionInverse n hn).map_add] at hsum
    filter_upwards [hsum, centralDoublePositionInverseValue_ae n hn f,
      centralDoublePositionInverseValue_ae n hn g,
      Lp.coeFn_add (centralRightPositionInverse n hn f) (centralRightPositionInverse n hn g),
      Lp.coeFn_add (centralDoublePositionInverseValue n hn f) (centralDoublePositionInverseValue n hn g)]
      with x hs hf hg hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' a f := by
    change centralDoublePositionInverseValue n hn (a • f) = a • centralDoublePositionInverseValue n hn f
    apply Lp.ext
    have hscale := centralDoublePositionInverseValue_ae n hn (a • f)
    rw [(centralRightPositionInverse n hn).map_smul] at hscale
    filter_upwards [hscale, centralDoublePositionInverseValue_ae n hn f,
      Lp.coeFn_smul a (centralRightPositionInverse n hn f),
      Lp.coeFn_smul a (centralDoublePositionInverseValue n hn f)] with x hs hf hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

/-- A bounded extension of the actual two-sided position inverse `XGX`. -/
def centralDoublePositionInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  (centralDoublePositionInverseLinearMap n hn).mkContinuous (2 / centralGapDelta)
    (centralDoublePositionInverseValue_norm_bound n hn)

theorem centralDoublePositionInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralDoublePositionInverse n hn‖ ≤ 2 / centralGapDelta :=
  LinearMap.mkContinuous_norm_le _
    (div_nonneg (by norm_num) centralGapDelta_pos.le)
    (centralDoublePositionInverseValue_norm_bound n hn)

theorem centralDoublePositionInverse_ae (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    HasPositionL2 (centralRightPositionInverse n hn f) (centralDoublePositionInverse n hn f) :=
  centralDoublePositionInverseValue_ae n hn f

/-- The bounded two-sided extension agrees with `XG(Xf)` on the actual
position multiplication domain. -/
theorem centralDoublePositionInverse_eq (n : ℕ) (hn : 2 ≤ n)
    (f xf : HermiteL2) (hf : HasPositionL2 f xf) :
    centralDoublePositionInverse n hn f = centralPositionInverse n hn xf := by
  have h := centralDoublePositionInverse_ae n hn f
  rw [centralRightPositionInverse_eq n hn f xf hf] at h
  exact h.unique (centralPositionInverse_ae n hn xf)

theorem centralDoublePositionInverse_inner_swap (n : ℕ) (hn : 2 ≤ n) (f g : HermiteL2) :
    ⟪centralDoublePositionInverse n hn f, g⟫_ℝ =
      ⟪f, centralDoublePositionInverse n hn g⟫_ℝ := by
  have hfg := centralRightInverseEnergyLift_pairing n hn f (centralRightInverseEnergyLift n hn g)
  have hgf := centralRightInverseEnergyLift_pairing n hn g (centralRightInverseEnergyLift n hn f)
  rw [centralRightInverseEnergyLift_base] at hfg hgf
  change ⟪centralRightInverseEnergyLift n hn f, centralRightInverseEnergyLift n hn g⟫_ℝ =
    ⟪f, centralDoublePositionInverseValue n hn g⟫_ℝ + centralEnergyShift (2 * (n : ℝ)) *
      ⟪centralRightPositionInverse n hn f, centralRightPositionInverse n hn g⟫_ℝ at hfg
  change ⟪centralRightInverseEnergyLift n hn g, centralRightInverseEnergyLift n hn f⟫_ℝ =
    ⟪g, centralDoublePositionInverseValue n hn f⟫_ℝ + centralEnergyShift (2 * (n : ℝ)) *
      ⟪centralRightPositionInverse n hn g, centralRightPositionInverse n hn f⟫_ℝ at hgf
  have hE := real_inner_comm (centralRightInverseEnergyLift n hn f)
    (centralRightInverseEnergyLift n hn g)
  have hR := real_inner_comm (centralRightPositionInverse n hn f) (centralRightPositionInverse n hn g)
  rw [hE, hR] at hgf
  have h : ⟪f, centralDoublePositionInverseValue n hn g⟫_ℝ =
      ⟪g, centralDoublePositionInverseValue n hn f⟫_ℝ :=
    add_right_cancel (hfg.symm.trans hgf)
  change ⟪centralDoublePositionInverseValue n hn f, g⟫_ℝ =
    ⟪f, centralDoublePositionInverseValue n hn g⟫_ℝ
  exact (real_inner_comm _ _).trans h.symm

end ContinuousFlexibility.Radial
