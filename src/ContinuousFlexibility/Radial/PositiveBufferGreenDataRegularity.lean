import ContinuousFlexibility.Radial.PositiveBufferEnergyGlobalData

/-!
# Classical representatives of the constructed Green energy columns

The glued kernel is the actual continuous representative of its energy
field. Its smooth interior formula therefore has the genuine retained
traces and satisfies the ordinary cutoff-source equation. The same
energy representative bounds the physical exterior endpoint profile.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem bufferAffineBranch_second_deriv {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    (c k b x : ℝ) :
    deriv (deriv (fun y => k * p (b * (y - c)))) x =
      k * b ^ 2 * deriv (deriv p) (b * (x - c)) := by
  have hfirst : deriv (fun y => k * p (b * (y - c))) =
      fun y => k * b * deriv p (b * (y - c)) := by
    funext y
    exact (bufferAffineBranch_hasDerivAt hp c k b y).deriv
  rw [hfirst]
  exact (bufferAffineBranch_second_hasDerivAt hp c k b x).deriv

namespace PositiveBufferGreenData

theorem kernel_continuous {B : BufferData} {Ccut : ℝ}
    (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B) (i : Fin 2) :
    Continuous (D.profiles.kernel i) :=
  positiveBufferGreenKernel_continuous hB i (D.profiles.A i)
    (D.profiles.normalizedIn_smooth i).continuous
    (D.profiles.normalizedOut_smooth i).continuous
    (D.profiles.normalizedIn_zero i) (D.profiles.normalizedOut_zero i)

theorem kernel_eq_representative {B : BufferData} {Ccut : ℝ}
    (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B) (i : Fin 2) :
    D.profiles.kernel i =
      positiveBufferEnergyRepresentative B.potential (D.energy i) :=
  (positiveBufferEnergyRepresentative_eq B.potential (D.energy i)
    (D.kernel_continuous hB i) (D.base_ae i)).symm

theorem interiorKernel_eq_representative {B : BufferData} {Ccut : ℝ}
    (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B) (i : Fin 2) :
    EqOn (D.profiles.interiorKernel i)
      (positiveBufferEnergyRepresentative B.potential (D.energy i)) (Icc B.l B.h) := by
  intro x hx
  rw [← D.kernel_eq_representative hB i]
  exact (positiveBufferGreenKernel_eq_interior hB i (D.profiles.A i)
    (D.profiles.normalizedIn_zero i) (D.profiles.normalizedOut_zero i) hx).symm

theorem interiorKernel_smooth {B : BufferData} {Ccut : ℝ}
    (D : PositiveBufferGreenData B Ccut) (i : Fin 2) :
    ContDiff ℝ ∞ (D.profiles.interiorKernel i) :=
  positiveBufferGreenInterior_contDiff B i (D.profiles.A i)
    (D.profiles.normalizedIn_smooth i)

/-- The smooth retained representative solves the actual commutator equation. -/
theorem interiorKernel_equation {B : BufferData} {Ccut : ℝ}
    (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B) (i : Fin 2)
    (x : ℝ) (hx : x ∈ Ioo B.l B.h) :
    -deriv (deriv (D.profiles.interiorKernel i)) x +
      B.potential x * D.profiles.interiorKernel i x = D.profiles.sourceFunction i x := by
  have hm := buffer_mass_pos hB i
  have hA := D.profiles.A_pos hB i
  have hxc : x ≠ bufferCut B i := by
    by_cases hi : i = 0
    · simpa only [bufferCut, if_pos hi] using (ne_of_gt hx.1)
    · simpa only [bufferCut, if_neg hi] using (ne_of_lt hx.2)
  have htne : positiveBufferCoordinate B i x ≠ 0 := by
    intro hz
    have he := positiveBufferPoint_coordinate hB i x
    rw [hz, positiveBufferPoint_zero] at he
    exact hxc he.symm
  have ht : 0 < positiveBufferCoordinate B i x :=
    lt_of_le_of_ne (positiveBufferCoordinate_nonneg_interval hB i ⟨hx.1.le, hx.2.le⟩)
      (Ne.symm htne)
  have hin := positiveBuffer_normalized_inner_equation hB i
    (D.profiles.pin_smooth i) (D.profiles.pin_equation i)
  have hout := positiveBuffer_normalized_outer_equation hB i
    (D.profiles.pout_smooth i) (D.profiles.pout_equation i)
  have hcurv := positiveBufferGreenProfile_curvature hB i
    (D.profiles.normalizedIn_smooth i) (D.profiles.normalizedOut_smooth i) hin hout htne
  rw [bufferCutGlue_of_lt _ _ _ ht, positiveBufferGreenProfile,
    bufferCutGlue_of_lt _ _ _ ht] at hcurv
  let pR : ℝ → ℝ := fun t =>
    positiveBufferCutoff (B.action i) t * D.profiles.normalizedIn i t
  have hpR : ContDiff ℝ ∞ pR :=
    (positiveBufferCutoff_contDiff (B.action i)).mul (D.profiles.normalizedIn_smooth i)
  have hsecond : deriv (deriv (D.profiles.interiorKernel i)) x =
      (D.profiles.A i)⁻¹ * (-bufferSign i * B.mass i) ^ 2 *
        deriv (deriv pR) (positiveBufferCoordinate B i x) := by
    exact bufferAffineBranch_second_deriv hpR (bufferCut B i) (D.profiles.A i)⁻¹
      (-bufferSign i * B.mass i) x
  rw [hsecond]
  dsimp only [pR]
  rw [hcurv, mul_pow, neg_sq, bufferSign_sq, one_mul,
    positiveBufferPoint_coordinate hB i x]
  unfold PositiveBufferProfileData.interiorKernel PositiveBufferProfileData.sourceFunction
    positiveBufferGreenInterior positiveBufferGreenError
  field_simp [hm.ne', hA.ne']
  <;> ring

/-- The normalized exterior branch inherits a uniform bound from the actual
continuous energy representative; affine inversion gives the physical bound. -/
theorem pout_bounded {B : BufferData} {Ccut : ℝ}
    (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B) (i : Fin 2) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ closure (bufferExterior B i), |D.profiles.pout i x| ≤ M := by
  let M : ℝ := |D.profiles.A i| * (2 * ‖D.energy i‖)
  have hglobal : ∀ x : ℝ, |D.profiles.kernel i x| ≤ 2 * ‖D.energy i‖ := by
    intro x
    rw [D.kernel_eq_representative hB i]
    exact positiveBufferEnergyRepresentative_bound B.potential (D.energy i) x
  have hout := positiveBufferGreenKernel_outward_bound hB i
    (D.profiles.A_pos hB i).ne' (D.profiles.normalizedIn i) (D.profiles.normalizedOut i)
    hglobal
  refine ⟨M, mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _)), ?_⟩
  intro x hx
  have ht : -positiveBufferCoordinate B i x ∈ Ici (0 : ℝ) := by
    rw [← positiveBufferPoint_outward_preimage_exterior_closure hB i]
    change positiveBufferPoint B i (- -positiveBufferCoordinate B i x) ∈
      closure (bufferExterior B i)
    simpa only [neg_neg, positiveBufferPoint_coordinate hB i x] using hx
  have hb := hout (-positiveBufferCoordinate B i x) ht
  change |D.profiles.pout i (positiveBufferPoint B i (- -positiveBufferCoordinate B i x))| ≤ M at hb
  simpa only [neg_neg, positiveBufferPoint_coordinate hB i x] using hb

end PositiveBufferGreenData

end ContinuousFlexibility.Radial
