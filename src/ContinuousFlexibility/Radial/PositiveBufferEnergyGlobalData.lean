import ContinuousFlexibility.Radial.PositiveBufferEnergyGreenData

/-!
# The constructed endpoint and Green data at both cuts

This record packages the actual variational profiles, their physical
energies, the weighted energy columns and the smooth L² commutator
sources. Every field is obtained from the constructions above.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

structure PositiveBufferProfileData (B : BufferData) where
  pin : Fin 2 → ℝ → ℝ
  pout : Fin 2 → ℝ → ℝ
  alphaIn : Fin 2 → ℝ
  alphaOut : Fin 2 → ℝ
  pin_smooth : ∀ i, ContDiff ℝ ∞ (pin i)
  pout_smooth : ∀ i, ContDiff ℝ ∞ (pout i)
  inner_energy_integrable : ∀ i,
    IntervalIntegrable (fun x => deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2)
      volume (bufferCut B i) (bufferInnerWall B i)
  outer_energy_integrable : ∀ i,
    IntegrableOn (fun x => deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2)
      (bufferExterior B i) volume
  pin_cut : ∀ i, pin i (bufferCut B i) = 1
  pin_wall : ∀ i, pin i (bufferInnerWall B i) = 0
  pout_cut : ∀ i, pout i (bufferCut B i) = 1
  pout_memLp : ∀ i, MemLp (pout i) 2 (volume.restrict (bufferExterior B i))
  pin_equation : ∀ i x, x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i) →
    -deriv (deriv (pin i)) x + B.potential x * pin i x = 0
  pout_equation : ∀ i x, x ∈ bufferExterior B i →
    -deriv (deriv (pout i)) x + B.potential x * pout i x = 0
  alphaIn_conormal : ∀ i, alphaIn i = bufferSign i * deriv (pin i) (bufferCut B i)
  alphaOut_conormal : ∀ i, alphaOut i = -bufferSign i * deriv (pout i) (bufferCut B i)
  alphaIn_energy : ∀ i, alphaIn i = ∫ x in
    min (bufferCut B i) (bufferInnerWall B i)..max (bufferCut B i) (bufferInnerWall B i),
      deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2
  alphaOut_energy : ∀ i, alphaOut i = ∫ x in bufferExterior B i,
    deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2
  alphaIn_lower : ∀ i, B.mass i ≤ alphaIn i
  alphaIn_upper : ∀ i,
    alphaIn i ≤ 4 * (morseCutoffDerivativeConstant ^ 2 + B.layerBound) * B.mass i
  alphaOut_lower : ∀ i, B.mass i ≤ alphaOut i
  alphaOut_upper : ∀ i,
    alphaOut i ≤ 4 * (morseCutoffDerivativeConstant ^ 2 + B.layerBound) * B.mass i

namespace PositiveBufferProfileData

def A {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) : ℝ :=
  D.alphaIn i + D.alphaOut i

def normalizedIn {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) : ℝ → ℝ :=
  fun t => D.pin i (positiveBufferPoint B i t)

def normalizedOut {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) : ℝ → ℝ :=
  fun t => D.pout i (positiveBufferPoint B i (-t))

def kernel {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) : ℝ → ℝ :=
  positiveBufferGreenKernel B i (D.A i) (D.normalizedIn i) (D.normalizedOut i)

def sourceFunction {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) : ℝ → ℝ :=
  positiveBufferGreenError B i (D.A i) (D.normalizedIn i) (deriv (D.normalizedIn i))

def interiorKernel {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) : ℝ → ℝ :=
  positiveBufferGreenInterior B i (D.A i) (D.normalizedIn i)

theorem A_pos {B : BufferData} (D : PositiveBufferProfileData B)
    (hB : BufferHypotheses B) (i : Fin 2) : 0 < D.A i := by
  have hm := buffer_mass_pos hB i
  have hi := D.alphaIn_lower i
  have ho := D.alphaOut_lower i
  dsimp [A]
  linarith

theorem A_lower {B : BufferData} (D : PositiveBufferProfileData B)
    (hB : BufferHypotheses B) (i : Fin 2) : B.mass i ≤ D.A i := by
  have hm := buffer_mass_pos hB i
  have hi := D.alphaIn_lower i
  have ho := D.alphaOut_lower i
  dsimp [A]
  linarith

theorem A_upper {B : BufferData} (D : PositiveBufferProfileData B)
    (hB : BufferHypotheses B) {C₀ : ℝ} (hC₀ : B.layerBound ≤ C₀) (i : Fin 2) :
    D.A i ≤ 2 * (4 * (morseCutoffDerivativeConstant ^ 2 + C₀ + 1)) * B.mass i := by
  have hm := buffer_mass_pos hB i
  have hi := D.alphaIn_upper i
  have ho := D.alphaOut_upper i
  dsimp [A]
  nlinarith [mul_nonneg (sub_nonneg.mpr hC₀) hm.le]

theorem normalizedIn_smooth {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) :
    ContDiff ℝ ∞ (D.normalizedIn i) :=
  positiveBuffer_normalized_inner_contDiff i (D.pin_smooth i)

theorem normalizedOut_smooth {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) :
    ContDiff ℝ ∞ (D.normalizedOut i) :=
  positiveBuffer_normalized_outer_contDiff i (D.pout_smooth i)

@[simp] theorem normalizedIn_zero {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) :
    D.normalizedIn i 0 = 1 := by
  simpa only [normalizedIn, positiveBufferPoint_zero] using D.pin_cut i

@[simp] theorem normalizedOut_zero {B : BufferData} (D : PositiveBufferProfileData B) (i : Fin 2) :
    D.normalizedOut i 0 = 1 := by
  simpa only [normalizedOut, neg_zero, positiveBufferPoint_zero] using D.pout_cut i

end PositiveBufferProfileData

structure PositiveBufferGreenData (B : BufferData) (Ccut : ℝ) where
  profiles : PositiveBufferProfileData B
  energy : Fin 2 → PositiveBufferEnergy B.potential
  source : Fin 2 → RadialL2
  base_ae : ∀ i, (positiveBufferEnergyCoordinate B.potential 0 (energy i) : ℝ → ℝ) =ᵐ[volume]
    profiles.kernel i
  source_ae : ∀ i, (source i : ℝ → ℝ) =ᵐ[volume] profiles.sourceFunction i
  source_smooth : ∀ i, ContDiff ℝ ∞ (profiles.sourceFunction i)
  source_compact : ∀ i, HasCompactSupport (profiles.sourceFunction i)
  source_zero : ∀ i j t, t < B.action j + 2 →
    profiles.sourceFunction i (positiveBufferPoint B j t) = 0
  border_orthogonal : ∀ i, ⟪B.border, positiveBufferEnergyCoordinate B.potential 0 (energy i)⟫_ℝ = 0
  own_trace : ∀ i, positiveBufferTraceAt B.potential (bufferCut B i) (energy i) = (profiles.A i)⁻¹
  norm_bound : ∀ i,
    ‖positiveBufferEnergyCoordinate B.potential 0 (energy i)‖ ≤
      1 / (B.mass i * sqrt (profiles.A i))
  source_norm_bound : ∀ i,
    ‖source i‖ ≤ 6 * Ccut * sqrt (B.mass i) * exp (-B.action i)
  form_identity : ∀ (hV : Continuous B.potential) i (w : PositiveBufferEnergy B.potential),
    positiveBufferEnergyForm B.potential hV (energy i) w =
      ⟪source i, positiveBufferEnergyCoordinate B.potential 0 w⟫_ℝ +
        positiveBufferTraceAt B.potential (bufferCut B i) w

theorem positiveBuffer_profileData_nonempty {B : BufferData} (hB : BufferHypotheses B) :
    Nonempty (PositiveBufferProfileData B) := by
  obtain ⟨pin, pout, alphaIn, alphaOut, hp⟩ := positiveBuffer_exists_buffer_profiles hB
  refine ⟨
    { pin := pin
      pout := pout
      alphaIn := alphaIn
      alphaOut := alphaOut
      pin_smooth := ?_
      pout_smooth := ?_
      inner_energy_integrable := ?_
      outer_energy_integrable := ?_
      pin_cut := ?_
      pin_wall := ?_
      pout_cut := ?_
      pout_memLp := ?_
      pin_equation := ?_
      pout_equation := ?_
      alphaIn_conormal := ?_
      alphaOut_conormal := ?_
      alphaIn_energy := ?_
      alphaOut_energy := ?_
      alphaIn_lower := ?_
      alphaIn_upper := ?_
      alphaOut_lower := ?_
      alphaOut_upper := ?_ }⟩
  all_goals
    intro i
    rcases hp i with ⟨hsin, hsout, hEin, hEout, hinc, hinw, houtc, houtLp,
      hin, hout, hαin, hαout, hαinE, hαoutE, hαinlo, hαinhi, hαoutlo, hαouthi⟩
    assumption

/-- Both concrete columns and both concrete sources are chosen at once. -/
theorem positiveBuffer_greenData_nonempty {B : BufferData} (hB : BufferHypotheses B)
    {Ccut : ℝ} (hCcut : 0 ≤ Ccut)
    (hcut : ∀ i t, |deriv (positiveBufferCutoff (B.action i)) t| ≤ Ccut ∧
      |deriv (deriv (positiveBufferCutoff (B.action i))) t| ≤ Ccut) :
    Nonempty (PositiveBufferGreenData B Ccut) := by
  obtain ⟨D⟩ := positiveBuffer_profileData_nonempty hB
  have hc (i : Fin 2) := positiveBuffer_green_column_of_profiles hB i hCcut (hcut i)
    (D.pin_smooth i) (D.pout_smooth i) (D.pin_cut i) (D.pin_wall i) (D.pout_cut i)
    (D.pout_memLp i) (D.inner_energy_integrable i) (D.outer_energy_integrable i)
    (D.pin_equation i) (D.pout_equation i) (D.alphaIn_conormal i) (D.alphaOut_conormal i)
    (D.alphaIn_energy i) (D.alphaOut_energy i) (D.alphaIn_lower i) (D.alphaOut_lower i)
  choose energy source hbase hsource hsmooth hcompact hzero hborder htrace hnorm hsnorm hform using hc
  exact ⟨
    { profiles := D
      energy := energy
      source := source
      base_ae := hbase
      source_ae := hsource
      source_smooth := hsmooth
      source_compact := hcompact
      source_zero := hzero
      border_orthogonal := hborder
      own_trace := htrace
      norm_bound := hnorm
      source_norm_bound := hsnorm
      form_identity := fun _ i w => hform i w }⟩

end ContinuousFlexibility.Radial
