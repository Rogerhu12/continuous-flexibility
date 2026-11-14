module

public import ContinuousFlexibility.Radial.InnerBufferSource
public import ContinuousFlexibility.Radial.InnerBufferLeading

/-!
# One localized construction from the actual compression witnesses

The Dirichlet inverse, Poisson representatives, conormal entries,
localized leading fields and cutoff errors all come from one application
of positive-buffer compression. The leading and remainder estimates are
derived here, using the original inward energy and the actual commutator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators InnerProductSpace

structure InnerBufferLocalizedColumn (B : BufferData) (C K : ℝ)
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ)) (i : Fin 2) where
  pin : ℝ → ℝ
  p : ℝ → ℝ
  field : RadialL2
  scalar : ℝ
  inwardEnergy : ℝ
  outwardEnergy : ℝ
  pin_regular : ContDiffOn ℝ 2 pin (uIcc (bufferCut B i) (bufferInnerWall B i))
  pin_cut_regular : ContDiffAt ℝ ∞ pin (bufferCut B i)
  pin_cut : pin (bufferCut B i) = 1
  pin_wall : pin (bufferInnerWall B i) = 0
  pin_equation : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
    -deriv (deriv pin) x + B.potential x * pin x = 0
  inward_flux : inwardEnergy = bufferSign i * deriv pin (bufferCut B i)
  inward_energy : inwardEnergy =
    ∫ x in min (bufferCut B i) (bufferInnerWall B i)..
      max (bufferCut B i) (bufferInnerWall B i),
        deriv pin x ^ 2 + B.potential x * pin x ^ 2
  inward_lower : B.mass i / C ≤ inwardEnergy
  inward_upper : inwardEnergy ≤ C * B.mass i
  outward_lower : B.mass i / C ≤ outwardEnergy
  outward_upper : outwardEnergy ≤ C * B.mass i
  p_regular : ∀ x ∈ Icc B.l B.h, ContDiffAt ℝ ∞ p x
  field_ae : (field : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator p
  scalar_row : if B.bordered then ⟪B.border, field⟫_ℝ = 0 else scalar = 0
  equation : ∀ x ∈ Ioo B.l B.h,
    -deriv (deriv p) x + B.potential x * p x + scalar * B.borderFunction x = 0
  trace : ∀ k, p (bufferCut B k) = if i = k then 1 else 0
  leading : RadialL2
  forcing : RadialL2
  leading_ae : (leading : ℝ → ℝ) =ᵐ[volume]
    (Ioo B.l B.h).indicator (fun x => innerBufferCutoff B i x * pin x)
  forcing_ae : (forcing : ℝ → ℝ) =ᵐ[volume]
    (Ioo B.l B.h).indicator (innerBufferSource B i pin)
  decomposition : (field, scalar) = (leading, 0) - G (forcing, 0)
  leading_bound : ‖leading‖ ≤ sqrt inwardEnergy / B.mass i
  forcing_bound : ‖forcing‖ ≤ K * (1 + B.layerBound) *
    B.mass i ^ (3 / 2 : ℝ) * exp (-B.action i)

structure InnerBufferLocalizedData (B : BufferData) (C K : ℝ) where
  dirichlet : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ)
  dirichlet_bound : ‖dirichlet‖ ≤ B.B₀ + C * ∑ i, (B.mass i)⁻¹ ^ 2
  dirichlet_solves : ∀ F : RadialL2 × ℝ, (B.bordered = false → F.2 = 0) →
    ((F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) →
    BorderedIntervalGraph B.potential B.border B.bordered B.l B.h (dirichlet F) F
  dirichlet_unique : ∀ U F,
    BorderedIntervalGraph B.potential B.border B.bordered B.l B.h U F → dirichlet F = U
  column : (i : Fin 2) → InnerBufferLocalizedColumn B C K dirichlet i
  flux_error : ∀ i k,
    |(bufferSign i * deriv (column k).p (bufferCut B i) -
      (if i = k then (column i).inwardEnergy else 0)) /
      sqrt (((column i).inwardEnergy + (column i).outwardEnergy) *
        ((column k).inwardEnergy + (column k).outwardEnergy))| ≤
      C * B.B₀ * B.mass i * B.mass k * exp (-B.action i - B.action k)

/-- A single universal cutoff constant works for all positive-buffer
data. Neither the localized decomposition nor either norm bound is
an input to this construction. -/
theorem exists_innerBufferLocalizedData :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : BufferData) (C : ℝ),
      BufferHypotheses B → BufferCompressionConclusion B C →
        Nonempty (InnerBufferLocalizedData B C K) := by
  obtain ⟨C₁, hC₁, h₁⟩ := innerTransition_deriv_bounded
  obtain ⟨C₂, hC₂, h₂⟩ := innerTransition_second_deriv_bounded
  let K : ℝ := C₂ + 4 * C₁ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro B C hB hcompression
  rcases hcompression with
    ⟨G, hGnorm, hGsolve, hGunique, pin, pout, p, P, scalar, αin, αout,
      hpin, hp, _, _, herror⟩
  have hconstruct (i : Fin 2) :
      ∃ L f : RadialL2,
        ((L : ℝ → ℝ) =ᵐ[volume]
          (Ioo B.l B.h).indicator (fun x => innerBufferCutoff B i x * pin i x)) ∧
        ((f : ℝ → ℝ) =ᵐ[volume]
          (Ioo B.l B.h).indicator (innerBufferSource B i (pin i))) ∧
        (P i, scalar i) = (L, 0) - G (f, 0) := by
    rcases hpin i with
      ⟨hpinReg, _, _, _, hpinCutReg, _, hpinCut, _, _, _, hpinEq, _⟩
    rcases hp i with ⟨hpL, hpR, hpI, _, hPin, hPout, hrow, heq, htrace⟩
    exact innerBufferPoisson_cutoff_decomposition hB i G hpinReg hpinCutReg hpinCut
      hpinEq hpL hpR hpI hPin hPout hrow heq htrace hGunique
  choose L f hL hf hdec using hconstruct
  let columns : (i : Fin 2) → InnerBufferLocalizedColumn B C K G i := fun i => by
    rcases hpin i with
      ⟨hpinReg, _, hpinInt, _, hpinCutReg, _, hpinCut, hpinWall, _, _,
        hpinEq, _, hαinFlux, _, hαinEnergy, _, hαinLo, hαinHi, hαoutLo, hαoutHi⟩
    rcases hp i with ⟨hpL, hpR, hpI, _, hPin, hPout, hrow, heq, htrace⟩
    refine
      { pin := pin i
        p := p i
        field := P i
        scalar := scalar i
        inwardEnergy := αin i
        outwardEnergy := αout i
        pin_regular := hpinReg
        pin_cut_regular := hpinCutReg
        pin_cut := hpinCut
        pin_wall := hpinWall
        pin_equation := hpinEq
        inward_flux := hαinFlux
        inward_energy := hαinEnergy
        inward_lower := hαinLo
        inward_upper := hαinHi
        outward_lower := hαoutLo
        outward_upper := hαoutHi
        p_regular := innerPoisson_contDiff_closed hpL hpR hpI
        field_ae := innerPoisson_eq_indicator hPin hPout
        scalar_row := hrow
        equation := heq
        trace := htrace
        leading := L i
        forcing := f i
        leading_ae := hL i
        forcing_ae := hf i
        decomposition := hdec i
        leading_bound := innerBufferLeading_norm_bound hB i hpinInt hαinEnergy (L i) (hL i)
        forcing_bound := ?_ }
    have hs := innerBufferSource_L2_bound hB i hC₁ hC₂ h₁ h₂
      hpinReg hpinEq hpinCut hpinWall (f i) (hf i)
    have hLayer : 0 ≤ B.layerBound := hB.2.2.2.1.le
    have hconstant : C₂ + 2 * C₁ * (2 + B.layerBound) ≤ K * (1 + B.layerBound) := by
      dsimp only [K]
      nlinarith only [mul_nonneg hC₂ hLayer, mul_nonneg hC₁ hLayer, hLayer]
    have hm := buffer_mass_pos hB i
    exact hs.trans (by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      exact mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hm.le _))
  exact ⟨
    { dirichlet := G
      dirichlet_bound := hGnorm
      dirichlet_solves := hGsolve
      dirichlet_unique := hGunique
      column := columns
      flux_error := herror }⟩

end ContinuousFlexibility.Radial
