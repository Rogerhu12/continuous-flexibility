import ContinuousFlexibility.Analysis.N04RealizationFactoredRootTraceDirections
import ContinuousFlexibility.Analysis.N04bOpticalCoefficientVariation
import ContinuousFlexibility.Analysis.N04bRootGermCollar
import ContinuousFlexibility.Analysis.N06RootLogHeight

/-!
# Boundary jets of the selected physical root factors

The smooth drift and speed factor retained by the actual root collar
are compared with the original fields on the positive physical side.
Smooth one-sided uniqueness identifies all ordinary boundary jets.
The fixed reference division factor is chosen before the state; no
parameter regularity of a selected collar or flow extension is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem originalCharacteristic_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hneg : deriv (stateProfile D S C z.1) p.1 < 0) :
    n04bCharacteristicDrift (originalCoefficients D S C z) p =
        characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) p ∧
      n04bCharacteristicHalfGap (originalCoefficients D S C z) p =
        characteristicSpeed (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hr : 0 < p.1 := hgeom.1.trans hp.1.1
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hgeom.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hb := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hw).mp
      (lt_of_lt_of_le (by norm_num) hb.2.2.1)
  have hdisc : 0 < polarDiscriminant
      (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num) hb.2.2.2.2.1
  exact ⟨(n04b_characteristicDrift_eq_corrected_ratio
      ((contDiff_stateHeight_of_n01 hS hT hN z).contDiffAt.of_le (by simp))
      hr.ne' hdisc hQ).symm,
    (n04b_characteristicSpeed_eq_corrected_ratio
      ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) p.1)
      hr hw hneg hdisc hQ).symm⟩

/-- One fixed original division factor identifies the boundary jets of
every supplied smooth pair with the retained physical identities. -/
theorem n04Realization_exists_selectedRootFactor_trace_model
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε r σ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (hsign : σ * deriv (deriv D.w) r < 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ 0 < g 0 ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ (ρ : ℝ) (d c : PolarPoint → ℝ), 0 < ρ →
        ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
          Real.sqrt x * c (x, θ) =
            n04bCharacteristicHalfGap (L.coefficients z) (rootProfileShift r σ (x, θ))) →
        (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
          d (x, θ) =
            σ * n04bCharacteristicDrift (L.coefficients z) (rootProfileShift r σ (x, θ))) →
        ∀ n : ℕ, ∀ θ : ℝ,
          radialBoundaryJet d 0 n θ =
            radialBoundaryJet (orientedCharacteristicDrift
              (stateProfile D S C z.1) (stateHeight D S C z) r σ) 0 n θ ∧
          radialBoundaryJet c 0 n θ =
            radialBoundaryJet (factoredCharacteristicSpeed D.w g
              (stateProfile D S C z.1) (stateHeight D S C z) r σ) 0 n θ := by
  have hN : N01Properties D T S C base loss ε := h03.1.1
  obtain ⟨g, δ, hg, hg0, hδ, _, hstrip, hstates⟩ :=
    n01_exists_common_characteristic_root_strip hS hT hN hr hroot hsign
  refine ⟨g, hg, hg0, ?_⟩
  intro z hz hs ρ d c hρ hd hc hgap hdrift n θ
  let w : ℝ → ℝ := stateProfile D S C z.1
  let H : PolarPoint → ℝ := stateHeight D S C z
  let d₀ : PolarPoint → ℝ := orientedCharacteristicDrift w H r σ
  let c₀ : PolarPoint → ℝ := factoredCharacteristicSpeed D.w g w H r σ
  have hdata := hstates z hz hs
  have hmem : (0, θ) ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ) :=
    ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, mem_univ _⟩
  have hd₀ : ContDiffAt ℝ ∞ d₀ (0, θ) :=
    hdata.2.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmem)
  have hc₀ : ContDiffAt ℝ ∞ c₀ (0, θ) :=
    hdata.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmem)
  have hshift : ContinuousAt (fun x : ℝ => rootProfileShift r σ (x, θ)) 0 :=
    ((continuous_const.add (continuous_const.mul continuous_id)).prodMk continuous_const).continuousAt
  have ht : Tendsto (fun x : ℝ => rootProfileShift r σ (x, θ))
      (𝓝 0) (𝓝 (r, θ)) := by
    simpa only [rootProfileShift, mul_zero, add_zero] using hshift.tendsto
  have hcoeff := h03.2.2.2.1 z hz hs (r, θ) ⟨hr, mem_univ _⟩ hroot
  have heq : ∀ᶠ x : ℝ in 𝓝 0, 0 < x →
      d (x, θ) = d₀ (x, θ) ∧ c (x, θ) = c₀ (x, θ) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ,
      Iio_mem_nhds hρ, hcoeff.1.comp_tendsto ht, hcoeff.2.comp_tendsto ht]
      with x hx hxρ hb hc' hxpos
    let p : PolarPoint := rootProfileShift r σ (x, θ)
    have hp : p ∈ annularOpen D := ⟨(hstrip x hx).1, mem_univ _⟩
    have hf := hdata.2.2 (x, θ) ⟨hx, mem_univ _⟩
    have hspeed : characteristicSpeed w H p = Real.sqrt x * c₀ (x, θ) :=
      hf.2.2.2 hxpos.le
    have hspeedpos : 0 < characteristicSpeed w H p := by
      rw [hspeed]
      exact mul_pos (Real.sqrt_pos.mpr hxpos) hf.1
    have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
    have hrp : 0 < p.1 := hgeom.1.trans hp.1.1
    have hwp : 0 < w p.1 :=
      mul_pos (hgeom.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
    have hneg : deriv w p.1 < 0 := by
      by_contra hn
      have hrad : -w p.1 * deriv w p.1 / p.1 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hwp.le)
            (le_of_not_gt hn)) hrp.le
      have hzero : characteristicSpeed w H p = 0 := by
        simp only [characteristicSpeed, Real.sqrt_eq_zero_of_nonpos hrad,
          zero_mul, zero_div]
      exact hspeedpos.ne' hzero
    have hfields := originalCharacteristic_fields hT hS hN hz hs hp hneg
    have ha := h03.2.1 z hz hs p
    have hdmatch : n04bCharacteristicDrift (L.coefficients z) p =
        characteristicDrift w H p := by
      rw [n04bCharacteristicDrift, ha, hb]
      exact hfields.1
    have hcmatch : n04bCharacteristicHalfGap (L.coefficients z) p =
        Real.sqrt x * c₀ (x, θ) := by
      rw [n04bCharacteristicHalfGap, ha, hb, hc']
      exact hfields.2.trans hspeed
    constructor
    · exact (hdrift x ⟨hxpos.le, hxρ.le⟩ θ).trans
        (congrArg (fun t : ℝ => σ * t) hdmatch)
    · exact mul_left_cancel₀ (Real.sqrt_pos.mpr hxpos).ne'
        ((hgap x ⟨hxpos.le, hxρ.le⟩ θ).trans hcmatch)
  have hline : ContDiffAt ℝ ∞ (fun x : ℝ => ((x, θ) : PolarPoint)) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  constructor
  · exact n06_iteratedDeriv_eq_of_positive_germ
      (hd.contDiffAt.comp 0 hline) (hd₀.comp 0 hline)
      (heq.mono (fun x hx hxpos => (hx hxpos).1)) n
  · exact n06_iteratedDeriv_eq_of_positive_germ
      (hc.contDiffAt.comp 0 hline) (hc₀.comp 0 hline)
      (heq.mono (fun x hx hxpos => (hx hxpos).2)) n

end ContinuousFlexibility.Analysis
