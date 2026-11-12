import ContinuousFlexibility.Analysis.N04bRootFieldExtension
import ContinuousFlexibility.Analysis.N04bActualCharacteristics
import Mathlib.Tactic.LinearCombination

/-!
# Symmetric global factors of the actual root characteristic field

Odd/even averaging imposes the required reflection symmetry on the global
extensions. Both actual characteristic identities survive the averaging,
because N03 interchanges the two physical characteristic speeds under
angular reflection. No division by the square-root coordinate is used,
so the identities continue to hold at the root itself.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual corrected root field admits globally smooth periodic odd
drift and positive even square-root factor. Both physical characteristic
equations hold throughout a nontrivial closed collar. -/
theorem n04b_exists_symmetric_corrected_root_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ σ : ℝ} (hr₀ : r₀ ∈ Ioo D.a D.b)
    (hroot : deriv D.w r₀ = 0) (hsign : σ * deriv (deriv D.w) r₀ < 0) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ r θ, d (r, -θ) = -d (r, θ)) ∧
      (∀ r θ, c₀ (r, -θ) = c₀ (r, θ)) ∧
      (∀ p, 0 < c₀ p) ∧
      ∀ p ∈ Icc (0 : ℝ) ρ ×ˢ (univ : Set ℝ),
        rootProfileShift r₀ σ p ∈ annularOpen D ∧
          σ * minusCharacteristicSpeed (L.coefficients z) (rootProfileShift r₀ σ p) =
            d p - σ * Real.sqrt p.1 * c₀ p ∧
          σ * plusCharacteristicSpeed (L.coefficients z) (rootProfileShift r₀ σ p) =
            d p + σ * Real.sqrt p.1 * c₀ p := by
  obtain ⟨ρ, d, c₀, hρ, hd, hc, hdp, hcp, hcpos, hphysical⟩ :=
    n04b_exists_extended_corrected_root_factors hT hS h03 hL hz hs hr₀ hroot hsign
  let ds : PolarPoint → ℝ := fun p => (d p - d (p.1, -p.2)) / 2
  let cs : PolarPoint → ℝ := fun p => (c₀ p + c₀ (p.1, -p.2)) / 2
  have hreflection : ContDiff ℝ ∞ (fun p : PolarPoint => (p.1, -p.2)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  have hds : ContDiff ℝ ∞ ds := (hd.sub (hd.comp hreflection)).div_const 2
  have hcs : ContDiff ℝ ∞ cs := (hc.add (hc.comp hreflection)).div_const 2
  have hreflect_period (f : ℝ → ℝ) (hf : Function.Periodic f Real.pi) (θ : ℝ) :
      f (-(θ + Real.pi)) = f (-θ) := by
    have hh := hf (-(θ + Real.pi))
    have harg : -(θ + Real.pi) + Real.pi = -θ := by ring
    rw [harg] at hh
    exact hh.symm
  refine ⟨ρ, ds, cs, hρ, hds, hcs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r θ
    dsimp only [ds]
    have hperiod : d (r, θ + Real.pi) = d (r, θ) := hdp r θ
    have hreflect : d (r, -(θ + Real.pi)) = d (r, -θ) :=
      hreflect_period (fun x => d (r, x)) (hdp r) θ
    rw [hperiod, hreflect]
  · intro r θ
    dsimp only [cs]
    have hperiod : c₀ (r, θ + Real.pi) = c₀ (r, θ) := hcp r θ
    have hreflect : c₀ (r, -(θ + Real.pi)) = c₀ (r, -θ) :=
      hreflect_period (fun x => c₀ (r, x)) (hcp r) θ
    rw [hperiod, hreflect]
  · intro r θ
    dsimp only [ds]
    rw [neg_neg]
    ring
  · intro r θ
    dsimp only [cs]
    rw [neg_neg]
    ring
  · intro p
    exact div_pos (add_pos (hcpos p) (hcpos (p.1, -p.2))) (by norm_num)
  · intro p hp
    have hpr : (p.1, -p.2) ∈ Icc (0 : ℝ) ρ ×ˢ (univ : Set ℝ) :=
      ⟨hp.1, mem_univ _⟩
    have hh := hphysical p hp
    have hr := hphysical (p.1, -p.2) hpr
    have hsymmetric := h03.2.2.2.2.1 z hz hs (r₀ + σ * p.1) p.2
    have hreflect := n04b_characteristic_reflection (L.coefficients z)
      (r₀ + σ * p.1) p.2 hsymmetric.1 hsymmetric.2.1 hsymmetric.2.2
    have hplus_reflect :
        plusCharacteristicSpeed (L.coefficients z) (r₀ + σ * p.1, -p.2) =
          -minusCharacteristicSpeed (L.coefficients z) (r₀ + σ * p.1, p.2) := by
      change n04bCharacteristicDrift (L.coefficients z) (r₀ + σ * p.1, -p.2) +
        n04bCharacteristicHalfGap (L.coefficients z) (r₀ + σ * p.1, -p.2) =
        -(n04bCharacteristicDrift (L.coefficients z) (r₀ + σ * p.1, p.2) -
          n04bCharacteristicHalfGap (L.coefficients z) (r₀ + σ * p.1, p.2))
      rw [hreflect.1, hreflect.2.1]
      ring
    have hm := hh.2.1
    have hplus := hh.2.2
    have hmr := hr.2.1
    have hplusr := hr.2.2
    dsimp only [rootProfileShift] at hm hplus hmr hplusr
    rw [hreflect.2.2] at hmr
    rw [hplus_reflect] at hplusr
    refine ⟨hh.1, ?_, ?_⟩
    · dsimp only [rootProfileShift, ds, cs]
      linear_combination (1 / 2 : ℝ) * hm - (1 / 2 : ℝ) * hplusr
    · dsimp only [rootProfileShift, ds, cs]
      linear_combination (1 / 2 : ℝ) * hplus - (1 / 2 : ℝ) * hmr

end ContinuousFlexibility.Analysis
