import ContinuousFlexibility.Radial.R07DeepTailData

/-!
# Exact masses and resistances of the concrete logarithmic chain

At frequency two the normalized logarithmic quantities are the radial
quantities in `MorseMassResistanceBounds`, multiplied by the endpoint
normalization.  The left gap following mass interval `n` uses the original
gap with index `n+1`.  The initial left gap uses the original starting gap.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_density_two_mass_change_at_radii {D : ReferenceData} (right : Bool)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 < (if right then D.b else D.a)) (hw : Continuous D.w) :
    (∫ x in r07OutwardLog right a..r07OutwardLog right b, r07PhysicalDensity D right 2 x) =
      ((if right then D.b else D.a) ^ 8)⁻¹ * r07OutwardSign right *
        (∫ r in a..b, D.w r * r ^ 6) := by
  simpa only [r07_radius_outwardLog right ha, r07_radius_outwardLog right hb] using
    r07_density_two_mass_change right (r07OutwardLog right a) (r07OutwardLog right b) he hw

theorem r07_density_two_resistance_change_at_radii {D : ReferenceData} (right : Bool)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 < (if right then D.b else D.a)) (hw : Continuous D.w)
    (hw0 : ∀ r ∈ uIcc a b, D.w r ≠ 0) :
    (∫ x in r07OutwardLog right a..r07OutwardLog right b,
      (r07PhysicalDensity D right 2 x)⁻¹) =
      (if right then D.b else D.a) ^ 8 * r07OutwardSign right *
        (∫ r in a..b, (D.w r * r ^ 8)⁻¹) := by
  have hc := r07_density_two_resistance_change right
    (r07OutwardLog right a) (r07OutwardLog right b) he hw
    (fun x hx => hw0 _ (r07_radius_mem_log_interval ha hb hx))
  simpa only [r07_radius_outwardLog right ha, r07_radius_outwardLog right hb] using hc

theorem r07_profile_ne_zero_between {D : ReferenceData} (hD : RadialProfileGeometry D)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) :
    ∀ r ∈ uIcc a b, D.w r ≠ 0 :=
  fun r hr => (hD.2.2.2.2.1 r (ordConnected_Ioo.uIcc_subset ha hb hr)).ne'

/-- Reversing the radial endpoints on the left cancels the outward
orientation sign. -/
theorem r07_oriented_integral (right : Bool) (a b : ℝ) (f : ℝ → ℝ) :
    r07OutwardSign right *
        (∫ r in (if right then a else b)..(if right then b else a), f r) =
      ∫ r in a..b, f r := by
  cases right
  · simp only [r07OutwardSign, Bool.false_eq_true, if_false, neg_one_mul]
    rw [intervalIntegral.integral_symm (a := b) (b := a), neg_neg]
  · simp only [r07OutwardSign, if_true, one_mul]

theorem r07_deepTail_cell_integrals {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {start : ℕ} (hstart : T.index ≤ start) (η K : ℝ) (n : ℕ) :
    let Q := r07DeepTailData T D right 2 start η K
    tailMass Q n = ((if right then D.b else D.a) ^ 8)⁻¹ *
        morseCellMass T D right (start + n) ∧
      tailInnerResistance Q n = (if right then D.b else D.a) ^ 8 *
        morseCellResistance T D right (start + n) := by
  have hD := r07_realization_geometry h
  have he : 0 < (if right then D.b else D.a) := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hn := hstart.trans (Nat.le_add_right start n)
  have hc := r07_chain_mass_nodes_core h right hn
  have hnode := hD.1.trans hc.1.1
  have hexit := hD.1.trans hc.2.1
  have hmass := r07_density_two_mass_change_at_radii right hnode hexit he hD.2.2.1.1.continuous
  have hres := r07_density_two_resistance_change_at_radii right hnode hexit he
    hD.2.2.1.1.continuous (r07_profile_ne_zero_between hD hc.1 hc.2)
  constructor
  · change (∫ x in r07OutwardLog right (r07MassNodeRadius T right (start + n))..
      r07OutwardLog right (r07MassExitRadius T right (start + n)),
      r07PhysicalDensity D right 2 x) = _
    rw [hmass]
    unfold r07MassNodeRadius r07MassExitRadius morseCellMass
    rw [mul_assoc, r07_oriented_integral]
  · change (∫ x in r07OutwardLog right (r07MassNodeRadius T right (start + n))..
      r07OutwardLog right (r07MassExitRadius T right (start + n)),
      (r07PhysicalDensity D right 2 x)⁻¹) = _
    rw [hres]
    unfold r07MassNodeRadius r07MassExitRadius morseCellResistance
    rw [mul_assoc, r07_oriented_integral]

def r07GapIndex (right : Bool) (n : ℕ) : ℕ := if right then n else n + 1

theorem r07_chain_gap_radii {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    r07MassExitRadius T right n =
        (if right then morseChainMassEnd T right (r07GapIndex right n)
          else morseChainResistanceEnd T right (r07GapIndex right n)) ∧
      r07MassNodeRadius T right (n + 1) =
        (if right then morseChainResistanceEnd T right (r07GapIndex right n)
          else morseChainMassEnd T right (r07GapIndex right n)) := by
  have he := r07_chain_resistance_ends h hn
  cases right
  · exact ⟨he.2.symm, rfl⟩
  · exact ⟨rfl, he.1.symm⟩

theorem r07_deepTail_gap_integrals {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {start : ℕ} (hstart : T.index ≤ start) (η K : ℝ) (n : ℕ) :
    let Q := r07DeepTailData T D right 2 start η K
    tailGapMass Q n = ((if right then D.b else D.a) ^ 8)⁻¹ *
        morseJoinMass T D right (r07GapIndex right (start + n)) ∧
      tailResistance Q n = (if right then D.b else D.a) ^ 8 *
        morseJoinResistance T D right (r07GapIndex right (start + n)) := by
  have hD := r07_realization_geometry h
  have he : 0 < (if right then D.b else D.a) := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hn := hstart.trans (Nat.le_add_right start n)
  have hnext := hn.trans (Nat.le_succ (start + n))
  have hc := (r07_chain_mass_nodes_core h right hn).2
  have hd := (r07_chain_mass_nodes_core h right hnext).1
  have hleft := hD.1.trans hc.1
  have hright := hD.1.trans hd.1
  have hmass := r07_density_two_mass_change_at_radii right hleft hright he hD.2.2.1.1.continuous
  have hres := r07_density_two_resistance_change_at_radii right hleft hright he
    hD.2.2.1.1.continuous (r07_profile_ne_zero_between hD hc hd)
  have hends := r07_chain_gap_radii h right hn
  constructor
  · change (∫ x in r07OutwardLog right (r07MassExitRadius T right (start + n))..
      r07OutwardLog right (r07MassNodeRadius T right (start + n + 1)),
      r07PhysicalDensity D right 2 x) = _
    rw [hmass, hends.1, hends.2]
    unfold morseJoinMass
    rw [mul_assoc, r07_oriented_integral]
  · change (∫ x in r07OutwardLog right (r07MassExitRadius T right (start + n))..
      r07OutwardLog right (r07MassNodeRadius T right (start + n + 1)),
      (r07PhysicalDensity D right 2 x)⁻¹) = _
    rw [hres, hends.1, hends.2]
    unfold morseJoinResistance
    rw [mul_assoc, r07_oriented_integral]

theorem r07_deepTail_initial_integrals {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    let Q := r07DeepTailData T D right 2 start η K
    tailInitialGapMass Q =
        (if right then 0 else ((if right then D.b else D.a) ^ 8)⁻¹ *
          morseJoinMass T D right start) ∧
      tailInitialResistance Q =
        (if right then 0 else (if right then D.b else D.a) ^ 8 *
          morseJoinResistance T D right start) := by
  have hD := r07_realization_geometry h
  cases right
  · have hc := r07_chain_resistanceEnd_core h false hstart
    have hd := (r07_chain_mass_cuts_core h false hstart.le).2.1
    have hleft := hD.1.trans hc.1
    have hright := hD.1.trans hd.1
    have hmass := r07_density_two_mass_change_at_radii false hleft hright hD.1
      hD.2.2.1.1.continuous
    have hres := r07_density_two_resistance_change_at_radii false hleft hright hD.1
      hD.2.2.1.1.continuous (r07_profile_ne_zero_between hD hc hd)
    constructor
    · change (∫ x in r07OutwardLog false (morseChainResistanceEnd T false start)..
        r07OutwardLog false (morseChainMassEnd T false start),
        r07PhysicalDensity D false 2 x) = (D.a ^ 8)⁻¹ * morseJoinMass T D false start
      rw [hmass]
      unfold morseJoinMass
      rw [mul_assoc]
      exact congrArg (fun z : ℝ => (D.a ^ 8)⁻¹ * z)
        (r07_oriented_integral false (morseChainMassEnd T false start)
          (morseChainResistanceEnd T false start) (fun r => D.w r * r ^ 6))
    · change (∫ x in r07OutwardLog false (morseChainResistanceEnd T false start)..
        r07OutwardLog false (morseChainMassEnd T false start),
        (r07PhysicalDensity D false 2 x)⁻¹) = D.a ^ 8 * morseJoinResistance T D false start
      rw [hres]
      unfold morseJoinResistance
      rw [mul_assoc]
      exact congrArg (fun z : ℝ => D.a ^ 8 * z)
        (r07_oriented_integral false (morseChainMassEnd T false start)
          (morseChainResistanceEnd T false start) (fun r => (D.w r * r ^ 8)⁻¹))
  · simp only [r07DeepTailData, tailInitialGapMass, tailInitialResistance, if_true,
      Nat.add_zero, intervalIntegral.integral_same, and_self]

end ContinuousFlexibility.Radial
