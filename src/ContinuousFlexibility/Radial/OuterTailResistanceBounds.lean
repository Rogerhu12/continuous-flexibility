module

public import ContinuousFlexibility.Radial.OuterTailDensityBounds
public import ContinuousFlexibility.Radial.OuterLocalizationWeights
public import ContinuousFlexibility.Radial.TailFundamentalGreenBounds

/-!
# Coefficient bounds for the actual deep-tail Green block weight

The whole logarithmic tail is short in the transition band.  The actual
reciprocal-density bound therefore controls both resistance integrals.
The remaining inverse-mass term is bounded by the actual resistance using
the large mass-resistance hypothesis, with no new spectral estimate assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem outer_tail_length_le_one {T : DeepTailData} {j : ℕ} (hj : 2 ≤ j)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    T.endpoint - T.entrance ≤ 1 := by
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hlarge : (1 : ℝ) ≤ 2 * (j : ℝ) ^ 2 := by nlinarith
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlarge
  exact hclose.trans (by simpa only [one_div, inv_one] using hh)

theorem outer_tail_short_interval_resistance {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a b B : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ Ico T.entrance T.endpoint)
    (hlen : b - a ≤ 1) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Ioo a b, (T.p x)⁻¹ ≤ B) :
    (∫ x in a..b, (T.p x)⁻¹) ≤ B := by
  have hcont : ContinuousOn (fun x => (T.p x)⁻¹) (Icc a b) :=
    ((deepTail_contDiffOn hT).continuousOn.mono hsub).inv₀
      (fun x hx => (deepTail_pos hT x (hsub hx)).ne')
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcont)
    (intervalIntegrable_const (μ := volume) (c := B)) hbound
  calc
    _ ≤ (b - a) * B := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hlen hB
    _ = B := one_mul B

theorem outer_tail_reciprocal_density_edge_bound
    {D : ReferenceData} {T : DeepTailData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) (hT : DeepTailHypotheses T)
    {right : Bool} {j start : ℕ} (hj : 2 ≤ j)
    (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (T.node n) (T.node (n + 1))) :
    (T.p x)⁻¹ ≤ exp 1 * D.b * (C 0 * radialE (start + n + 1) ^ (C 0)) := by
  obtain ⟨m, hm, _, hi⟩ := tailPhysicalEdge_label hphysical n ⟨x, hx, rfl⟩
  have hxT : x ∈ Ioo T.entrance T.endpoint :=
    ⟨(deepTail_entrance_le_node hT n).trans_lt hx.1,
      hx.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
  have hC0 : 0 < C 0 := hC.2.2.1 0
  have hb : 0 < D.b := hC.1.1.trans hC.1.2.1
  apply (outer_tail_reciprocal_density_cell_bound hC hj hphysical hclose hxT hm).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (exp_pos 1).le hb.le)
  apply mul_le_mul_of_nonneg_left _ hC0.le
  rw [outer_radialE_rpow, outer_radialE_rpow]
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (radialQ_monotone hi) hC0.le)

/-- Both actual resistance integrals have the same coefficient envelope. -/
theorem outer_tail_resistances_le
    {D : ReferenceData} {T : DeepTailData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) (hT : DeepTailHypotheses T)
    {right : Bool} {j start : ℕ} (hj : 2 ≤ j)
    (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) (n : ℕ) :
    let B := exp 1 * D.b * (C 0 * radialE (start + n + 1) ^ (C 0))
    tailInnerResistance T n ≤ B ∧ tailResistance T n ≤ B := by
  let B := exp 1 * D.b * (C 0 * radialE (start + n + 1) ^ (C 0))
  have hC0 : 0 < C 0 := hC.2.2.1 0
  have hb : 0 < D.b := hC.1.1.trans hC.1.2.1
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg (exp_pos 1).le hb.le)
      (mul_nonneg hC0.le
        (rpow_nonneg (show 0 ≤ radialE (start + n + 1) from (exp_pos _).le) _))
  have ho := hT.2.2.2.2.2.2.2.2.2.2 n
  have he := deepTail_entrance_le_node hT n
  have hend := deepTail_node_lt_endpoint hT (n + 1)
  have hlen := outer_tail_length_le_one hj hclose
  have hpoint (x : ℝ) (hx : x ∈ Ioo (T.node n) (T.node (n + 1))) : (T.p x)⁻¹ ≤ B :=
    outer_tail_reciprocal_density_edge_bound hC hT hj hphysical hclose n hx
  constructor
  · apply outer_tail_short_interval_resistance hT ho.1.le
      (fun x hx => tailActualEdge_interval_subset hT n ⟨hx.1, hx.2.trans ho.2.1.le⟩)
      (by linarith only [he, hend, ho.2.1, hlen]) hB
    intro x hx
    exact hpoint x ⟨hx.1, hx.2.trans ho.2.1⟩
  · apply outer_tail_short_interval_resistance hT ho.2.1.le
      (fun x hx => tailActualEdge_interval_subset hT n ⟨ho.1.le.trans hx.1, hx.2⟩)
      (by linarith only [he, hend, ho.1, hlen]) hB
    intro x hx
    exact hpoint x ⟨ho.1.trans hx.1, hx.2⟩

theorem outer_tail_inverse_mass_le_resistance {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    (T.Λ * tailMass T n)⁻¹ ≤ tailResistance T n := by
  have hmass := mul_pos hT.2.2.1 (tailMass_pos hT n)
  have hlarge := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1
  have hK : 1 ≤ T.K := hT.2.2.2.2.2.2.1.le
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hmass).mpr
  calc
    1 ≤ T.K := hK
    _ ≤ T.Λ * tailMass T n * tailResistance T n := hlarge
    _ = tailResistance T n * (T.Λ * tailMass T n) := by ring

/-- The coefficient exponent is chosen before the profile in a family
with common coefficient constants and right endpoint. -/
theorem exists_outer_tail_blockWeight_envelope_uniform
    {C : ℕ → ℝ} (hC0 : 0 < C 0) {b : ℝ} (hb : 0 < b) :
    ∃ L : ℝ, 0 < L ∧ ∀ (D : ReferenceData), AccumulatingProfileBounds D C → D.b = b →
      ∀ (T : DeepTailData), DeepTailHypotheses T →
      ∀ (right : Bool) (j start : ℕ), 2 ≤ j →
      TailPhysicalRelation D T right j start →
      T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
      ∀ n : ℕ, 1 ≤ start + n →
        tailFundamentalGreenBlockWeight T n ≤ radialE (start + n) ^ L := by
  obtain ⟨A, hA, hshift⟩ := outer_coefficient_weight_nearby hC0.le
  let B := 1 + 3 * (exp 1 * b * C 0)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B + A, add_pos hB hA, ?_⟩
  intro D hC hDb T hT right j start hj hphysical hclose n hn
  obtain ⟨hI, hR⟩ := outer_tail_resistances_le hC hT hj hphysical hclose n
  change tailInnerResistance T n ≤
    exp 1 * D.b * (C 0 * radialE (start + n + 1) ^ (C 0)) at hI
  change tailResistance T n ≤
    exp 1 * D.b * (C 0 * radialE (start + n + 1) ^ (C 0)) at hR
  rw [hDb] at hI hR
  have hmass := outer_tail_inverse_mass_le_resistance hT n
  have hs := hshift (start + n + 1) (start + n) hn (by omega)
  have hE : 1 ≤ radialE (start + n) ^ A := by
    rw [outer_radialE_rpow]
    exact one_le_exp_iff.mpr (mul_nonneg hA.le (radialQ_nonneg _))
  have hfactor : 0 ≤ exp 1 * b * C 0 := by positivity
  have hshifted := mul_le_mul_of_nonneg_left hs hfactor
  have hblock : tailFundamentalGreenBlockWeight T n ≤ B * radialE (start + n) ^ A := by
    dsimp only [tailFundamentalGreenBlockWeight, B]
    nlinarith only [hI, hR, hmass, hshifted, hE]
  calc
    _ ≤ B * radialE (start + n) ^ A := hblock
    _ ≤ radialE (start + n) ^ B * radialE (start + n) ^ A :=
      mul_le_mul_of_nonneg_right (outer_prefactor_le_envelope hn hB.le)
        (rpow_nonneg (exp_pos _).le _)
    _ = _ := (rpow_add (exp_pos _) B A).symm

/-- The block weight is a coefficient power, uniformly in frequency and entrance. -/
theorem exists_outer_tail_blockWeight_envelope
    {D : ReferenceData} {C : ℕ → ℝ} (hC : AccumulatingProfileBounds D C) :
    ∃ L : ℝ, 0 < L ∧ ∀ (T : DeepTailData), DeepTailHypotheses T →
      ∀ (right : Bool) (j start : ℕ), 2 ≤ j →
      TailPhysicalRelation D T right j start →
      T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
      ∀ n : ℕ, 1 ≤ start + n →
        tailFundamentalGreenBlockWeight T n ≤ radialE (start + n) ^ L := by
  obtain ⟨L, hL, hbound⟩ := exists_outer_tail_blockWeight_envelope_uniform
    (hC.2.2.1 0) (hC.1.1.trans hC.1.2.1)
  exact ⟨L, hL, hbound D hC rfl⟩

end ContinuousFlexibility.Radial
