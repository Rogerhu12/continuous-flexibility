module

public import ContinuousFlexibility.Radial.OuterTailPointwiseBounds
public import ContinuousFlexibility.Radial.OuterKernelEnvelopeAlgebra

/-!
# A uniform physical two-point envelope for the actual deep inverse

All coefficient exponents are selected before the profile, frequency,
orientation, or tail entrance. The proof uses the actual initial and
ordinary resistances, the actual normalized Green pair, and its sharp
mass-resistance products. No pointwise kernel estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem exists_outerTailPointWeight_envelope_uniform
    {C : ℕ → ℝ} (hC0 : 0 < C 0) {b : ℝ} (hb : 0 < b) :
    ∃ L : ℝ, 0 < L ∧ ∀ (D : ReferenceData), AccumulatingProfileBounds D C → D.b = b →
      ∀ (T : DeepTailData), DeepTailHypotheses T →
      ∀ (right : Bool) (j start : ℕ), 2 ≤ j → 1 ≤ start →
      TailPhysicalRelation D T right j start →
      T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
      ∀ n : ℕ, outerTailPointWeight T n ≤ radialE (start + n) ^ L := by
  obtain ⟨A, hA, hblock⟩ := exists_outer_tail_blockWeight_envelope_uniform hC0 hb
  obtain ⟨B, hB, hinitial⟩ := exists_outer_tail_initialResistance_envelope_uniform hC0 hb
  refine ⟨2 + max A B, by have := le_max_left A B; linarith, ?_⟩
  intro D hC hDb T hT right j start hj hstart hphysical hclose n
  have hn : 1 ≤ start + n := hstart.trans (Nat.le_add_right _ _)
  have hleft := hblock D hC hDb T hT right j start hj hphysical hclose n hn
  have hright := (hinitial D hC hDb T hT right j start hj hstart hphysical hclose).trans
    (outer_envelope_index_mono (Nat.le_add_right start n) hB.le)
  exact (add_le_add hleft hright).trans (outer_envelope_sum hn)

/-- The physical kernel of the same actual deep inverse has the full
cubic attenuation, including the initial interval and all node points. -/
theorem exists_outer_physical_kernel_decay_uniform
    {C : ℕ → ℝ} (hC0 : 0 < C 0) {b : ℝ} (hb : 0 < b)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ L : ℝ, 0 < L ∧ ∀ (M : MorseChainData) (D : ReferenceData),
      AccumulatingProfileBounds D C → D.b = b →
      ∀ (right : Bool) (j start : ℕ) (entrance η K : ℝ)
        (F : MorsePhysicalTailBasis M D right j start entrance η K),
        DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K) →
        η ≤ 1 / 16 → 32 ≤ K → 2 ≤ j → 1 ≤ start →
        TailPhysicalRelation D (morsePhysicalDeepTail M D right j start entrance η K)
          right j start →
        (morsePhysicalDeepTail M D right j start entrance η K).endpoint -
          (morsePhysicalDeepTail M D right j start entrance η K).entrance ≤
            (2 * (j : ℝ) ^ 2)⁻¹ →
        (∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
          A * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤
            (morsePhysicalDeepTail M D right j start entrance η K).Λ *
              tailMass (morsePhysicalDeepTail M D right j start entrance η K) (k + 1) *
              tailResistance (morsePhysicalDeepTail M D right j start entrance η K) k) →
        ∀ m n : ℕ, ∀ x y : ℝ,
          OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) m x →
          OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) n y →
          |F.Q (min (outerOutwardLogRadius right x) (outerOutwardLogRadius right y)) *
            F.P (max (outerOutwardLogRadius right x) (outerOutwardLogRadius right y))| ≤
              radialE (start + m) ^ L * radialE (start + n) ^ L *
                exp (-|radialS (start + m) - radialS (start + n)|) := by
  obtain ⟨B, hB, hweight⟩ := exists_outerTailPointWeight_envelope_uniform hC0 hb
  let P : ℝ := 144 * exp 2
  let L : ℝ := P + B + outerPhysicalDecayCost A
  have hP : 0 < P := by dsimp only [P]; positivity
  have hcost := outerPhysicalDecayCost_nonneg hA
  have hL : 0 < L := by dsimp only [L]; linarith only [hP, hB, hcost]
  refine ⟨L, hL, ?_⟩
  intro M D hC hDb right j start entrance η K F hT hη hK hj hstart hphysical hclose hden
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hord (m n : ℕ) (x y : ℝ) (hmn : m ≤ n)
      (hx : OuterTailPoint T m x) (hy : OuterTailPoint T n y) :
      |F.Q (min (outerOutwardLogRadius right x) (outerOutwardLogRadius right y)) *
        F.P (max (outerOutwardLogRadius right x) (outerOutwardLogRadius right y))| ≤
          radialE (start + m) ^ L * radialE (start + n) ^ L *
            exp (-|radialS (start + m) - radialS (start + n)|) := by
    have hlog := F.log_point_kernel_envelope hT hη hK hA hden hmn hx hy
    change |F.logQ (min x y) * F.logP (max x y)| ≤
      144 * outerTailPointWeight T m *
        (radialE (start + n) ^ outerPhysicalDecayCost A *
          exp (-|radialS (start + n) - radialS (start + m)|)) at hlog
    rw [abs_sub_comm (radialS (start + n)) (radialS (start + m))] at hlog
    have hphys := outer_tail_physical_kernel_bound hC.1 hj hphysical hclose
      (outerTailPoint_mem hT hx) (outerTailPoint_mem hT hy) hlog
    have hw := hweight D hC hDb T hT right j start hj hstart hphysical hclose m
    have hE : 0 ≤ radialE (start + n) ^ outerPhysicalDecayCost A *
        exp (-|radialS (start + m) - radialS (start + n)|) :=
      mul_nonneg (rpow_nonneg (show 0 ≤ radialE (start + n) from (exp_pos _).le) _)
        (exp_pos _).le
    change |outerOutwardDirichletKernel D right j F.logQ F.logP
      (outerOutwardLogRadius right x) (outerOutwardLogRadius right y)| ≤ _
    calc
      _ ≤ exp 2 * (144 * outerTailPointWeight T m *
          (radialE (start + n) ^ outerPhysicalDecayCost A *
            exp (-|radialS (start + m) - radialS (start + n)|))) := hphys
      _ ≤ exp 2 * (144 * radialE (start + m) ^ B *
          (radialE (start + n) ^ outerPhysicalDecayCost A *
            exp (-|radialS (start + m) - radialS (start + n)|))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) hE)
          (exp_pos 2).le
      _ = (P * radialE (start + m) ^ B * radialE (start + n) ^ outerPhysicalDecayCost A) *
          exp (-|radialS (start + m) - radialS (start + n)|) := by dsimp only [P]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (outer_envelope_pair_prefactor
          (hstart.trans (Nat.le_add_right start m)) hP.le hB.le hcost) (exp_pos _).le
  intro m n x y hx hy
  rcases le_total m n with hmn | hnm
  · exact hord m n x y hmn hx hy
  · have h := hord n m y x hnm hy hx
    rw [min_comm (outerOutwardLogRadius right y) (outerOutwardLogRadius right x),
      max_comm (outerOutwardLogRadius right y) (outerOutwardLogRadius right x),
      abs_sub_comm (radialS (start + n)) (radialS (start + m)),
      mul_comm (radialE (start + n) ^ L) (radialE (start + m) ^ L)] at h
    exact h

end ContinuousFlexibility.Radial
