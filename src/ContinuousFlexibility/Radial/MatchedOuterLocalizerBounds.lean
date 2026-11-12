import ContinuousFlexibility.Radial.OuterDeepUniformProduct
import ContinuousFlexibility.Radial.OuterPhysicalKernelEnvelope
import ContinuousFlexibility.Radial.OuterPhysicalNaturalEnvelope
import ContinuousFlexibility.Radial.OuterLocalizerCutoff

/-!
# The original localizers in the actual physical tail envelopes

The physical point labels are recovered from the supplied nonzero
localizers. Initial resistance points and node points use the same
cover, so no cell is assumed to lie in a single open edge. The resulting
coefficient exponents are chosen before the profile and frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem MorseOuterLocalizerLabels.tail_point
    {M : MorseChainData} {D : ReferenceData} {N : ℕ}
    (hlabels : MorseOuterLocalizerLabels M D N)
    (right : Bool) (j : ℕ) (η K : ℝ) (n m : ℕ) (x : ℝ)
    (hx : OuterTailPoint (morsePhysicalDeepTail M D right j (N + 1)
      (morseOuterDeepEntrance M right N) η K) n x)
    (hθ : D.localizer m (tailPhysicalRadius right x) ≠ 0) :
    N + 1 + n ≤ D.cellIndex m + 2 ∧ D.cellIndex m ≤ N + 1 + n + 2 := by
  rcases hx with ⟨rfl, hx⟩ | hx
  · simpa only [Nat.add_zero] using hlabels.2.1 right j η K m x hx hθ
  · exact hlabels.1 right j η K n m x hx hθ

/-- The actual outward point has its original signed logarithmic coordinate. -/
theorem matchedOuter_tail_point_coordinates
    {D : ReferenceData} (hD : RadialProfileGeometry D) (right : Bool)
    {entrance x : ℝ} (hentry : 0 < entrance)
    (hx : x ∈ Ico (outerOutwardRadius right entrance)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    0 < outerOutwardRadius right x ∧
      tailPhysicalLog right (outerOutwardRadius right x) ∈
        Ico (tailPhysicalLog right entrance)
          (tailPhysicalLog right (tailPhysicalEndpoint D right)) ∧
      outerOutwardLogRadius right
        (tailPhysicalLog right (outerOutwardRadius right x)) = x := by
  have hc : 0 < outerOutwardRadius right x ∧
      tailPhysicalLog right (outerOutwardRadius right x) ∈
        Ico (tailPhysicalLog right entrance)
          (tailPhysicalLog right (tailPhysicalEndpoint D right)) := by
    simpa only [outerOutwardRadius_eq_sign] using
      outerTail_outward_log_mem hD right hentry
        (show x ∈ Ico (outerTailSign right * entrance)
          (outerTailSign right * tailPhysicalEndpoint D right) from
          by simpa only [outerOutwardRadius_eq_sign] using hx)
  refine ⟨hc.1, hc.2, ?_⟩
  rw [outerOutwardLogRadius, tailPhysicalRadius_log right hc.1, outerOutwardRadius_twice]

/-- The same actual deep kernel has a common envelope at the original
cell indices. This includes the initial gap and every node point. -/
theorem exists_matchedOuter_actual_tail_kernel_cell_exponent
    {C : ℕ → ℝ} (hC0 : 0 < C 0) {b : ℝ} (hb : 0 < b)
    {Ad : ℝ} (hAd : 0 ≤ Ad) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (M : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData)
        (h : MorseChainRealization M σ D C), D.b = b →
      ∀ (N : ℕ), M.index + 3 ≤ N → MorseOuterLocalizerLabels M D N →
      ∀ (right : Bool) (j : ℕ) (η K : ℝ)
        (F : MorsePhysicalTailBasis M D right j (N + 1)
          (morseOuterDeepEntrance M right N) η K),
        let T := morsePhysicalDeepTail M D right j (N + 1)
          (morseOuterDeepEntrance M right N) η K
        DeepTailHypotheses T → η ≤ 1 / 16 → 32 ≤ K → 2 ≤ j →
        TailPhysicalRelation D T right j (N + 1) →
        T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
        (∀ k, exp (2 * ((N + 1 + k : ℕ) : ℝ) ^ 2 -
          Ad * (((N + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + 1 + k : ℕ))) ≤
          T.Λ * tailMass T (k + 1) * tailResistance T k) →
        ∀ (k m : ℕ) (x y : ℝ),
          x ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
          y ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
          D.localizer k (outerOutwardRadius right x) ≠ 0 →
          D.localizer m (outerOutwardRadius right y) ≠ 0 →
          |F.Q (min x y) * F.P (max x y)| ≤
            exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
              |radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
  obtain ⟨B, hB, hkernel⟩ := exists_outer_physical_kernel_decay_uniform hC0 hb hAd
  obtain ⟨A, hA, hshift⟩ := outer_localized_envelope_shift hB.le
  refine ⟨A, hA, ?_⟩
  intro M σ D h hDb N hN hlabels right j η K F
  dsimp only
  intro hT hη hK hj hphysical hclose hden k m x y hx hy hθk hθm
  have hNi : M.index ≤ N := by omega
  have hentry : 0 < morseOuterDeepEntrance M right N :=
    h.geometry.1.trans (morseOuterDeepEntrance_mem_core h right N hNi).1
  have hxc := matchedOuter_tail_point_coordinates h.geometry right hentry hx
  have hyc := matchedOuter_tail_point_coordinates h.geometry right hentry hy
  obtain ⟨p, hp⟩ := exists_outerTailPoint hT hxc.2.1
  obtain ⟨q, hq⟩ := exists_outerTailPoint hT hyc.2.1
  have hkp := hlabels.tail_point right j η K p k _ hp (by
    rw [tailPhysicalRadius_log right hxc.1]
    exact hθk)
  have hmq := hlabels.tail_point right j η K q m _ hq (by
    rw [tailPhysicalRadius_log right hyc.1]
    exact hθm)
  have hraw := hkernel M D h.accumulating hDb right j (N + 1)
    (morseOuterDeepEntrance M right N) η K F hT hη hK hj (by omega)
    hphysical hclose hden p q _ _ hp hq
  rw [hxc.2.2, hyc.2.2] at hraw
  refine hraw.trans ((hshift (N + 1 + p) (N + 1 + q)
    (D.cellIndex k) (D.cellIndex m) (by omega) (by omega)
    (by omega) (by omega) hkp.1 hkp.2 hmq.1 hmq.2).trans_eq ?_)
  rw [outer_radialE_rpow, outer_radialE_rpow, ← exp_add, ← exp_add]
  congr 1 <;> ring

/-- The same normalized natural solution has a common actual-cell
envelope relative to the true transition index. -/
theorem exists_matchedOuter_actual_tail_natural_cell_exponent
    {Ad : ℝ} (hAd : 0 ≤ Ad) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (M : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (C : ℕ → ℝ)
        (h : MorseChainRealization M σ D C),
      ∀ (N : ℕ), M.index + 3 ≤ N → MorseOuterLocalizerLabels M D N →
      ∀ (right : Bool) (j : ℕ) (η K : ℝ)
        (F : MorsePhysicalTailBasis M D right j (N + 1)
          (morseOuterDeepEntrance M right N) η K),
        let T := morsePhysicalDeepTail M D right j (N + 1)
          (morseOuterDeepEntrance M right N) η K
        DeepTailHypotheses T → η ≤ 1 / 16 → 32 ≤ K → 2 ≤ j →
        TailPhysicalRelation D T right j (N + 1) →
        T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ →
        (∀ k, exp (2 * ((N + 1 + k : ℕ) : ℝ) ^ 2 -
          Ad * (((N + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + 1 + k : ℕ))) ≤
          T.Λ * tailMass T (k + 1) * tailResistance T k) →
        ∀ (m : ℕ) (x : ℝ),
          x ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
          D.localizer m (outerOutwardRadius right x) ≠ 0 →
          |F.P x| ≤ exp (A * (radialQ (D.cellIndex m) + radialQ N) -
            |radialS (D.cellIndex m) - radialS N|) := by
  let B := outerPhysicalNaturalExponent Ad
  have hB : 0 < B := outerPhysicalNaturalExponent_pos hAd
  have hBp : 0 ≤ B + 18 := by linarith
  obtain ⟨A, hA, hshift⟩ := outer_localized_envelope_shift hBp
  refine ⟨A, hA, ?_⟩
  intro M σ D C h N hN hlabels right j η K F
  dsimp only
  intro hT hη hK hj hphysical hclose hden m x hx hθ
  have hNi : M.index ≤ N := by omega
  have hentry : 0 < morseOuterDeepEntrance M right N :=
    h.geometry.1.trans (morseOuterDeepEntrance_mem_core h right N hNi).1
  have hxc := matchedOuter_tail_point_coordinates h.geometry right hentry hx
  obtain ⟨p, hp⟩ := exists_outerTailPoint hT hxc.2.1
  have hmp := hlabels.tail_point right j η K p m _ hp (by
    rw [tailPhysicalRadius_log right hxc.1]
    exact hθ)
  have hraw := F.physical_natural_point_envelope h.geometry hentry hT hη hK
    hj (by omega) hphysical hclose hAd hden hp
  rw [hxc.2.2] at hraw
  have hdec := outer_attenuation_from_core (by omega : 1 ≤ N)
    (by omega : N + 1 ≤ N + 1 + p)
  have hpoint : |F.P x| ≤
      radialE (N + 1 + p) ^ (B + 18) *
        exp (-|radialS (N + 1 + p) - radialS N|) := by
    refine hraw.trans ((mul_le_mul_of_nonneg_left hdec
      (rpow_nonneg (show 0 ≤ radialE (N + 1 + p) from (exp_pos _).le) B)).trans_eq ?_)
    rw [rpow_add (show 0 < radialE (N + 1 + p) from exp_pos _) B 18]
    ring
  have hpair : |F.P x| ≤
      radialE (N + 1 + p) ^ (B + 18) * radialE N ^ (B + 18) *
        exp (-|radialS (N + 1 + p) - radialS N|) := by
    refine hpoint.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact le_mul_of_one_le_right
      (rpow_nonneg (show 0 ≤ radialE (N + 1 + p) from (exp_pos _).le) _)
      (outer_envelope_one_le N hBp)
  refine hpair.trans ((hshift (N + 1 + p) N (D.cellIndex m) N
    (by omega) (by omega) (by omega) (by omega)
    hmp.1 hmp.2 (by omega) (by omega)).trans_eq ?_)
  rw [outer_radialE_rpow, outer_radialE_rpow, ← exp_add, ← exp_add]
  congr 1 <;> ring

end ContinuousFlexibility.Radial
