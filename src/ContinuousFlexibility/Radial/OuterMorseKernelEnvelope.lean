module

public import ContinuousFlexibility.Radial.OuterActualGreenData
public import ContinuousFlexibility.Radial.OuterDeepUniformProduct
public import ContinuousFlexibility.Radial.OuterMorsePointLabels
public import ContinuousFlexibility.Radial.OuterPhysicalKernelEnvelope
public import ContinuousFlexibility.Radial.OuterPhysicalNaturalEnvelope
public import ContinuousFlexibility.Radial.OuterStateScaleEnvelope
public import ContinuousFlexibility.Radial.OuterWholeKernelEnvelope

/-!
# The actual whole outer kernel has the full cubic attenuation

The coefficient exponent is chosen before the profile, frequency, state
scale and endpoint. Both the Dirichlet term and the natural rank-one
term use the basis stored in the same actual Robin inverse certificate.
The action factor is retained explicitly, with no loss in the exponent
between the two physical position labels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem outerTailPoint_outward_mem
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K x : ℝ} {k : ℕ}
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hx : OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) k x) :
    outerOutwardLogRadius right x ∈
      Ico (outerOutwardRadius right entrance)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
  have hlog := outerTailPoint_mem hT hx
  have h := outerTailRadius_mem_outwardIco hD right hentry hlog
  simpa only [outerOutwardLogRadius, outerOutwardRadius_eq_sign] using h

/-- Every actual outer Green certificate satisfies the same pointwise
estimate. The only numerical hypotheses are the allowed state-scale
ratio and the frequency/cell conditions of the manuscript. -/
theorem exists_morseOuterGreen_kernel_envelope_uniform
    {C : ℕ → ℝ} (hC0 : 0 < C 0) {b : ℝ} (hb : 0 < b)
    {Ls Cbound Co : ℝ} (hLs : 0 ≤ Ls) (hCb : 0 ≤ Cbound) (hCo : 0 ≤ Co) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ (M : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData),
        MorseChainRealization M σ D C →
        (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseMassResistanceBounds M σ D C → D.b = b →
        ∀ (right : Bool) (n j : ℕ) (entry η K lam : ℝ),
          M.index ≤ n → 31 ≤ n → 2 ≤ j → entry ∈ morseInitialMiddle M →
          η ≤ 1 / 16 → 32 ≤ K → 0 < lam →
          morseChainAmplitude M σ n / lam ≤ exp (Ls * (n : ℝ) ^ 2) →
          ∀ G : MorseOuterGreenData M D right n j entry η K lam Cbound Co,
            ∀ p q : ℕ, ∀ x y : ℝ,
              MorseOuterPoint M D entry right j n η K p x →
              MorseOuterPoint M D entry right j n η K q y →
              |outerGreenKernel lam G.pair.U G.pair.V x y| ≤
                radialE p ^ Q * radialE q ^ Q *
                  exp (Co * ((j : ℝ) * sqrt (morseChainA M n))) ^ 2 *
                    exp (-|radialS p - radialS q|) := by
  let A := outerDeepProductExponent C
  have hA : 0 ≤ A := (outerDeepProductExponent_pos C).le
  obtain ⟨Ld, hLd, hdeepKernel⟩ := exists_outer_physical_kernel_decay_uniform hC0 hb hA
  let Lt := max Ld (outerPhysicalNaturalExponent A + 18)
  let T := 2 + (Ls + 1) + 2 * Lt
  have hLt : 0 ≤ Lt := hLd.le.trans (le_max_left _ _)
  have hTpos : 0 < T := by dsimp only [T]; linarith only [hLs, hLt]
  refine ⟨T + Cbound, by linarith only [hTpos, hCb], ?_⟩
  intro M σ D h hσ hmass hDb right n j entry η K lam hn h31 hj he hη hK hlam hscale G
  have hn1 : 1 ≤ n := by omega
  have hs1 : 1 ≤ n + 1 := by omega
  have hdeep := morseOuterDeepEntrance_mem_core h right n hn
  have hdpos : 0 < morseOuterDeepEntrance M right n := h.geometry.1.trans hdeep.1
  have hden := outer_actual_deepTail_product_lower h hσ hmass right hj hn h31 η K G.close
  have hkernel := hdeepKernel M D h.accumulating hDb right j (n + 1)
    (morseOuterDeepEntrance M right n) η K G.basis G.deep_hypotheses hη hK hj hs1
    G.physical_relation G.close hden
  have hi := morseTransitionOutward_interval h he right n hn
  rw [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] at hi
  have hPc : G.basis.P (outerOutwardRadius right (morseOuterDeepEntrance M right n)) = 1 := by
    simpa only [outerOutwardRadius_eq_sign] using G.basis.P_entrance
  have hQc : G.basis.Q (outerOutwardRadius right (morseOuterDeepEntrance M right n)) = 0 := by
    simpa only [outerOutwardRadius_eq_sign] using G.basis.Q_entrance
  have hflux : G.basis.ZQ lam (outerOutwardRadius right (morseOuterDeepEntrance M right n)) =
      1 / lam := by
    simpa only [outerOutwardRadius_eq_sign] using G.basis.ZQ_entrance lam
  have hshape {p : ℕ} {r : ℝ}
      (hp : MorseOuterPoint M D entry right j n η K p r) :
      (p = n ∧ r ∈ Icc
        (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
        (outerOutwardRadius right (morseOuterDeepEntrance M right n))) ∨
      (r ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right n))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) ∧
        |G.basis.P r| ≤ radialE p ^ Lt * exp (-|radialS p - radialS n|)) := by
    rcases hp with ⟨hp, hr⟩ | ⟨k, x, rfl, hx, rfl⟩
    · exact Or.inl ⟨hp, by
        simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using hr⟩
    · refine Or.inr ⟨outerTailPoint_outward_mem h.geometry hdpos G.deep_hypotheses hx, ?_⟩
      have hnat := G.basis.physical_natural_point_envelope h.geometry hdpos
        G.deep_hypotheses hη hK hj hs1 G.physical_relation G.close hA hden hx
      have hatt := outer_attenuation_from_core hn1 (Nat.le_add_right (n + 1) k)
      have he0 : 0 ≤ radialE (n + 1 + k) ^ outerPhysicalNaturalExponent A :=
        rpow_nonneg (show 0 ≤ radialE (n + 1 + k) from (exp_pos _).le) _
      calc
        _ ≤ radialE (n + 1 + k) ^ outerPhysicalNaturalExponent A *
            exp (-|radialS (n + 1 + k) - radialS (n + 1)|) := hnat
        _ ≤ radialE (n + 1 + k) ^ outerPhysicalNaturalExponent A *
            (radialE (n + 1 + k) ^ (18 : ℝ) *
              exp (-|radialS (n + 1 + k) - radialS n|)) :=
          mul_le_mul_of_nonneg_left hatt he0
        _ = radialE (n + 1 + k) ^ (outerPhysicalNaturalExponent A + 18) *
            exp (-|radialS (n + 1 + k) - radialS n|) := by
          rw [rpow_add (show 0 < radialE (n + 1 + k) from exp_pos _)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (outer_envelope_exponent_mono _ (le_max_right _ _)) (exp_pos _).le
  intro p q x y hxp hyp
  have hp := morseOuterPoint_label_ge hxp
  have hq := morseOuterPoint_label_ge hyp
  have hdirichlet (hx : x ∈ Ico
      (outerOutwardRadius right (morseOuterDeepEntrance M right n))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
      (hy : y ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right n))
        (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
      |G.basis.Q (min x y) * G.basis.P (max x y)| ≤
        radialE p ^ Lt * radialE q ^ Lt * exp (-|radialS p - radialS q|) := by
    have hnonneg : 0 ≤ radialE p ^ Lt * radialE q ^ Lt * exp (-|radialS p - radialS q|) :=
      mul_nonneg (mul_nonneg
        (rpow_nonneg (show 0 ≤ radialE p from (exp_pos _).le) _)
        (rpow_nonneg (show 0 ≤ radialE q from (exp_pos _).le) _)) (exp_pos _).le
    rcases hxp with ⟨_, hc⟩ | ⟨k, u, rfl, hu, rfl⟩
    · have hxle : x ≤ outerOutwardRadius right (morseOuterDeepEntrance M right n) := by
        simpa only [morseTransitionOutwardRight_eq] using hc.2
      have hxeq := le_antisymm hxle hx.1
      simpa only [hxeq, min_eq_left hy.1, hQc, zero_mul, abs_zero] using hnonneg
    · rcases hyp with ⟨_, hc⟩ | ⟨l, v, rfl, hv, rfl⟩
      · have hyle : y ≤ outerOutwardRadius right (morseOuterDeepEntrance M right n) := by
          simpa only [morseTransitionOutwardRight_eq] using hc.2
        have hyeq := le_antisymm hyle hy.1
        simpa only [hyeq, min_eq_right hx.1, hQc, zero_mul, abs_zero] using hnonneg
      · exact (hkernel k l u v hu hv).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul
            (outer_envelope_exponent_mono _ (le_max_left Ld _))
            (outer_envelope_exponent_mono _ (le_max_left Ld _))
            (rpow_nonneg (show 0 ≤ radialE (n + 1 + l) from (exp_pos _).le) _)
            (rpow_nonneg (show 0 ≤ radialE (n + 1 + k) from (exp_pos _).le) _))
          (exp_pos _).le)
  let Kn := exp (Co * ((j : ℝ) * sqrt (morseChainA M n)))
  let Bn := radialE n ^ Cbound
  have hKn : 1 ≤ Kn := one_le_exp_iff.mpr
    (mul_nonneg hCo (mul_nonneg (Nat.cast_nonneg _) (sqrt_nonneg _)))
  have hBn : 1 ≤ Bn := outer_envelope_one_le n hCb
  have hactual := G.pair.kernel_point_envelope hlam
    (one_le_mul_of_one_le_of_one_le hBn hKn)
    (by linarith only [hLs] : 0 ≤ Ls + 1) hLt hn1 hp hq hi.1.le hi.2
    hPc hQc hflux (fun r hr => (G.core_bound r hr).1)
    (fun r hr => (G.core_bound r hr).2.2.1)
    (outer_stateScale_inv_le M σ hσ hn1 hlam hLs hscale)
    (hshape hxp) (hshape hyp) hdirichlet
  have hBn2 : Bn ^ 2 ≤ radialE p ^ Cbound * radialE q ^ Cbound := by
    rw [pow_two]
    exact mul_le_mul (outer_envelope_index_mono hp hCb)
      (outer_envelope_index_mono hq hCb) (zero_le_one.trans hBn)
      (rpow_nonneg (show 0 ≤ radialE p from (exp_pos _).le) _)
  have hW : 0 ≤ radialE p ^ T * radialE q ^ T := mul_nonneg
    (rpow_nonneg (show 0 ≤ radialE p from (exp_pos _).le) _)
    (rpow_nonneg (show 0 ≤ radialE q from (exp_pos _).le) _)
  calc
    _ ≤ radialE p ^ T * radialE q ^ T * (Bn * Kn) ^ 2 *
        exp (-|radialS p - radialS q|) := hactual
    _ = (radialE p ^ T * radialE q ^ T * Bn ^ 2) * Kn ^ 2 *
        exp (-|radialS p - radialS q|) := by ring
    _ ≤ (radialE p ^ T * radialE q ^ T *
        (radialE p ^ Cbound * radialE q ^ Cbound)) * Kn ^ 2 *
        exp (-|radialS p - radialS q|) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBn2 hW) (sq_nonneg _))
      (exp_pos _).le
    _ = _ := by
      rw [rpow_add (show 0 < radialE p from exp_pos _) T Cbound,
        rpow_add (show 0 < radialE q from exp_pos _) T Cbound]
      ring

end ContinuousFlexibility.Radial
