import ContinuousFlexibility.Radial.OuterOutgoingJoin

/-!
# The complete core ending at the actual natural-tail entrance

At the right end the outgoing connector is included, so the endpoint
is the next mass interval's left cut.  At the left end the already
constructed core leads into the initial resistance edge.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def morseOuterFullCoreRight (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  if side then T.joinRight side n else morseOuterCoreRight T side n

def outerFullCoreQuadraticExponent (C : ℕ → ℝ) (K a Cstar L : ℝ) : ℝ :=
  outerCoreInteriorQuadraticExponent C K a Cstar L +
    outerOutgoingQuadraticExponent C K a Cstar L

def outerFullCoreActionExponent (C : ℕ → ℝ) (K a : ℝ) : ℝ :=
  outerCoreActionExponent C K a + outerOutgoingActionExponent C K a

theorem morseOuterFullCore_interval {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    morseOuterCoreLeft T side n < morseOuterFullCoreRight T side n ∧
      Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n) ⊆ radialCore D := by
  have hc := morseOuterCore_interval h side n hn
  cases side with
  | false => simpa only [morseOuterFullCoreRight, Bool.false_eq_true, ite_false] using hc
  | true =>
      have hj := h.join_data true n hn.le
      have hs : T.joinLeft true n = morseOuterCoreRight T true n := by
        simpa only [morseOuterCoreRight, ite_true] using hj.2.1
      have he := morseRealized_retained_endpoints h true (n + 1) (by omega)
      have hr : T.joinRight true n ∈ radialCore D := by
        rw [hj.2.2.1]
        exact he.1
      have hl := hc.2 (left_mem_Icc.mpr hc.1.le)
      have hlt : morseOuterCoreLeft T true n < T.joinRight true n :=
        hc.1.trans (by rw [← hs]; exact hj.1)
      exact ⟨hlt, fun x hx => ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩⟩

theorem morseOuterCore_subset_full {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ⊆
      Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n) := by
  apply Icc_subset_Icc_right
  cases side with
  | false => exact le_rfl
  | true =>
      have hj := h.join_data true n hn.le
      change T.radius true n (T.rightX true n) ≤ T.joinRight true n
      simpa only [hj.2.1, ite_true] using hj.1.le

theorem morseOuterFullCore_outgoing_subset {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (n : ℕ) (hn : T.index < n) :
    Icc (T.joinLeft true n) (T.joinRight true n) ⊆
      Icc (morseOuterCoreLeft T true n) (morseOuterFullCoreRight T true n) := by
  apply Icc_subset_Icc_left
  have hc := morseOuterCore_interval h true n hn
  have hj := h.join_data true n hn.le
  simpa only [morseOuterCoreRight, ite_true, hj.2.1] using hc.1.le

/-- Actual homogeneous states are controlled between arbitrary physical
points of the entire core, including the outgoing right connector. -/
theorem morseOuterFullCore_energy_on_exp_of_upper
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n))
    (ht : t ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (outerFullCoreQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  let N := (n : ℝ) ^ 2
  let tau := (j : ℝ) * sqrt (morseChainA T n)
  let E (x : ℝ) := u x ^ 2 + z x ^ 2
  let Fc := exp (outerCoreInteriorQuadraticExponent C K D.a Cstar L * N +
    outerCoreActionExponent C K D.a * tau)
  let Fo := exp (outerOutgoingQuadraticExponent C K D.a Cstar L * N +
    outerOutgoingActionExponent C K D.a * tau)
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have ha : 0 < D.a := h.geometry.1
  have hFc : 1 ≤ Fc := one_le_exp_iff.mpr (by
    dsimp only [Fc, N, tau, outerCoreInteriorQuadraticExponent, outerCoreQuadraticExponent,
      outerCoreActionExponent, outerFrequencyExponent, outerJoinPrefactor]
    positivity)
  have hFo : 1 ≤ Fo := one_le_exp_iff.mpr (by
    dsimp only [Fo, N, tau, outerOutgoingQuadraticExponent, outerOutgoingActionExponent,
      outerFrequencyExponent, outerJoinPrefactor]
    positivity)
  have hprod : Fc * Fo =
      exp (outerFullCoreQuadraticExponent C K D.a Cstar L * N +
        outerFullCoreActionExponent C K D.a * tau) := by
    dsimp only [Fc, Fo]
    rw [← exp_add]
    congr 1
    dsimp only [outerFullCoreQuadraticExponent, outerFullCoreActionExponent]
    ring
  have hsub := morseOuterCore_subset_full h side n hn
  have hbase : ∀ s ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n),
      ∀ t ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n),
      E t ≤ E s * Fc :=
    fun s hs t ht => morseOuterCore_energy_on_exp_of_upper h hσ hcell hscale hL side hn hupper hhi hlo
      (fun r hr => hstate r (hsub hr)) hs ht
  cases side with
  | false =>
      calc
        _ ≤ E s * Fc := hbase s hs t ht
        _ ≤ (E s * Fc) * Fo :=
          le_mul_of_one_le_right (by dsimp only [E, Fc]; positivity) hFo
        _ = _ := by rw [mul_assoc, hprod]
  | true =>
      have hc := morseOuterCore_interval h true n hn
      have hj := h.join_data true n hn.le
      have hseam : T.joinLeft true n = morseOuterCoreRight T true n := by
        simpa only [morseOuterCoreRight, ite_true] using hj.2.1
      have hjoinSub := morseOuterFullCore_outgoing_subset h n hn
      have hfull := morseOuterFullCore_interval h true n hn
      have hjoinFactor := morse_outgoing_join_factor_le_frequency_exp_of_upper h hσ hcell hscale hL hn hupper hhi hlo
      have hje : ∀ s ∈ Icc (T.joinLeft true n) (T.joinRight true n),
          ∀ t ∈ Icc (T.joinLeft true n) (T.joinRight true n), E t ≤ E s * Fo := by
        intro s hs t ht
        exact (outer_positive_physical_energy_on h.geometry hscale hj.1
          (hjoinSub.trans hfull.2) hj.2.2.2.2 (fun r hr => hstate r (hjoinSub hr)) hs ht).trans
            (mul_le_mul_of_nonneg_left hjoinFactor (by positivity))
      rw [hseam] at hje
      have hbc : morseOuterCoreRight T true n ≤ T.joinRight true n := by
        rw [← hseam]
        exact hj.1.le
      have hh := energy_transfer_join hc.1.le hbc hFc hFo
        (fun x _ => show 0 ≤ E x by dsimp only [E]; positivity) hbase hje hs ht
      rw [hprod] at hh
      exact hh

theorem morseOuterFullCore_energy_on_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n))
    (ht : t ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (outerFullCoreQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) :=
  morseOuterFullCore_energy_on_exp_of_upper h hσ hcell hscale hL side hn hband.2.2 hhi hlo hstate hs ht

end ContinuousFlexibility.Radial
