import ContinuousFlexibility.Radial.R07IncomingJoin
import ContinuousFlexibility.Radial.R07OriginalOutgoing

/-!
# Concrete simultaneous matching in every later band

The incoming construction supplies the fixed cap slope, the exact height
coordinate, and the small continuous join state. The outgoing construction
supplies the invariant nonzero natural state. A single height sequence then
separates the actual two physical solutions at both endpoints in every
noninitial frequency band.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff ENNReal
open ContinuousFlexibility.Statements

theorem radialState_eq_heightOuterState {D : ReferenceData} {j : ℕ} {p e σ Ξ : ℝ}
    (hp : D.w p ≠ 0) (hweight : D.w e = σ * Ξ * D.w p) (v : ℝ → ℝ) :
    radialState D j e (D.w p) v = morseHeightOuterState Ξ σ (r07OutgoingState j e v) := by
  apply Prod.ext
  · rfl
  · simp only [radialState, morseHeightOuterState, r07OutgoingState]
    rw [hweight]
    field_simp [hp]
    <;> ring

private theorem r07_join_subset_cut_entry (right : Bool) {c p e : ℝ}
    (horder : if right then c < p ∧ p < e else e < p ∧ p < c) :
    uIcc p e ⊆ uIcc c e := by
  apply uIcc_subset_uIcc_right
  cases right
  · exact mem_uIcc.mpr (Or.inr ⟨horder.1.le, horder.2.le⟩)
  · exact mem_uIcc.mpr (Or.inl ⟨horder.1.le, horder.2.le⟩)

/-- Once an actual outgoing family has been constructed, all other
height-selection hypotheses follow from the original Morse geometry. -/
theorem exists_r07_selected_later_of_outgoing {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ) (K : ℕ → ℝ)
    (hfamily : ∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
      MorseChainRealization T σ (morseChainReferenceFamily G phi σ) K)
    {C : ℝ} (hC : 1000 ≤ C)
    (hsmall : R07JoinActionSmall T C (r07UniformTolerance C))
    (v : R07LaterCondition T C → (ℕ → ℝ) → ℝ → ℝ)
    (hnatural : ∀ q, ∀ σ ∈ heightCube,
      RadialNaturalTail (morseChainReferenceFamily G phi σ) q.1.1 q.1.2.1.2
        (r07CellEntry T q.1.1 q.1.2.1.1) (v q σ))
    (hB : ∀ q, ∀ σ ∈ heightCube,
      r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1) (v q σ) ≠ (0, 0))
    (hBcont : ∀ q, ContinuousOn
      (fun σ => r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1) (v q σ)) heightCube)
    (hBindep : ∀ q, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1)
          (v q (Function.update σ q.1.2.1.1 t)) =
        r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1) (v q σ)) :
    ∃ (σ : ℕ → ℝ) (u : R07LaterCondition T C → ℝ → ℝ),
      (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) ∧
      ∀ q : R07LaterCondition T C,
        let side := q.1.1
        let n := q.1.2.1.1
        let j := q.1.2.1.2
        let D := morseChainReferenceFamily G phi σ
        let c := r07PreviousCellCut T side (n - 1)
        let p := r07PreviousCellJoin T side (n - 1)
        let e := r07CellEntry T side n
        R07MatchingGeometry T D side n j c p e (u q) (v q σ) ∧
          r07UniformTolerance C * exp (-(n : ℝ) ^ 2) ≤
            radialAngleSine (radialState D j e (D.w p) (u q))
              (radialState D j e (D.w p) (v q σ)) := by
  classical
  let F := morseChainReferenceFamily G phi
  let c₀ := r07UniformTolerance C
  have hCp : 0 < C := by linarith only [hC]
  have hc₀ : 0 < c₀ := r07UniformTolerance_pos hCp.le
  have hc₀48 : c₀ ≤ 1 / 48 := r07UniformTolerance_le C
  have hc₀1 : c₀ ≤ 1 := hc₀48.trans (by norm_num)
  have hex (q : R07LaterCondition T C) :
      ∃ (a Ξ : ℝ) (u : (ℕ → ℝ) → ℝ → ℝ),
        a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) ∧ 0 < Ξ ∧
        (∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
          let n := q.1.2.1.1
          let j := q.1.2.1.2
          let c := r07PreviousCellCut T q.1.1 (n - 1)
          let p := r07PreviousCellJoin T q.1.1 (n - 1)
          let e := r07CellEntry T q.1.1 n
          ContDiff ℝ ∞ (u σ) ∧
          R07MatchingGeometry T (F σ) q.1.1 n j c p e (u σ) (v q σ) ∧
          radialState (F σ) j p ((F σ).w p) (u σ) = (1, a) ∧
          (F σ).w e = σ n * Ξ * (F σ).w p) ∧
        ContinuousOn (fun σ => radialState (F σ) q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1)
          ((F σ).w (r07PreviousCellJoin T q.1.1 (q.1.2.1.1 - 1))) (u σ)) heightCube := by
    let n := q.1.2.1.1
    let k := n - 1 - T.index
    have hm : T.index + k = n - 1 := by dsimp only [k]; have := q.property; omega
    have hn : n - 1 + 1 = n := by have := q.property; omega
    have hband : radialFrequencyBand T C (T.index + k + 1) q.1.2.1.2 := by
      simpa only [hm, hn] using q.1.2.2.2.2
    obtain ⟨a, Ξ, u, ha, hΞ, hu, hcont⟩ := exists_r07_original_incoming_family G phi K
      hfamily hC q.1.1 k q.1.2.2.1 hband
    refine ⟨a, Ξ, u, ha, hΞ, ?_, ?_⟩
    · intro σ hσ
      have hs := hu σ hσ
      have hv := hnatural q σ (mem_heightCube.mpr hσ)
      have hg := hs.2.1 (v q σ) (by simpa only [hm, hn] using hv)
      refine ⟨hs.1, ?_, ?_, ?_⟩
      · simpa only [hm, hn] using hg
      · simpa only [hm] using hs.2.2.1
      · simpa only [hm, hn] using hs.2.2.2
    · simpa only [hm, hn] using hcont
  choose a Ξ U ha hΞ hU hcont using hex
  let Y (q : R07LaterCondition T C) (σ : ℕ → ℝ) : ℝ × ℝ :=
    radialState (F σ) q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1)
      ((F σ).w (r07PreviousCellJoin T q.1.1 (q.1.2.1.1 - 1))) (U q σ)
  let B (q : R07LaterCondition T C) (σ : ℕ → ℝ) : ℝ × ℝ :=
    r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1) (v q σ)
  have hY : ∀ q, ∀ σ ∈ heightCube,
      |(Y q σ).1 - 1| ≤ (c₀ * exp (-(q.1.2.1.1 : ℝ) ^ 2)) / 4 ∧
      |(Y q σ).2 - a q| ≤ (c₀ * exp (-(q.1.2.1.1 : ℝ) ^ 2)) / 4 := by
    intro q σ hσ
    let n := q.1.2.1.1
    let k := n - 1 - T.index
    have hm : T.index + k = n - 1 := by dsimp only [k]; have := q.property; omega
    have hn : n - 1 + 1 = n := by have := q.property; omega
    have hband : radialFrequencyBand T C (T.index + k + 1) q.1.2.1.2 := by
      simpa only [hm, hn] using q.1.2.2.2.2
    have hσ' := mem_heightCube.mp hσ
    have hs := hU q σ hσ'
    have hg := hs.2.1
    have hjoint := r07_join_subset_cut_entry q.1.1 hg.order
    have hode : ∀ r ∈ uIcc (r07PreviousCellJoin T q.1.1 (T.index + k))
        (r07CellEntry T q.1.1 (T.index + k + 1)),
        radialJacobi ((q.1.2.1.2 : ℝ) ^ 2) (F σ).w (U q σ) r = 0 := by
      intro r hr
      apply hg.incoming_equation.2 r
      apply hjoint
      simpa only [hm, hn] using hr
    have hstate : radialState (F σ) q.1.2.1.2
        (r07PreviousCellJoin T q.1.1 (T.index + k))
        ((F σ).w (r07PreviousCellJoin T q.1.1 (T.index + k))) (U q σ) = (1, a q) := by
      simpa only [hm] using hs.2.2.1
    have hc := r07_actual_incoming_join_close G (hfamily σ hσ') hσ' hc₀.le hc₀1 hsmall
      q.1.1 k q.1.2.2.1 hband hs.1 hode hstate (ha q)
    simpa only [Y, hm, hn] using hc
  obtain ⟨σ, hσ, hangle⟩ := exists_r07_later_heights T C c₀
    (fun q _ => a q) (fun q _ => Ξ q) Y B hc₀ hc₀48
    (fun q _ _ => ha q) (fun q _ _ => hΞ q) hB hY
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hBindep
    hcont (fun _ => continuousOn_const) hBcont
    (r07UniformTolerance_two_endpoint_budget T hCp.le (fun n _ => G.d_exact n))
  refine ⟨σ, fun q => U q σ, hσ, ?_⟩
  intro q
  have hs := hU q σ hσ
  refine ⟨hs.2.1, ?_⟩
  rw [radialState_eq_heightOuterState hs.2.1.join_positive.ne' hs.2.2.2 (v q σ)]
  exact hangle q

/-- The actual R06 natural family closes all later-band hypotheses. The
only preliminary threshold is the numerical one chosen before the chain. -/
theorem exists_r07_selected_later {T : MorseChainData} (hR06 : R06Statement)
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ) (K : ℕ → ℝ)
    (hfamily : ∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
      MorseChainRealization T σ (morseChainReferenceFamily G phi σ) K ∧
        MorseMassResistanceBounds T σ (morseChainReferenceFamily G phi σ) K)
    {C : ℝ} (hC : 1000 ≤ C)
    (hsmall : R07JoinActionSmall T C (r07UniformTolerance C)) :
    ∃ (σ : ℕ → ℝ) (u v : R07LaterCondition T C → ℝ → ℝ),
      (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) ∧
      ∀ q : R07LaterCondition T C,
        let side := q.1.1
        let n := q.1.2.1.1
        let j := q.1.2.1.2
        let D := morseChainReferenceFamily G phi σ
        let c := r07PreviousCellCut T side (n - 1)
        let p := r07PreviousCellJoin T side (n - 1)
        let e := r07CellEntry T side n
        R07MatchingGeometry T D side n j c p e (u q) (v q) ∧
          r07UniformTolerance C * exp (-(n : ℝ) ^ 2) ≤
            radialAngleSine (radialState D j e (D.w p) (u q))
              (radialState D j e (D.w p) (v q)) := by
  classical
  have hex (q : R07LaterCondition T C) : ∃ V : (ℕ → ℝ) → ℝ → ℝ,
      (∀ σ ∈ heightCube, ContDiff ℝ ∞ (V σ) ∧
        RadialNaturalTail (morseChainReferenceFamily G phi σ) q.1.1 q.1.2.1.2
          (r07CellEntry T q.1.1 q.1.2.1.1) (V σ)) ∧
      ContinuousOn (fun σ => r07OutgoingState q.1.2.1.2
        (r07CellEntry T q.1.1 q.1.2.1.1) (V σ)) heightCube ∧
      (∀ σ ∈ heightCube, r07OutgoingState q.1.2.1.2
        (r07CellEntry T q.1.1 q.1.2.1.1) (V σ) ≠ (0, 0)) ∧
      ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
        r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1)
            (V (Function.update σ q.1.2.1.1 t)) =
          r07OutgoingState q.1.2.1.2 (r07CellEntry T q.1.1 q.1.2.1.1) (V σ) := by
    have hn : T.index + (q.1.2.1.1 - T.index) = q.1.2.1.1 := by
      have := q.property
      omega
    simpa only [hn] using exists_r07OriginalOutgoing_raw hR06 G phi K hfamily
      q.1.1 (q.1.2.1.1 - T.index) q.1.2.1.2 q.1.2.2.1
  choose V hV hVc hVne hVi using hex
  obtain ⟨σ, u, hσ, hmatch⟩ := exists_r07_selected_later_of_outgoing G phi K
    (fun σ hσ => (hfamily σ hσ).1) hC hsmall V
    (fun q σ hσ => (hV q σ hσ).2) hVne hVc hVi
  exact ⟨σ, u, fun q => V q σ, hσ, hmatch⟩

end ContinuousFlexibility.Radial
