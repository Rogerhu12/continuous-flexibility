import ContinuousFlexibility.Radial.R07ChainIncoming
import ContinuousFlexibility.Radial.R07RadialTransport
import ContinuousFlexibility.Radial.R07NaturalTailScale
import ContinuousFlexibility.Radial.R07TailParameter
import ContinuousFlexibility.Radial.MorseChainFullRealization

/-!
# Fixed cap normalization and the exact height coordinate at a join
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_realized_model_height_scale {T : MorseChainData} {D E : ReferenceData}
    {σ τ C K : ℕ → ℝ} (hD : MorseChainRealization T σ D C)
    (hE : MorseChainRealization T τ E K) (hτ : ∀ i, 1 ≤ τ i ∧ τ i ≤ 2)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (T.leftX right n) (T.rightX right n)) :
    D.w (T.radius right n x) =
      (morseChainAmplitude T σ n / morseChainAmplitude T τ n) * E.w (T.radius right n x) := by
  rw [hD.profile_eq right n hn x hx, hE.profile_eq right n hn x hx]
  field_simp [(morseChainAmplitude_pos T τ hτ n).ne']
  <;> ring

theorem r07_adjacent_amplitude_relative (T : MorseChainData) (σ : ℕ → ℝ) {m : ℕ}
    (hm : T.index ≤ m) :
    morseChainAmplitude T σ (m + 1) / morseChainAmplitude T morseUnitHeights (m + 1) =
      σ (m + 1) * (morseChainAmplitude T σ m / morseChainAmplitude T morseUnitHeights m) := by
  rw [morseChainAmplitude_succ T σ m (hm.trans (Nat.le_succ m)),
    morseChainAmplitude_succ T morseUnitHeights m (hm.trans (Nat.le_succ m))]
  simp only [morseUnitHeights, one_mul]
  field_simp [(morseChainAmplitude_pos T morseUnitHeights morseUnitHeights_admissible m).ne',
    exp_ne_zero]
  <;> ring

/-- The coefficient multiplying the selected height is entirely geometric.
It is the entry/join height ratio of the fixed unit-height profile. -/
theorem r07_realized_entry_join_ratio {T : MorseChainData} {D E : ReferenceData}
    {σ C K : ℕ → ℝ} (hD : MorseChainRealization T σ D C)
    (hE : MorseChainRealization T morseUnitHeights E K)
    (right : Bool) {m : ℕ} (hm : T.index ≤ m) :
    D.w (r07CellEntry T right (m + 1)) =
      σ (m + 1) * (E.w (r07CellEntry T right (m + 1)) /
        E.w (r07PreviousCellJoin T right m)) * D.w (r07PreviousCellJoin T right m) := by
  have hm1 := hm.trans (Nat.le_succ m)
  have hcutOrder := (hE.2.2.1 right m hm).2.1.le
  have hnextOrder := (hE.2.2.1 right (m + 1) hm1).2.1.le
  have hp : (if right then T.rightX right m else T.leftX right m) ∈
      Icc (T.leftX right m) (T.rightX right m) := by
    cases right
    · exact ⟨le_rfl, hcutOrder⟩
    · exact ⟨hcutOrder, le_rfl⟩
  have he : (if right then T.leftX right (m + 1) else T.rightX right (m + 1)) ∈
      Icc (T.leftX right (m + 1)) (T.rightX right (m + 1)) := by
    cases right
    · exact ⟨hnextOrder, le_rfl⟩
    · exact ⟨le_rfl, hnextOrder⟩
  have hP := r07_realized_model_height_scale hD hE morseUnitHeights_admissible right hm hp
  have hQ := r07_realized_model_height_scale hD hE morseUnitHeights_admissible right hm1 he
  have hP0 : E.w (r07PreviousCellJoin T right m) ≠ 0 :=
    (hE.geometry.2.2.2.2.1 _ (hE.radius_mem_core right m hm _ hp)).ne'
  change D.w (r07PreviousCellJoin T right m) =
    (morseChainAmplitude T σ m / morseChainAmplitude T morseUnitHeights m) *
      E.w (r07PreviousCellJoin T right m) at hP
  change D.w (r07CellEntry T right (m + 1)) =
    (morseChainAmplitude T σ (m + 1) / morseChainAmplitude T morseUnitHeights (m + 1)) *
      E.w (r07CellEntry T right (m + 1)) at hQ
  rw [hQ, r07_adjacent_amplitude_relative T σ hm, hP]
  field_simp [hP0]
  <;> ring

/-- On each retained model, the original realized family differs from its
unit-height member by one constant, on a full neighborhood of every point. -/
theorem r07_originalFamily_model_scale_germ {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ) (σ : ℕ → ℝ)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) (right : Bool) (k : ℕ) {r : ℝ}
    (hr : r ∈ Icc (morseChainCellLeftRadius T right k) (morseChainCellRightRadius T right k)) :
    (morseChainReferenceFamily G phi σ).w =ᶠ[𝓝 r]
      fun y => (morseChainAmplitude T σ (T.index + k) /
        morseChainAmplitude T morseUnitHeights (T.index + k)) *
          (morseChainReferenceFamily G phi morseUnitHeights).w y := by
  rw [morseChainReferenceFamily_admissible G phi σ hσ,
    morseChainReferenceFamily_admissible G phi morseUnitHeights morseUnitHeights_admissible]
  change morseChainGluedProfile G σ hσ =ᶠ[𝓝 r]
    fun y => (morseChainAmplitude T σ (T.index + k) /
      morseChainAmplitude T morseUnitHeights (T.index + k)) *
        morseChainGluedProfile G morseUnitHeights morseUnitHeights_admissible y
  have hs := morseChainGluedProfile_model_germ G σ hσ right k hr
  have h₀ := morseChainGluedProfile_model_germ G morseUnitHeights morseUnitHeights_admissible right k hr
  filter_upwards [hs, h₀] with y hy hy₀
  rw [hy, hy₀]
  simp only [morseChainPhysicalModelHeight]
  field_simp [(morseChainAmplitude_pos T morseUnitHeights morseUnitHeights_admissible (T.index + k)).ne']
  <;> ring

/-- Continuity of a fixed-initial-data radial family gives the precise
normalized matching state, including its varying endpoint weight ratio. -/
theorem continuous_radialState_transport {X : Type*} [TopologicalSpace X]
    {D : X → ReferenceData} {u : X → ℝ → ℝ} {a b : ℝ} (j : ℕ)
    (hw : ∀ p, ContDiff ℝ ∞ (D p).w) (hu : ∀ p, ContDiff ℝ ∞ (u p))
    (h₀ : ContinuousOn (fun z : X × ℝ => (D z.1).w z.2) {z | z.2 ∈ uIcc a b})
    (h₁ : ContinuousOn (fun z : X × ℝ => deriv (D z.1).w z.2) {z | z.2 ∈ uIcc a b})
    (hwn : ∀ p r, r ∈ uIcc a b → (D p).w r ≠ 0)
    (hrn : ∀ r ∈ uIcc a b, r ≠ 0)
    (hode : ∀ p r, r ∈ uIcc a b → radialJacobi ((j : ℝ) ^ 2) (D p).w (u p) r = 0)
    (hinit₀ : Continuous (fun p => u p a)) (hinit₁ : Continuous (fun p => deriv (u p) a)) :
    Continuous (fun p => radialState (D p) j b ((D p).w a) (u p)) := by
  have hU := continuous_radialCauchyData_transport j hw hu h₀ h₁ hwn hrn hode hinit₀ hinit₁
  have hWa : Continuous (fun p => (D p).w a) :=
    h₀.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => left_mem_uIcc)
  have hWb : Continuous (fun p => (D p).w b) :=
    h₀.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => right_mem_uIcc)
  exact hU.fst.prodMk ((hWb.div hWa (fun p => hwn p a left_mem_uIcc)).mul
    ((hU.snd.const_mul b).div_const ((j : ℝ) ^ 2) |>.sub hU.fst))

end ContinuousFlexibility.Radial
