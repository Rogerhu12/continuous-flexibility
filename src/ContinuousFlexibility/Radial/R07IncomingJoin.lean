import ContinuousFlexibility.Radial.R07IncomingFamily
import ContinuousFlexibility.Radial.R07ConcreteJoinContrast

/-!
# The actual incoming state after its preceding join

The numerical threshold is chosen before the geometry. The normalized
physical join width cancels its radius, and its actual height contrast
then gives the coordinate error required by simultaneous height selection.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

def R07JoinActionSmall (T : MorseChainData) (C c : ℝ) : Prop :=
  ∀ n j, T.index < n → radialFrequencyBand T C n j →
    ∀ contrast fraction : ℝ, 0 ≤ contrast → contrast ≤ exp (6 * (n : ℝ) ^ 2) →
    0 ≤ fraction → fraction ≤ (1 / 100 : ℝ) * morseChainA T (n - 1) ^ 12 →
      2 * (j : ℝ) ^ 2 * contrast * fraction < c * exp (-(n : ℝ) ^ 2) / 12

theorem exists_r07_joinActionSmall_start {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∃ N : ℕ, 100 ≤ N ∧ ∀ T : MorseChainData,
      (∀ n, T.index ≤ n → T.d n = morseChainInteger n) →
      N ≤ T.index → R07JoinActionSmall T C c :=
  exists_r07_uniform_join_start hC hc

theorem r07_preceding_join_length {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (right : Bool) (k : ℕ) :
    |r07CellEntry T right (T.index + k + 1) - r07PreviousCellJoin T right (T.index + k)| =
      |T.joinRight right (T.index + k) - T.joinLeft right (T.index + k)| := by
  have hJ := G.joins k
  cases right
  · simp only [r07CellEntry, r07PreviousCellJoin, Bool.false_eq_true, if_false, Nat.add_assoc]
    rw [← hJ.2.2.1, ← hJ.2.2.2]
    exact abs_sub_comm _ _
  · simp only [r07CellEntry, r07PreviousCellJoin, if_true, Nat.add_assoc]
    rw [← hJ.2.1, ← hJ.1]

/-- The fixed cap normalization remains within one quarter of the
prescribed Gaussian tolerance after the actual physical connector. -/
theorem r07_actual_incoming_join_close {T : MorseChainData} {D : ReferenceData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D K) (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2)
    {C c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hc₀1 : c₀ ≤ 1) (hsmall : R07JoinActionSmall T C c₀)
    (right : Bool) (k : ℕ) {j : ℕ} (hj : 2 ≤ j)
    (hband : radialFrequencyBand T C (T.index + k + 1) j)
    {u : ℝ → ℝ} {a : ℝ} (hu : ContDiff ℝ ∞ u)
    (hode : ∀ r ∈ uIcc (r07PreviousCellJoin T right (T.index + k))
      (r07CellEntry T right (T.index + k + 1)), radialJacobi ((j : ℝ) ^ 2) D.w u r = 0)
    (hstate : radialState D j (r07PreviousCellJoin T right (T.index + k))
      (D.w (r07PreviousCellJoin T right (T.index + k))) u = (1, a))
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) :
    let m := T.index + k
    let Y := radialState D j (r07CellEntry T right (m + 1))
      (D.w (r07PreviousCellJoin T right m)) u
    |Y.1 - 1| ≤ (c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2)) / 4 ∧
      |Y.2 - a| ≤ (c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2)) / 4 := by
  let m := T.index + k
  let p := r07PreviousCellJoin T right m
  let e := r07CellEntry T right (m + 1)
  let contrast := max (D.w e / D.w p) (D.w p / D.w e)
  have hcontrast := r07_actual_join_contrast G hreal hσ right k
  have hI : uIcc p e = Icc (T.joinLeft right m) (T.joinRight right m) :=
    r07_preceding_join_interval G right k
  have hp : p ∈ Icc (T.joinLeft right m) (T.joinRight right m) := by
    rw [← hI]
    exact left_mem_uIcc
  have he : e ∈ Icc (T.joinLeft right m) (T.joinRight right m) := by
    rw [← hI]
    exact right_mem_uIcc
  have hm : T.index ≤ m := Nat.le_add_right _ _
  have hm1 : T.index ≤ m + 1 := hm.trans (Nat.le_succ m)
  have hpcut : (if right then T.rightX right m else T.leftX right m) ∈
      Icc (T.leftX right m) (T.rightX right m) := by
    have ho := (hreal.2.2.1 right m hm).2.1.le
    cases right
    · exact ⟨le_rfl, ho⟩
    · exact ⟨ho, le_rfl⟩
  have hecut : (if right then T.leftX right (m + 1) else T.rightX right (m + 1)) ∈
      Icc (T.leftX right (m + 1)) (T.rightX right (m + 1)) := by
    have ho := (hreal.2.2.1 right (m + 1) hm1).2.1.le
    cases right
    · exact ⟨ho, le_rfl⟩
    · exact ⟨le_rfl, ho⟩
  have hpCore : p ∈ radialCore D := hreal.radius_mem_core right m hm _ hpcut
  have heCore : e ∈ radialCore D := hreal.radius_mem_core right (m + 1) hm1 _ hecut
  have hleft : T.joinLeft right m ∈ uIcc p e := by
    rw [hI]
    exact left_mem_Icc.mpr (morseChainPhysicalJoin_order G right k).le
  have hr₀ : 0 < T.joinLeft right m :=
    hreal.geometry.1.trans ((ordConnected_Ioo.uIcc_subset hpCore heCore) hleft).1
  have hJ : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith only [hj', sq_nonneg ((j : ℝ) - 2)]
  have hcontrast₀ : 0 ≤ contrast := zero_le_one.trans hcontrast.1
  have hgeo := r07_geometry_join_action_le G right k (sq_nonneg (j : ℝ)) hcontrast₀ hr₀
  have hnum := hsmall (m + 1) j (by dsimp only [m]; omega) hband contrast
    ((1 / 100 : ℝ) * morseChainA T m ^ 12) hcontrast₀ hcontrast.2.1 (by positivity)
    (by simpa only [Nat.add_sub_cancel] using
      (le_refl ((1 / 100 : ℝ) * morseChainA T m ^ 12)))
  have haction : 2 * (j : ℝ) ^ 2 * contrast / T.joinLeft right m * |e - p| ≤
      (c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2)) / 12 := by
    rw [r07_preceding_join_length G right k]
    exact (hgeo.trans_lt hnum).le
  have hmargin : c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2) ≤ 1 :=
    (mul_le_of_le_one_right hc₀ (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))).trans hc₀1
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  have hu' : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  apply r07_joinState_close hr₀ hJ (hcontrast.2.2 p left_mem_uIcc).1 hcontrast.1
    (fun r _ => ⟨hw.differentiable (by simp) r, hu.differentiable (by simp) r,
      hu'.differentiable (by simp) r⟩)
    (fun r hr => hcontrast.2.2 r (by rwa [hI]))
    (fun r hr => hode r (by rwa [hI])) hp he hstate ha hmargin haction

end ContinuousFlexibility.Radial
