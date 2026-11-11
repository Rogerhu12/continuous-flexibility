import ContinuousFlexibility.Radial.MorseChainFullRealization
import ContinuousFlexibility.Radial.MorseChainMassResistance

/-!
# Replacing the finite middle while retaining the actual Morse tails

The first frequency band is finite. Its cone heads can therefore be chosen
after the infinite tail height selection. A fixed smooth positive middle,
with the same endpoint germs, is multiplied by the head amplitude for every
height sequence. This preserves all uniform realization estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

/-- The concrete conditions on a replacement unit middle. -/
def R07MiddleAdmissible {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (M : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ M ∧ (∀ r, 0 < M r) ∧
    (M =ᶠ[𝓝 (morseChainCellRightRadius T false 0)]
      morseChainPhysicalModelHeight G 1 false 0) ∧
    (M =ᶠ[𝓝 (morseChainCellLeftRadius T true 0)]
      morseChainPhysicalModelHeight G 1 true 0) ∧
    ∀ r ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0),
      0 < deriv M r

theorem r07MiddleUnit_admissible {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) : R07MiddleAdmissible G (morseChainMiddleUnit G) :=
  Classical.choose_spec (exists_morseChainMiddleUnit G)

/-- Replace a finite middle, retaining the old profile on both exterior sides. -/
def r07ReplaceMiddle (a b : ℝ) (w M : ℝ → ℝ) : ℝ → ℝ :=
  morseGlueCut a w (morseGlueCut b M w)

theorem r07ReplaceMiddle_germs {a b : ℝ} {w M : ℝ → ℝ}
    (hab : a ≤ b) (ha : w =ᶠ[𝓝 a] M) (hb : w =ᶠ[𝓝 b] M) :
    (∀ x, x ≤ a ∨ b ≤ x → r07ReplaceMiddle a b w M =ᶠ[𝓝 x] w) ∧
      ∀ x ∈ Icc a b, r07ReplaceMiddle a b w M =ᶠ[𝓝 x] M := by
  have hmeet : w =ᶠ[𝓝 a] morseGlueCut b M w :=
    ha.trans (morseGlueCut_eventually_left hb.symm hab).symm
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact morseGlueCut_eventually_left hmeet hx
    · exact (morseGlueCut_eventually_right hmeet (hab.trans hx)).trans
        (morseGlueCut_eventually_right hb.symm hx)
  · intro x hx
    exact (morseGlueCut_eventually_right hmeet hx.1).trans
      (morseGlueCut_eventually_left hb.symm hx.2)

theorem contDiff_r07ReplaceMiddle {a b : ℝ} {w M : ℝ → ℝ}
    (hab : a ≤ b) (hw : ContDiff ℝ ∞ w) (hM : ContDiff ℝ ∞ M)
    (ha : w =ᶠ[𝓝 a] M) (hb : w =ᶠ[𝓝 b] M) :
    ContDiff ℝ ∞ (r07ReplaceMiddle a b w M) :=
  contDiff_morseGlueCut hw (contDiff_morseGlueCut hM hw hb.symm)
    (ha.trans (morseGlueCut_eventually_left hb.symm hab).symm)

def r07MiddlePatchedProfile {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (M : ℝ → ℝ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) : ℝ → ℝ :=
  r07ReplaceMiddle (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0)
    (morseChainGluedProfile G σ hσ) (fun r => Statements.morseChainAmplitude T σ T.index * M r)

theorem r07MiddlePatchedProfile_match {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    (morseChainGluedProfile G σ hσ =ᶠ[𝓝 (morseChainCellRightRadius T false 0)]
      fun r => Statements.morseChainAmplitude T σ T.index * M r) ∧
    (morseChainGluedProfile G σ hσ =ᶠ[𝓝 (morseChainCellLeftRadius T true 0)]
      fun r => Statements.morseChainAmplitude T σ T.index * M r) := by
  have hu := r07MiddleUnit_admissible G
  have hab : morseChainCellRightRadius T false 0 < morseChainCellLeftRadius T true 0 := by
    simpa only [morseChainCellRightRadius, morseChainCellLeftRadius, Nat.add_zero] using G.middle_gap
  exact ⟨(morseChainGluedProfile_middle_germ G σ hσ (left_mem_Icc.mpr hab.le)).trans
      ((hu.2.2.1.trans hM.2.2.1.symm).fun_comp
        (fun z => Statements.morseChainAmplitude T σ T.index * z)),
    (morseChainGluedProfile_middle_germ G σ hσ (right_mem_Icc.mpr hab.le)).trans
      ((hu.2.2.2.1.trans hM.2.2.2.1.symm).fun_comp
        (fun z => Statements.morseChainAmplitude T σ T.index * z))⟩

theorem r07MiddlePatchedProfile_germs {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    (∀ x, x ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ x →
      r07MiddlePatchedProfile G M σ hσ =ᶠ[𝓝 x] morseChainGluedProfile G σ hσ) ∧
    (∀ x ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0),
      r07MiddlePatchedProfile G M σ hσ =ᶠ[𝓝 x]
        fun r => Statements.morseChainAmplitude T σ T.index * M r) := by
  have hab : morseChainCellRightRadius T false 0 ≤ morseChainCellLeftRadius T true 0 := by
    simpa only [morseChainCellRightRadius, morseChainCellLeftRadius, Nat.add_zero] using G.middle_gap.le
  obtain ⟨hL, hR⟩ := r07MiddlePatchedProfile_match G hM σ hσ
  exact r07ReplaceMiddle_germs hab hL hR

theorem contDiff_r07MiddlePatchedProfile {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ContDiff ℝ ∞ (r07MiddlePatchedProfile G M σ hσ) := by
  have hab : morseChainCellRightRadius T false 0 ≤ morseChainCellLeftRadius T true 0 := by
    simpa only [morseChainCellRightRadius, morseChainCellLeftRadius, Nat.add_zero] using G.middle_gap.le
  obtain ⟨hL, hR⟩ := r07MiddlePatchedProfile_match G hM σ hσ
  exact contDiff_r07ReplaceMiddle hab (morseChainGluedProfile_flat G σ hσ).1
    (contDiff_const.mul hM.1) hL hR

/-- All middle modifications have exactly the same genuine tail germs. -/
theorem r07MiddlePatchedProfile_tail_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Statements.morseChainBlock T side (T.index + k)) :
    r07MiddlePatchedProfile G M σ hσ =ᶠ[𝓝 x] morseChainGluedProfile G σ hσ := by
  apply (r07MiddlePatchedProfile_germs G hM σ hσ).1
  let D := morseChainSelectedProfileData G σ hσ
  have hidx : T.index + k + 1 = T.index + (k + 1) := Nat.add_assoc _ _ _
  unfold Statements.morseChainBlock at hx
  rw [hidx] at hx
  cases side
  · change x ∈ uIcc (morseChainCellRightRadius T false k)
      (morseChainCellRightRadius T false (k + 1)) at hx
    have hn : -morseChainCellRightRadius T false k ≤ -morseChainCellRightRadius T false (k + 1) :=
      D.left.enter_strictMono.monotone (Nat.le_succ k)
    rw [uIcc_of_ge (le_of_neg_le_neg hn)] at hx
    have h0 : -morseChainCellRightRadius T false 0 ≤ -morseChainCellRightRadius T false k :=
      D.left.enter_strictMono.monotone (Nat.zero_le k)
    exact Or.inl (hx.2.trans (le_of_neg_le_neg h0))
  · change x ∈ uIcc (morseChainCellLeftRadius T true k)
      (morseChainCellLeftRadius T true (k + 1)) at hx
    have hn : morseChainCellLeftRadius T true k ≤ morseChainCellLeftRadius T true (k + 1) :=
      D.right.enter_strictMono.monotone (Nat.le_succ k)
    rw [uIcc_of_le hn] at hx
    exact Or.inr ((D.right.enter_strictMono.monotone (Nat.zero_le k)).trans hx.1)

/-- The same fixed partition controls every replacement middle, uniformly
in the original product height cube. -/
theorem exists_r07MiddlePatchedProfile_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
      (phi chi chiLeft : ℝ → ℝ) (m : ℕ) (x : ℝ),
      let D := morsePartitionReference G (r07MiddlePatchedProfile G M σ hσ) phi chi chiLeft
      x ∈ D.cells m → MorseChainJetBounds (D.cellIndex m) s C D.w x := by
  apply exists_morsePartitionReference_jetBounds_of_pieces G s (r07MiddlePatchedProfile G M)
  · obtain ⟨C, hC, hB⟩ := exists_morseChainGluedProfile_tail_jetBounds G s
    refine ⟨C, hC, fun σ hσ side k x hx => ?_⟩
    exact morseSelected_jetBounds_of_germ (hB σ hσ side k x hx)
      (r07MiddlePatchedProfile_tail_germ G hM σ hσ side k hx)
  · obtain ⟨C, hC, hB⟩ := exists_morseChainScaledMiddle_jetBounds G s M ⟨hM.1, hM.2.1⟩
    refine ⟨C, hC, fun σ hσ x hx => ?_⟩
    exact morseSelected_jetBounds_of_germ (hB σ hσ x hx)
      ((r07MiddlePatchedProfile_germs G hM σ hσ).2 x hx)

theorem r07MiddlePatchedProfile_geometry {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (phi chi chiLeft : ℝ → ℝ)
    (hPhi : ContDiff ℝ ∞ phi ∧ (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
      ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0) :
    Statements.RadialProfileGeometry
      (morsePartitionReference G (r07MiddlePatchedProfile G M σ hσ) phi chi chiLeft) := by
  let a := morseChainCellRightRadius T false 0
  let b := morseChainCellLeftRadius T true 0
  let w := r07MiddlePatchedProfile G M σ hσ
  let w₀ := morseChainGluedProfile G σ hσ
  let A := Statements.morseChainAmplitude T σ T.index
  have hA : 0 < A := morseChainAmplitude_pos T σ hσ T.index
  have hc : 1 < a ∧ b < G.rightEnd := by
    have h := (morseChainSelectedProfileData G σ hσ).cuts_inside
    change 1 < -(-morseChainCellRightRadius T false 0) ∧
      morseChainCellLeftRadius T true 0 < G.rightEnd at h
    simpa only [neg_neg] using h
  have hOld := morseChainGluedProfile_interior_exterior G σ hσ
  obtain ⟨hout, hin⟩ := r07MiddlePatchedProfile_germs G hM σ hσ
  have hpositive (x : ℝ) (hx : x ∈ Ioo 1 G.rightEnd) : 0 < w x := by
    by_cases he : x ≤ a ∨ b ≤ x
    · rw [(hout x he).eq_of_nhds]
      exact hOld.2.1 x hx
    · have hm : x ∈ Icc a b := by push_neg at he; exact ⟨he.1.le, he.2.le⟩
      rw [(hin x hm).eq_of_nhds]
      exact mul_pos hA (hM.2.1 x)
  refine ⟨zero_lt_one, G.rightEnd_gt_one,
    ⟨contDiff_r07MiddlePatchedProfile G hM σ hσ, ?_⟩,
    ⟨hPhi.1, hPhi.2.1⟩, hpositive, hPhi.2.2, ?_⟩
  · intro x hx
    have he : x ≤ a ∨ b ≤ x := hx.imp (fun h => h.trans hc.1.le) (fun h => hc.2.le.trans h)
    rw [(hout x he).eq_of_nhds]
    exact hOld.2.2 x hx
  · intro x hx hz
    by_cases he : x ≤ a ∨ b ≤ x
    · have hg := hout x he
      rw [hg.deriv.deriv_eq]
      exact morseChainGluedProfile_nonDegenerate G σ hσ hx (hg.deriv_eq ▸ hz)
    · have hm : x ∈ Icc a b := by push_neg at he; exact ⟨he.1.le, he.2.le⟩
      have hd : deriv w x = A * deriv M x := (hin x hm).deriv_eq.trans
        (((hM.1.differentiable (by simp) x).hasDerivAt).const_mul A).deriv
      have hp : 0 < deriv w x := by rw [hd]; exact mul_pos hA (hM.2.2.2.2 x hm)
      exact (hp.ne' hz).elim

end ContinuousFlexibility.Radial
