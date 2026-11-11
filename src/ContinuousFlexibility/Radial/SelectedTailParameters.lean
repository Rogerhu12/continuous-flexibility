import ContinuousFlexibility.Radial.R07IncomingSelection
import ContinuousFlexibility.Radial.R07FirstBandMatching
import ContinuousFlexibility.Radial.SelectedFixedBandAssembly
import ContinuousFlexibility.Radial.SelectedActualEntry

/-!
# Choosing the actual selected tail after quantitative parameters

Cstar is a caller-supplied number at least 1000. Its later-band tolerance
is fixed first. The uniform join threshold is then combined with any
requested starting index before the actual geometry is constructed.
The first-band correction changes neither the retained cells nor the
later-band angle bound.

The conclusion keeps one selected object, its canonical entrances, the
first band containing mode two, and the actual geometry used to build it.
To meet an arbitrary lower bound Cmin, call this theorem with max 1000 Cmin.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- The actual middle keeps its strictly increasing germ at both
initial entrances, including the seams themselves. -/
theorem r10a_middle_initial_derivative_pos {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M phi : ℝ → ℝ}
    (hM : R07MiddleAdmissible G M) (sigma : ℕ → ℝ)
    (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2) (right : Bool) :
    0 < deriv (r07MiddleReferenceFamily G M phi sigma).w
      (r07CellEntry T right T.index) := by
  have hab : morseChainCellRightRadius T false 0 ≤ morseChainCellLeftRadius T true 0 := by
    simpa only [morseChainCellRightRadius, morseChainCellLeftRadius, Nat.add_zero]
      using G.middle_gap.le
  have heq : r07CellEntry T right T.index =
      if right then morseChainCellLeftRadius T true 0
        else morseChainCellRightRadius T false 0 := by
    cases right <;> simp only [r07CellEntry, morseChainCellRightRadius,
      morseChainCellLeftRadius, Nat.add_zero, Bool.false_eq_true, if_false, if_true]
  have hmem : r07CellEntry T right T.index ∈
      Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0) := by
    rw [heq]
    cases right
    · exact left_mem_Icc.mpr hab
    · exact right_mem_Icc.mpr hab
  have hg := (r07MiddlePatchedProfile_germs G hM sigma hsigma).2 _ hmem
  rw [r07MiddleReferenceFamily_admissible G M phi sigma hsigma]
  change 0 < deriv (r07MiddlePatchedProfile G M sigma hsigma) (r07CellEntry T right T.index)
  rw [hg.deriv_eq, deriv_const_mul_field]
  exact mul_pos (morseChainAmplitude_pos T sigma hsigma T.index) (hM.2.2.2.2 _ hmem)

theorem exists_r10a_parameterized_selectedTail (hR06 : R06Statement)
    (C : ℝ) (hC1000 : 1000 ≤ C) (requestedIndex : ℕ) :
    ∃ S : SelectedTailData, IsSelectedTail S ∧ S.Cstar = C ∧
      requestedIndex ≤ S.chain.index ∧ 100 ≤ S.chain.index ∧
      S.entry = r07CellEntry S.chain ∧
      S.entry false S.chain.index < S.entry true S.chain.index ∧
      radialFrequencyBand S.chain S.Cstar S.chain.index 2 ∧
      (∀ right, S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
        0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
        RadialNaturalTail (S.family S.sigma) right 2 (S.entry right S.chain.index)
          (S.outgoing right 2)) ∧
      (∀ right n, S.chain.index ≤ n →
        S.entry right n ∈ radialCore (S.family S.sigma) ∧
        (if right then S.entry right S.chain.index ≤ S.entry right n
          else S.entry right n ≤ S.entry right S.chain.index)) ∧
      (∀ right n j, 2 ≤ j → Even j → S.chain.index < n →
        radialFrequencyBand S.chain S.Cstar n j →
        r07UniformTolerance C * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine
            (radialState (S.family S.sigma) j (S.entry right n)
              ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j))
            (radialState (S.family S.sigma) j (S.entry right n)
              ((S.family S.sigma).w (S.joinInner right n)) (S.outgoing right j))) ∧
      ∃ (cFirst : ℝ) (G : MorseChainGeometryWitness S.chain)
        (H : R07ConeMiddleData) (phi : ℝ → ℝ),
        0 < cFirst ∧ cFirst ≤ 1 / 48 ∧
        S.c₀ = min cFirst (r07UniformTolerance C) ∧ R07MiddleAdmissible G H.middle ∧
        (ContDiff ℝ ∞ phi ∧ (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
          ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0) ∧
        S.family = r07MiddleReferenceFamily G H.middle phi ∧
        S.cut = (fun side n => if n = S.chain.index then H.cut side
          else r07PreviousCellCut S.chain side (n - 1)) ∧
        S.joinInner = (fun side n => if n = S.chain.index then H.join side
          else r07PreviousCellJoin S.chain side (n - 1)) := by
  classical
  let cLater : ℝ := r07UniformTolerance C
  have hC : 0 < C := (by norm_num : (0 : ℝ) < 1000).trans_le hC1000
  have hcLater : 0 < cLater := r07UniformTolerance_pos hC.le
  obtain ⟨N₀, hN₀, hthreshold⟩ := exists_r07_joinActionSmall_start hC hcLater
  obtain ⟨T, hT, ⟨G⟩⟩ := exists_morseChainGeometry (max N₀ requestedIndex)
  have hrequested : requestedIndex ≤ T.index := (le_max_right _ _).trans hT
  have hthresholdIndex : N₀ ≤ T.index := (le_max_left _ _).trans hT
  obtain ⟨phi, hPhi⟩ := exists_morseChainReference_auxiliary G
  obtain ⟨constants, hfamily⟩ := exists_r07OriginalFamily_constants G hPhi
  have hsmall : R07JoinActionSmall T C cLater :=
    hthreshold T (fun n _ => G.d_exact n) hthresholdIndex
  obtain ⟨sigma, uLater, vLater, hsigma, hlater⟩ :=
    exists_r07_selected_later hR06 G phi constants hfamily hC1000 hsmall
  have hreal := (hfamily sigma hsigma).1
  have hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T C n j :=
    fun j hj _ => morseChainRealization_existsUnique_band hreal hC hj
  have hVexists (side : Bool) (j : ℕ) (hj : 2 ≤ j) :
      ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
        RadialNaturalTail (morseChainReferenceFamily G phi sigma) side j
          (r07CellEntry T side T.index) v := by
    obtain ⟨V, hV, _, _, _⟩ :=
      exists_r07OriginalOutgoing_raw hR06 G phi constants hfamily side 0 j hj
    refine ⟨V sigma, ?_⟩
    simpa only [Nat.add_zero] using hV sigma (mem_heightCube.mpr hsigma)
  let V : Bool → ℕ → ℝ → ℝ := fun side j =>
    if hj : 2 ≤ j then Classical.choose (hVexists side j hj) else 0
  have hV (side : Bool) (j : ℕ) (hj : 2 ≤ j) (_heven : Even j)
      (_hband : radialFrequencyBand T C T.index j) :
      ContDiff ℝ ∞ (V side j) ∧
        RadialNaturalTail (morseChainReferenceFamily G phi sigma) side j
          (r07CellEntry T side T.index) (V side j) := by
    dsimp only [V]
    rw [dif_pos hj]
    exact Classical.choose_spec (hVexists side j hj)
  obtain ⟨H, cFirst, U, hM, hcFirst, hcFirst48, hfirst⟩ :=
    exists_r07_first_band_matching G phi hPhi sigma hsigma hreal C V hV
  obtain ⟨newConstants, hnewFamily⟩ := exists_r07MiddleReferenceFamily_constants G hM hPhi
  let family : (ℕ → ℝ) → ReferenceData := r07MiddleReferenceFamily G H.middle phi
  let cut : Bool → ℕ → ℝ := fun side n =>
    if n = T.index then H.cut side else r07PreviousCellCut T side (n - 1)
  let join : Bool → ℕ → ℝ := fun side n =>
    if n = T.index then H.join side else r07PreviousCellJoin T side (n - 1)
  let margin : ℕ → ℝ := fun n => if n = T.index then cFirst else cLater
  have hmargin (n : ℕ) : min cFirst cLater ≤ margin n := by
    dsimp only [margin]
    split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hmatch : ∀ side n j, 2 ≤ j → Even j → radialFrequencyBand T C n j →
      ∃ u v : ℝ → ℝ,
        R07MatchingGeometry T (family sigma) side n j (cut side n) (join side n)
          (r07CellEntry T side n) u v ∧
        margin n * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine
            (radialState (family sigma) j (r07CellEntry T side n)
              ((family sigma).w (join side n)) u)
            (radialState (family sigma) j (r07CellEntry T side n)
              ((family sigma).w (join side n)) v) := by
    intro side n j hj heven hband
    by_cases hn : n = T.index
    · subst n
      have hm := hfirst side j hj heven hband
      refine ⟨U side j, V side j, ?_, ?_⟩
      · simpa only [family, cut, join, if_pos rfl] using hm.2.1
      · simpa only [family, cut, join, margin, if_pos rfl] using hm.2.2
    · have hnlt : T.index < n := by have := hband.1; omega
      let q : R07LaterCondition T C := ⟨(side, ⟨(n, j), hj, heven, hband⟩), hnlt⟩
      have hm := hlater q
      have hk : T.index + (n - 1 - T.index) = n - 1 := by omega
      have hcut := r07PreviousCellCut_outside_middle G hreal side (n - 1 - T.index)
      rw [hk] at hcut
      have hgeometry := R07MatchingGeometry.replace_middle hM hsigma hm.1 hn hcut
      have hangle :
          cLater * exp (-(n : ℝ) ^ 2) ≤
            radialAngleSine
              (radialState (family sigma) j (r07CellEntry T side n)
                ((family sigma).w (r07PreviousCellJoin T side (n - 1))) (uLater q))
              (radialState (family sigma) j (r07CellEntry T side n)
                ((family sigma).w (r07PreviousCellJoin T side (n - 1))) (vLater q)) := by
        dsimp only [family]
        rw [R07MatchingGeometry.angle_replace_middle hM hsigma hm.1 hcut]
        exact hm.2
      refine ⟨uLater q, vLater q, ?_, ?_⟩
      · simpa only [family, cut, join, if_neg hn] using hgeometry
      · simpa only [family, cut, join, margin, if_neg hn] using hangle
  obtain ⟨incoming, outgoing, hselected, hangles⟩ :=
    exists_r10a_selected_fixed_data T family newConstants sigma C (min cFirst cLater)
      cut join (r07CellEntry T) margin hbands hC (lt_min hcFirst hcLater)
      hmargin hsigma hnewFamily hmatch
  let S : SelectedTailData := r07SelectedTailData T family newConstants sigma C
    (min cFirst cLater) cut join (r07CellEntry T) incoming outgoing hbands
  have hnewReal := (hnewFamily sigma hsigma).1
  have hfirstBand : radialFrequencyBand T C T.index 2 :=
    r10a_actual_first_band_two hnewReal hC1000 (by have := G.start_large; omega)
  refine ⟨S, hselected, rfl, hrequested, G.start_large, rfl, ?_, hfirstBand,
    ?_, ?_, ?_, ?_⟩
  · exact G.middle_gap
  · intro right
    have hf := hselected.2.2.2.2.2 right T.index 2 le_rfl (by decide) hfirstBand
    rcases hf with ⟨_, hentry, _, _, _, _, _, _, _, _, _, hnatural, _⟩
    exact ⟨hentry, r10a_middle_initial_derivative_pos G hM sigma hsigma right, hnatural⟩
  · intro right n hn
    simpa only [S, r07SelectedTailData, r07CellEntry] using
      r10a_actual_entry_retained hnewReal right hn
  · intro right n j hj heven hn hband
    have hnne : n ≠ T.index := hn.ne'
    have ha := hangles right n j hj heven hband
    simpa only [S, r07SelectedTailData, margin, if_neg hnne, cLater] using ha
  · exact ⟨cFirst, G, H, phi, hcFirst, hcFirst48, rfl, hM, hPhi, rfl, rfl, rfl⟩

end ContinuousFlexibility.Radial
