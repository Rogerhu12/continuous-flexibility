import ContinuousFlexibility.Radial.R07IncomingSelection
import ContinuousFlexibility.Radial.R07FirstBandMatching
import ContinuousFlexibility.Radial.R07ExistentialAssembly

/-!
# One actual selected tail for every frequency

A uniform numerical tolerance is fixed before the geometry. The concrete
incoming and outgoing families select all noninitial bands at once. The
remaining finite band is matched by a fixed middle replacement, which
preserves every previously selected tail. The positive minimum of the two
margins gives exactly the public selected-tail statement.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem r07_complete (hR06 : R06Statement) : R07Statement := by
  classical
  let Cstar : ℝ := 1000
  let cLater : ℝ := r07UniformTolerance Cstar
  have hC : 0 < Cstar := by norm_num [Cstar]
  have hC1000 : 1000 ≤ Cstar := le_rfl
  have hcLater : 0 < cLater := r07UniformTolerance_pos hC.le
  obtain ⟨N, hN, hthreshold⟩ := exists_r07_joinActionSmall_start hC hcLater
  obtain ⟨T, hT, ⟨G⟩⟩ := exists_morseChainGeometry N
  obtain ⟨phi, hPhi⟩ := exists_morseChainReference_auxiliary G
  obtain ⟨constants, hfamily⟩ := exists_r07OriginalFamily_constants G hPhi
  have hsmall : R07JoinActionSmall T Cstar cLater :=
    hthreshold T (fun n _ => G.d_exact n) hT
  obtain ⟨sigma, uLater, vLater, hsigma, hlater⟩ :=
    exists_r07_selected_later hR06 G phi constants hfamily hC1000 hsmall
  have hreal := (hfamily sigma hsigma).1
  have hbands : ∀ j, 2 ≤ j → Even j → ∃! n, radialFrequencyBand T Cstar n j :=
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
      (_hband : radialFrequencyBand T Cstar T.index j) :
      ContDiff ℝ ∞ (V side j) ∧
        RadialNaturalTail (morseChainReferenceFamily G phi sigma) side j
          (r07CellEntry T side T.index) (V side j) := by
    dsimp only [V]
    rw [dif_pos hj]
    exact Classical.choose_spec (hVexists side j hj)
  obtain ⟨H, cFirst, U, hM, hcFirst, hcFirst48, hfirst⟩ :=
    exists_r07_first_band_matching G phi hPhi sigma hsigma hreal Cstar V hV
  obtain ⟨newConstants, hnewFamily⟩ := exists_r07MiddleReferenceFamily_constants G hM hPhi
  let family := r07MiddleReferenceFamily G H.middle phi
  let cut : Bool → ℕ → ℝ := fun side n =>
    if n = T.index then H.cut side else r07PreviousCellCut T side (n - 1)
  let join : Bool → ℕ → ℝ := fun side n =>
    if n = T.index then H.join side else r07PreviousCellJoin T side (n - 1)
  apply r07_exists_selectedTail_of_band_matching T family newConstants sigma Cstar
    (min cFirst cLater) cut join (r07CellEntry T) hbands hC (lt_min hcFirst hcLater)
    hsigma hnewFamily
  intro side n j hj heven hband
  by_cases hn : n = T.index
  · subst n
    have hmatch := hfirst side j hj heven hband
    refine ⟨U side j, V side j, ?_, ?_⟩
    · simpa only [cut, join, if_pos rfl] using hmatch.2.1
    · have ha := (mul_le_mul_of_nonneg_right (min_le_left cFirst cLater)
        (exp_pos (-(T.index : ℝ) ^ 2)).le).trans hmatch.2.2
      simpa only [cut, join, if_pos rfl] using ha
  · have hnlt : T.index < n := by have := hband.1; omega
    let q : R07LaterCondition T Cstar := ⟨(side, ⟨(n, j), hj, heven, hband⟩), hnlt⟩
    have hmatch := hlater q
    have hk : T.index + (n - 1 - T.index) = n - 1 := by omega
    have hcut := r07PreviousCellCut_outside_middle G hreal side (n - 1 - T.index)
    rw [hk] at hcut
    have hgeometry := R07MatchingGeometry.replace_middle hM hsigma hmatch.1 hn hcut
    have hangle :
        cLater * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine
            (radialState (family sigma) j (r07CellEntry T side n)
              ((family sigma).w (r07PreviousCellJoin T side (n - 1))) (uLater q))
            (radialState (family sigma) j (r07CellEntry T side n)
              ((family sigma).w (r07PreviousCellJoin T side (n - 1))) (vLater q)) := by
      rw [R07MatchingGeometry.angle_replace_middle hM hsigma hmatch.1 hcut]
      exact hmatch.2
    refine ⟨uLater q, vLater q, ?_, ?_⟩
    · simpa only [cut, join, if_neg hn] using hgeometry
    · have ha := (mul_le_mul_of_nonneg_right (min_le_right cFirst cLater)
        (exp_pos (-(n : ℝ) ^ 2)).le).trans hangle
      simpa only [cut, join, if_neg hn] using ha

end ContinuousFlexibility.Radial
