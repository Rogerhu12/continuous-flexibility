import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# Completing radial cells along intervals of one index

This operation preserves the profile, all localizers, and their indices.
An interval covered pointwise by cells with one index is then contained
in one completed cell.  The full accumulating-profile contract survives
with at most a factor five in its constants.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- Complete each cell along intervals covered by cells of the same index. -/
def saturateReferenceCells (D : ReferenceData) : ReferenceData :=
  { D with
    cells := fun m => {r | ∃ s ∈ D.cells m,
      ∀ t ∈ uIcc s r, ∃ j, D.cellIndex j = D.cellIndex m ∧ t ∈ D.cells j} }

theorem subset_saturateReferenceCells (D : ReferenceData) (m : ℕ) :
    D.cells m ⊆ (saturateReferenceCells D).cells m := by
  intro r hr
  refine ⟨r, hr, ?_⟩
  intro t ht
  have htr : t = r := by simpa using ht
  subst t
  exact ⟨m, rfl, hr⟩

theorem saturateReferenceCells_point {D : ReferenceData} {m : ℕ} {r : ℝ}
    (hr : r ∈ (saturateReferenceCells D).cells m) :
    ∃ j, D.cellIndex j = D.cellIndex m ∧ r ∈ D.cells j := by
  obtain ⟨s, hs, hsegment⟩ := hr
  exact hsegment r (by simp)

theorem radialPartition_saturateReferenceCells {D : ReferenceData}
    (hD : RadialPartition D) : RadialPartition (saturateReferenceCells D) := by
  rcases hD with ⟨hsmooth, hpos, hsupport, hcore, hsum, hfinite⟩
  refine ⟨hsmooth, hpos, ?_, ?_, hsum, hfinite⟩
  · intro m r hr
    exact subset_saturateReferenceCells D m (hsupport m hr)
  · intro m r hr
    obtain ⟨j, hj, hrj⟩ := saturateReferenceCells_point hr
    exact hcore j hrj

theorem radialTraceScaffold_saturateReferenceCells {D : ReferenceData}
    (hD : RadialTraceScaffold D) :
    RadialTraceScaffold (saturateReferenceCells D) := by
  rcases hD with ⟨centers, widths, K, hK, hdata, hdisjoint⟩
  refine ⟨centers, widths, K, hK, ?_, hdisjoint⟩
  intro m
  obtain ⟨hcenter, hwidth, hlower, hinterval⟩ := hdata m
  exact ⟨subset_saturateReferenceCells D m hcenter, hwidth, hlower,
    hinterval.trans (subset_saturateReferenceCells D m)⟩

private theorem sameIndex_segment_length {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) {m : ℕ} {r s : ℝ}
    (hr : r ∈ D.cells m)
    (hsegment : ∀ t ∈ uIcc r s,
      ∃ j, D.cellIndex j = D.cellIndex m ∧ t ∈ D.cells j) :
    |s - r| ≤ 2 * (C 0 * exp (-(D.cellIndex m : ℝ) ^ 2)) := by
  rcases hD with ⟨hgeom, hpart, hC, hne, hfinite, hlocal, hdist, hrest⟩
  have hrCore := hpart.2.2.2.1 m hr
  obtain ⟨j, hj, hsj⟩ := hsegment s (by simp)
  have hsCore := hpart.2.2.2.1 j hsj
  have hmid : (r + s) / 2 ∈ uIcc r s := by
    rcases le_total r s with h | h
    · rw [uIcc_of_le h]
      constructor <;> linarith
    · rw [uIcc_of_ge h]
      constructor <;> linarith
  obtain ⟨k, hk, hmidk⟩ := hsegment ((r + s) / 2) hmid
  have hupper := (hdist k ((r + s) / 2) hmidk).2
  rw [hk] at hupper
  have hforward : (s - r) / 2 ≤
      min ((r + s) / 2 - D.a) (D.b - (r + s) / 2) :=
    le_min (by linarith only [hrCore.1]) (by linarith only [hsCore.2])
  have hbackward : (r - s) / 2 ≤
      min ((r + s) / 2 - D.a) (D.b - (r + s) / 2) :=
    le_min (by linarith only [hsCore.1]) (by linarith only [hrCore.2])
  apply abs_le.mpr
  constructor <;> linarith only [hforward, hbackward, hupper]

/-- Completing cells changes no analytic data and preserves every
quantitative requirement of an accumulating profile. -/
theorem isAccumulatingProfile_saturateReferenceCells {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    IsAccumulatingProfile (saturateReferenceCells D) := by
  obtain ⟨C, hbounds⟩ := hD
  have hC := hbounds.2.2.1
  have henlarged : AccumulatingProfileBounds D (fun s => 5 * C s) :=
    hbounds.mono (fun s => by linarith only [hC s])
  rcases henlarged with
    ⟨hgeom, hpart, hC', hne, hfinite, hlocal, hdist, hlow, hjet,
      hinv, hwidth, hscale, htrace⟩
  refine ⟨fun s => 5 * C s, hgeom, radialPartition_saturateReferenceCells hpart,
    hC', ?_, hfinite, ?_, ?_, ?_, ?_, ?_, ?_, hscale,
    radialTraceScaffold_saturateReferenceCells htrace⟩
  · intro m
    exact (hne m).mono (subset_saturateReferenceCells D m)
  · intro K hK hKcore
    have hOld := hlocal K hK hKcore
    obtain ⟨N, hN⟩ := (hOld.image D.cellIndex).bddAbove
    apply (hfinite N).subset
    intro m hm
    obtain ⟨r, hr, hrK⟩ := hm
    obtain ⟨j, hj, hrj⟩ := saturateReferenceCells_point hr
    have hjN : D.cellIndex j ≤ N := hN ⟨j, ⟨r, hrj, hrK⟩, rfl⟩
    simpa only [Set.mem_setOf_eq, hj] using hjN
  · intro m r hr
    obtain ⟨j, hj, hrj⟩ := saturateReferenceCells_point hr
    simpa only [saturateReferenceCells, hj] using hdist j r hrj
  · intro m r hr
    obtain ⟨j, hj, hrj⟩ := saturateReferenceCells_point hr
    simpa only [saturateReferenceCells, hj] using hlow j r hrj
  · intro m r hr s
    obtain ⟨j, hj, hrj⟩ := saturateReferenceCells_point hr
    simpa only [saturateReferenceCells, hj] using hjet j r hrj s
  · intro m r hr s
    obtain ⟨j, hj, hrj⟩ := saturateReferenceCells_point hr
    simpa only [saturateReferenceCells, hj] using hinv j r hrj s
  · intro m
    obtain ⟨l, h, hsub, hlength⟩ := hbounds.2.2.2.2.2.2.2.2.2.2.1 m
    let δ : ℝ := C 0 * exp (-(D.cellIndex m : ℝ) ^ 2)
    refine ⟨l - 2 * δ, h + 2 * δ, ?_, ?_⟩
    · intro r hr
      obtain ⟨s, hs, hsegment⟩ := hr
      have hsr := sameIndex_segment_length hbounds hs hsegment
      obtain ⟨hlower, hupper⟩ := abs_le.mp hsr
      obtain ⟨hsl, hsh⟩ := hsub hs
      change l - 2 * δ ≤ r ∧ r ≤ h + 2 * δ
      dsimp only [δ] at *
      constructor <;> linarith only [hlower, hupper, hsl, hsh]
    · dsimp only [δ, saturateReferenceCells]
      nlinarith only [hlength]

/-- Pointwise coverage with one fixed index gives whole-interval coverage
after the explicit completion. -/
theorem saturateReferenceCells_covers_interval {D : ReferenceData}
    {l h : ℝ} {n : ℕ} (hlh : l < h)
    (hcover : ∀ r ∈ Ioo l h, ∃ m, D.cellIndex m = n ∧ r ∈ D.cells m) :
    ∃ m, D.cellIndex m = n ∧
      Ioo l h ⊆ (saturateReferenceCells D).cells m := by
  have hmiddle : (l + h) / 2 ∈ Ioo l h := by
    constructor <;> linarith
  obtain ⟨m, hm, hmem⟩ := hcover ((l + h) / 2) hmiddle
  refine ⟨m, hm, ?_⟩
  intro r hr
  refine ⟨(l + h) / 2, hmem, ?_⟩
  intro t ht
  have htI : t ∈ Ioo l h := by
    rcases le_total ((l + h) / 2) r with horder | horder
    · rw [uIcc_of_le horder] at ht
      exact ⟨hmiddle.1.trans_le ht.1, ht.2.trans_lt hr.2⟩
    · rw [uIcc_of_ge horder] at ht
      exact ⟨hr.1.trans_le ht.1, ht.2.trans_lt hmiddle.2⟩
  obtain ⟨j, hj, htj⟩ := hcover t htI
  exact ⟨j, hj.trans hm.symm, htj⟩

end ContinuousFlexibility.Radial
