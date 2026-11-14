module

public import ContinuousFlexibility.Analysis.N06ReferenceCutTravel
public import ContinuousFlexibility.Analysis.N06NegativePieceFiniteness
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# Radiality of the selected reference charts on the negative halves

The actual N04 forward charts on the two halves of every original
negative component are radial at the reference state.  This is derived
from their null characteristics, the common cut radius and the original
irrational return margin.  No chosen Morse realization, coordinate
formula, boundary inverse value or additional matching condition is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_tricomiTime_injectiveOn :
    Set.InjOn n05TricomiTime (Ici (0 : ℝ)) := by
  apply (strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    n05TricomiTime_continuous.continuousOn ?_).injOn
  intro x hx
  have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  rw [(n05TricomiTime_hasDerivAt hxpos).deriv]
  exact Real.sqrt_pos.mpr hxpos

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- An actual negative root-to-cut chart with incommensurable doubled
cut time has no nontrivial angular reparametrization at reference. -/
theorem n06_reference_root_cut_radial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (hinside : Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D)
    {root cut y : ℝ} (hroot : root ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hcut : cut ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hwroot : deriv D.w root = 0) (hy : 0 < y)
    (hcutImage : ∀ θ, (K.chart (C.referenceState, 0) i (cut, θ)).1 = y)
    (hirr : Irrational ((2 * n05TricomiTime y) / Real.pi)) :
    ∃ τ : ℝ, τ ^ 2 = 1 ∧ τ * opticalTravel D.w root cut = n05TricomiTime y ∧
      ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ,
        K.chart (C.referenceState, 0) i (r, θ) =
            ((K.chart (C.referenceState, 0) i (r, 0)).1, θ) ∧
          K.height (C.referenceState, 0) i (r, θ) =
            K.height (C.referenceState, 0) i (r, 0) ∧
          n05TricomiTime (K.chart (C.referenceState, 0) i (r, θ)).1 =
            τ * opticalTravel D.w root r := by
  let Ψ : PolarPoint → PolarPoint := K.chart (C.referenceState, 0) i
  let H : PolarPoint → ℝ := K.height (C.referenceState, 0) i
  let β : ℝ → ℝ := fun θ => (Ψ (root, θ)).2
  have h01 := h.1.1.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hA := h.2.2.2.2.1.1
  have hpieces := hA.referenceBounds
  have hnegative := hA.referenceNegative
  have hclosed (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :=
    n05_reference_boundary_regular hA href hs i (p := p) hp
  have hrootClosed (θ : ℝ) : (root, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) i := by
    rw [n05_referencePhysicalPieceClosed_eq hA i]
    exact ⟨hroot, mem_univ _⟩
  have hΨ (p : PolarPoint) (hp : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      ContDiffAt ℝ ∞ Ψ p := (hclosed p hp).1
  have hH (p : PolarPoint) (hp : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      ContDiffAt ℝ ∞ H p := (hclosed p hp).2.1
  have hβ : Continuous β := continuous_iff_continuousAt.mpr fun θ =>
    (hΨ (root, θ) hroot).continuousAt.snd.comp
      (continuousAt_const.prodMk continuousAt_id)
  have hlift (θ : ℝ) : β (θ + Real.pi) = β θ + Real.pi := by
    simpa only [β, Ψ, Prod.mk_add_mk, Prod.snd_add, Prod.fst_add, add_zero] using
      congrArg Prod.snd (n05_canonical_closed_periodicity h.2.2.2.2.1 href hs i
        (p := (root, θ)) (hrootClosed θ)).1
  have hodd : Function.Odd β := by
    intro θ
    exact congrArg Prod.snd (n05_canonical_closed_reflection h.2.2.2.2.1 href hs i
      (p := (root, θ)) (hrootClosed θ)).1
  obtain ⟨τ, hτ, htravel, hperiod, hformula⟩ :=
    n06_reference_null_root_cut hT hS h hi hinside hroot hcut hwroot hy hcutImage
  have hβid : β = id := n06_circleLift_eq_id_of_irrational hβ hlift hodd hperiod hirr
  have hvalues (r : ℝ) (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
      (Ψ (r, θ)).2 = θ ∧
        n05TricomiTime (Ψ (r, θ)).1 = τ * opticalTravel D.w root r := by
    obtain ⟨hp, hm⟩ := hformula r hr θ
    change n05NullCoordinate Ψ 1 (r, θ) = β (θ + τ * opticalTravel D.w root r) at hp
    change n05NullCoordinate Ψ (-1) (r, θ) = β (θ - τ * opticalTravel D.w root r) at hm
    rw [hβid] at hp hm
    simp only [n05NullCoordinate, one_mul, neg_one_mul, id_eq] at hp hm
    constructor <;> linarith only [hp, hm]
  have hξpos (p : PolarPoint) (hp : p.1 ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) :
      0 < (Ψ p).1 :=
    n05_negative_reference_radius_pos hT hS h hi ⟨hp.1.le, hp.2.le⟩
      ⟨hinside ⟨hp.1.le, hp.2.le⟩, mem_univ _⟩ (hnegative i hi p.1 hp)
  have hchartOpen (p : PolarPoint)
      (hp : p.1 ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) :
      Ψ p = ((Ψ (p.1, 0)).1, p.2) := by
    apply Prod.ext
    · apply n06_tricomiTime_injectiveOn (hξpos p hp).le (hξpos (p.1, 0) hp).le
      exact (hvalues p.1 ⟨hp.1.le, hp.2.le⟩ p.2).2.trans
        (hvalues p.1 ⟨hp.1.le, hp.2.le⟩ 0).2.symm
    · exact (hvalues p.1 ⟨hp.1.le, hp.2.le⟩ p.2).1
  have hchartClosed (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      Ψ p = ((Ψ (p.1, 0)).1, p.2) := by
    apply n05_eqOn_closed_strip_of_nonreflection (hpieces i).1
      (f := Ψ) (g := fun q => ((Ψ (q.1, 0)).1, q.2))
      (fun q hq => (hΨ q hq).continuousAt) ?_
      (fun q hq _ => hchartOpen q hq) p hp
    intro q hq
    have hc : ContinuousAt (fun p : PolarPoint => (Ψ (p.1, 0)).1) q :=
      ((hΨ (q.1, 0) hq).continuousAt.fst).comp
        (f := fun p : PolarPoint => (p.1, (0 : ℝ))) (x := q)
        (continuousAt_fst.prodMk continuousAt_const)
    exact hc.prodMk continuousAt_snd
  obtain ⟨B, hB⟩ := h01.1.1
  have hheightOpen (p : PolarPoint)
      (hp : p.1 ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) : H p = H (p.1, 0) := by
    have hpc : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) := ⟨hp.1.le, hp.2.le⟩
    have hw : 0 < D.w p.1 := hB.1.2.2.2.2.1 p.1 (hinside hpc)
    have hr : 0 < p.1 := hB.1.1.trans (hinside hpc).1
    have hd : deriv D.w p.1 < 0 := hnegative i hi p.1 hp
    have hcoef : D.w p.1 * (deriv D.w p.1 / p.1) ≠ 0 :=
      mul_ne_zero hw.ne' (div_ne_zero hd.ne hr.ne')
    have he₁ := n05_negative_reference_determinant_closed hT hS h hi (x := p) hpc
    have he₂ := n05_negative_reference_determinant_closed hT hS h hi (x := (p.1, 0)) hpc
    have hpow : H p ^ 4 = H (p.1, 0) ^ 4 := by
      apply mul_right_cancel₀ hcoef
      exact he₁.trans ((congrArg (fun q : PolarPoint => -q.1) (hchartOpen p hp)).trans he₂.symm)
    exact (pow_left_inj₀ (hclosed p hpc).2.2.2.le
      (hclosed (p.1, 0) hpc).2.2.2.le
      (by norm_num : (4 : ℕ) ≠ 0)).mp hpow
  have hheightClosed (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i)) : H p = H (p.1, 0) := by
    apply n05_eqOn_closed_strip_of_nonreflection (hpieces i).1
      (f := H) (g := fun q => H (q.1, 0))
      (fun q hq => (hH q hq).continuousAt) ?_
      (fun q hq _ => hheightOpen q hq) p hp
    intro q hq
    exact (hH (q.1, 0) hq).continuousAt.comp
      (f := fun p : PolarPoint => (p.1, (0 : ℝ))) (x := q)
      (continuousAt_fst.prodMk continuousAt_const)
  exact ⟨τ, hτ, htravel, fun r hr θ =>
    ⟨hchartClosed (r, θ) hr, hheightClosed (r, θ) hr, (hvalues r hr θ).2⟩⟩

/-- Every selected negative half has the true radial reference chart and
height.  The only inputs are the original Through04 witness and its
original material and physical-space realizations. -/
theorem n06_reference_cutPair_radial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {i : ℕ} (hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2) :
    ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ,
      K.chart (C.referenceState, 0) i (r, θ) =
          ((K.chart (C.referenceState, 0) i (r, 0)).1, θ) ∧
        K.height (C.referenceState, 0) i (r, θ) = K.height (C.referenceState, 0) i (r, 0) := by
  have h01 := h.1.1.1
  have hg : controlGeometryConditions D S C := h01.2.2.2.1
  have hneg : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hg.1 m).1, (hg.1 m).2.1, (hg.1 m).2.2,
      (hg.2.1 m).1, (hg.2.1 m).2.1, hg.2.2.2.1 m⟩
  obtain ⟨A, _, hreturn⟩ := h01.1.2.2.1.2
  have hirr : Irrational ((2 * n05TricomiTime (K.cutRadius m)) / Real.pi) := by
    rw [← (n06_reference_cut_travel hT hS h m).2.2]
    exact (hreturn (C.left m) (C.right m) hneg).1.1
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hcuts := h.2.2.2.2.1.2.1.1.1
  obtain ⟨hnegL, hnegR, hl, hr, hmeet, hy, _, _, _, _⟩ := hcuts m
  let c := K.physicalRight (K.cutPair m).1
  have hrootL : C.left m ∈ Icc (K.physicalLeft (K.cutPair m).1)
      (K.physicalRight (K.cutPair m).1) := by
    rw [← hl]
    exact ⟨le_rfl, (hpieces (K.cutPair m).1).1.le⟩
  have hrootR : C.right m ∈ Icc (K.physicalLeft (K.cutPair m).2)
      (K.physicalRight (K.cutPair m).2) := by
    rw [← hr]
    exact ⟨(hpieces (K.cutPair m).2).1.le, le_rfl⟩
  have hcutL : c ∈ Icc (K.physicalLeft (K.cutPair m).1)
      (K.physicalRight (K.cutPair m).1) := ⟨(hpieces (K.cutPair m).1).1.le, le_rfl⟩
  have hcutR : c ∈ Icc (K.physicalLeft (K.cutPair m).2)
      (K.physicalRight (K.cutPair m).2) := by
    dsimp only [c]
    rw [hmeet]
    exact ⟨le_rfl, (hpieces (K.cutPair m).2).1.le⟩
  rcases hi with rfl | rfl
  · obtain ⟨_, _, _, hradial⟩ := n06_reference_root_cut_radial hT hS h hnegL
      (n06_cutPiece_closed_subset h m (Or.inl rfl)) hrootL hcutL (hg.2.1 m).1 hy
      (fun θ => n05_cut_reference_image hT hS h m (Or.inl rfl) θ) hirr
    exact fun r hr θ => ⟨(hradial r hr θ).1, (hradial r hr θ).2.1⟩
  · obtain ⟨_, _, _, hradial⟩ := n06_reference_root_cut_radial hT hS h hnegR
      (n06_cutPiece_closed_subset h m (Or.inr rfl)) hrootR hcutR (hg.2.1 m).2.1 hy
      (fun θ => n05_cut_reference_image hT hS h m (Or.inr rfl) θ) hirr
    exact fun r hr θ => ⟨(hradial r hr θ).1, (hradial r hr θ).2.1⟩

/-- The actual negative pieces are exhausted by the original cut halves,
so the radiality statement holds for every negative index of the selected
atlas, including both endpoint germs. -/
theorem n06_reference_negative_radial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) :
    ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ,
      K.chart (C.referenceState, 0) i (r, θ) =
          ((K.chart (C.referenceState, 0) i (r, 0)).1, θ) ∧
        K.height (C.referenceState, 0) i (r, θ) = K.height (C.referenceState, 0) i (r, 0) := by
  obtain ⟨m, hm⟩ := n06_negativePiece_is_cutHalf h.2.2.2.2.1 h.1.1.1.2.2.2.1 hi
  exact n06_reference_cutPair_radial hT hS h m hm

end ContinuousFlexibility.Statements
