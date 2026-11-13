import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData
import ContinuousFlexibility.Analysis.N04RealizationPotentialRegularity

/-!
# Linear operations on selected current height data

Addition, fixed scalar families and angular differentiation preserve the
selected-piece quantifiers.  Angular differentiation shifts the common
loss once and never changes the state neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

private theorem height_parameterGrading_mono (S : PhysicalSpacesData) :
    Monotone (parameterGrading S) :=
  tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)

/-- Sum two coefficient-envelope bounds while preserving one common
height factor and one common state weight. -/
theorem n04NegativeHeight_add_cost {A B E H X Y W u v : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXW : X ≤ W) (hYW : Y ≤ W)
    (hu : |u| ≤ A * E ^ A * H * X) (hv : |v| ≤ B * E ^ B * H * Y) :
    |u + v| ≤ (A + B) * E ^ (A + B) * H * W := by
  have hEp : 0 ≤ E ^ (A + B) := Real.rpow_nonneg (zero_le_one.trans hE) _
  have hu' : |u| ≤ A * E ^ (A + B) * H * W :=
    hu.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hB)) hA) hH)
      hXW hX (mul_nonneg (mul_nonneg hA hEp) hH))
  have hv' : |v| ≤ B * E ^ (A + B) * H * W :=
    hv.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hA)) hB) hH)
      hYW hY (mul_nonneg (mul_nonneg hB hEp) hH))
  exact ((abs_add_le u v).trans (add_le_add hu' hv')).trans_eq (by ring)

/-- The derivative of a periodic smooth field is periodic on the same
unit strip.  Only local smoothness on that strip is used. -/
theorem n04NegativeHeight_angularPartial_periodic
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f unitStrip)
    (hperiod : ∀ q ∈ unitStrip, f (q + (0, Real.pi)) = f q)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    angularPartial f (q + (0, Real.pi)) = angularPartial f q := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hs : q + (0, Real.pi) ∈ unitStrip :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have he : (fun y => f (y + (0, Real.pi))) =ᶠ[𝓝 q] f := by
    filter_upwards [hU.mem_nhds hq] with y hy
    exact hperiod y hy
  have hd := ((hf _ hs).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp q ((hasFDerivAt_id q).add_const (0, Real.pi))
  have hder : fderiv ℝ f (q + (0, Real.pi)) = fderiv ℝ f q := by
    have h := hc.fderiv.symm.trans he.fderiv_eq
    simpa only [ContinuousLinearMap.comp_id] using h
  exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) hder

private theorem height_angularPartial_smooth {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) :
    ContDiffOn ℝ ∞ (angularPartial f) unitStrip :=
  contDiffOn_cylinderPartial (isOpen_Ioo.prod isOpen_univ) hf (0, 1)

private theorem height_mixed_add_difference
    {f g f₀ g₀ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) (hg : ContDiffOn ℝ ∞ g unitStrip)
    (hf₀ : ContDiffOn ℝ ∞ f₀ unitStrip) (hg₀ : ContDiffOn ℝ ∞ g₀ unitStrip)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip) :
    mixedDerivative i j (fun y => (f y + g y) - (f₀ y + g₀ y)) q =
      mixedDerivative i j (fun y => f y - f₀ y) q +
        mixedDerivative i j (fun y => g y - g₀ y) q := by
  have heq : (fun y => (f y + g y) - (f₀ y + g₀ y)) =
      (fun y => (f y - f₀ y) + (g y - g₀ y)) := by
    funext y
    ring
  rw [heq]
  exact n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    (hf.sub hf₀) (hg.sub hg₀) i j hq

private theorem height_mixed_angular_difference
    {f f₀ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) (hf₀ : ContDiffOn ℝ ∞ f₀ unitStrip)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip) :
    mixedDerivative i j (fun y => angularPartial f y - angularPartial f₀ y) q =
      mixedDerivative i (j + 1) (fun y => f y - f₀ y) q := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  calc
    _ = mixedDerivative i j (angularPartial f) q -
        mixedDerivative i j (angularPartial f₀) q :=
      mixedDerivative_sub_of_contDiffOn hU
        (height_angularPartial_smooth hf) (height_angularPartial_smooth hf₀) i j hq
    _ = mixedDerivative i (j + 1) f q - mixedDerivative i (j + 1) f₀ q :=
      congrArg₂ (fun x y : ℝ => x - y)
        (mixedDerivative_angularPartial hU hf i j hq)
        (mixedDerivative_angularPartial hU hf₀ i j hq)
    _ = _ := (mixedDerivative_sub_of_contDiffOn hU hf hf₀ i (j + 1) hq).symm

section Data

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

theorem N04HeightReferenceDataOn.height_add
    (hf : N04HeightReferenceDataOn T cell P f₀)
    (hg : N04HeightReferenceDataOn T cell P g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04HeightReferenceDataOn T cell P (fun m q => f₀ m q + g₀ m q) := by
  refine ⟨fun m hm => ⟨(hf.1 m hm).1.add (hg.1 m hm).1,
    fun q hq => congrArg₂ (fun x y : ℝ => x + y)
      ((hf.1 m hm).2 q hq) ((hg.1 m hm).2 q hq)⟩, fun s => ?_⟩
  have hfs := hf.2 s
  have hgs := hg.2 s
  refine ⟨hfs.choose + hgs.choose, add_pos hfs.choose_spec.1 hgs.choose_spec.1,
    fun m hm q hq i j hij => ?_⟩
  rw [n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    (hf.1 m hm).1 (hg.1 m hm).1 i j hq]
  simpa only [mul_one] using n04NegativeHeight_add_cost
    hfs.choose_spec.1.le hgs.choose_spec.1.le (hE m)
    (H := 1) (X := 1) (Y := 1) (W := 1)
    zero_le_one zero_le_one zero_le_one le_rfl le_rfl
    (by simpa only [mul_one] using hfs.choose_spec.2 m hm q hq i j hij)
    (by simpa only [mul_one] using hgs.choose_spec.2 m hm q hq i j hij)

theorem N04HeightReferenceDataOn.height_angularPartial
    (hf : N04HeightReferenceDataOn T cell P f₀) :
    N04HeightReferenceDataOn T cell P (fun m => angularPartial (f₀ m)) := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  refine ⟨fun m hm => ⟨height_angularPartial_smooth (hf.1 m hm).1,
    n04NegativeHeight_angularPartial_periodic (hf.1 m hm).1
      (hf.1 m hm).2⟩, fun s => ?_⟩
  have h := hf.2 (s + 1)
  refine ⟨h.choose, h.choose_spec.1, fun m hm q hq i j hij => ?_⟩
  rw [mixedDerivative_angularPartial hU (hf.1 m hm).1 i j hq]
  exact h.choose_spec.2 m hm q hq i (j + 1) (by omega)

/-- Addition of actual reference differences.  Neither the reference
field nor its derivatives enter the resulting quantitative cost. -/
theorem CurrentJetDataOn.height_add
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hg : CurrentJetDataOn S T cell P base ε g g₀)
    (hf₀ : N04HeightReferenceDataOn T cell P f₀)
    (hg₀ : N04HeightReferenceDataOn T cell P g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell P base ε (fun z m q => f z m q + g z m q)
      (fun m q => f₀ m q + g₀ m q) := by
  have hmono := height_parameterGrading_mono S
  have he (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => (f z m y + g z m y) - (f₀ m y + g₀ m y)) q.val =
        mixedDerivative i j (fun y => f z m y - f₀ m y) q.val +
          mixedDerivative i j (fun y => g z m y - g₀ m y) q.val :=
    height_mixed_add_difference (hf.1 z hz m hm).1 (hg.1 z hz m hm).1
      (hf₀.1 m hm).1 (hg₀.1 m hm).1 i j q.property
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε) (fun z =>
        mixedDerivative i j
          (fun y => (f z m y + g z m y) - (f₀ m y + g₀ m y)) q.val) :=
    fun m hm i j q =>
      (smoothDirectionsAdd (hf.2.choose m hm i j q) (hg.2.choose m hm i j q)).congr
        (fun z hz => (he z hz m hm i j q).symm)
  have hfv := hf.2.choose_spec.1
  have hgv := hg.2.choose_spec.1
  refine ⟨fun z hz m hm => ⟨(hf.1 z hz m hm).1.add (hg.1 z hz m hm).1,
    fun q hq => congrArg₂ (fun x y : ℝ => x + y)
      ((hf.1 z hz m hm).2 q hq) ((hg.1 z hz m hm).2 q hq)⟩,
    J, ⟨max hfv.choose hgv.choose, fun s => ?_⟩, fun k => ?_⟩
  · have hfs := hfv.choose_spec s
    have hgs := hgv.choose_spec s
    refine ⟨hfs.choose + hgs.choose, add_pos hfs.choose_spec.1 hgs.choose_spec.1,
      fun z hz m hm q i j hij => ?_⟩
    apply (congrArg abs (he z hz m hm i j q)).trans_le
    exact n04NegativeHeight_add_cost hfs.choose_spec.1.le hgs.choose_spec.1.le (hE m)
      (Real.rpow_nonneg (hH m) _) (apply_nonneg _ _) (apply_nonneg _ _)
      (hmono (Nat.add_le_add_left (le_max_left _ _) s) z)
      (hmono (Nat.add_le_add_left (le_max_right _ _) s) z)
      (hfs.choose_spec.2 z hz m hm q i j hij)
      (hgs.choose_spec.2 z hz m hm q i j hij)
  · have hft := hf.2.choose_spec.2 k
    have hgt := hg.2.choose_spec.2 k
    refine ⟨max hft.choose hgt.choose, fun s => ?_⟩
    have hfs := hft.choose_spec s
    have hgs := hgt.choose_spec s
    refine ⟨hfs.choose + hgs.choose, add_pos hfs.choose_spec.1 hgs.choose_spec.1,
      fun z hz v m hm q i j hij => ?_⟩
    change |((hf.2.choose m hm i j q).D k z + (hg.2.choose m hm i j q).D k z) v| ≤ _
    rw [add_apply]
    exact n04NegativeHeight_add_cost hfs.choose_spec.1.le hgs.choose_spec.1.le (hE m)
      (Real.rpow_nonneg (hH m) _)
      (oneHighVariationWeight_nonneg _ _ _ _ _) (oneHighVariationWeight_nonneg _ _ _ _ _)
      (oneHighVariationWeight_mono hmono le_rfl
        (Nat.add_le_add_left (le_max_left _ _) s) z v)
      (oneHighVariationWeight_mono hmono le_rfl
        (Nat.add_le_add_left (le_max_right _ _) s) z v)
      (hfs.choose_spec.2 z hz v m hm q i j hij)
      (hgs.choose_spec.2 z hz v m hm q i j hij)

/-- Angular differentiation uses the actual shifted mixed derivatives
of the reference difference. -/
theorem CurrentJetDataOn.height_angularPartial
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hf₀ : N04HeightReferenceDataOn T cell P f₀) :
    CurrentJetDataOn S T cell P base ε (fun z m => angularPartial (f z m))
      (fun m => angularPartial (f₀ m)) := by
  have hdiff (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => angularPartial (f z m) y - angularPartial (f₀ m) y) q.val =
        mixedDerivative i (j + 1) (fun y => f z m y - f₀ m y) q.val :=
    height_mixed_angular_difference (hf.1 z hz m hm).1 (hf₀.1 m hm).1 i j q.property
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε) (fun z =>
        mixedDerivative i j
          (fun y => angularPartial (f z m) y - angularPartial (f₀ m) y) q.val) :=
    fun m hm i j q =>
      (hf.2.choose m hm i (j + 1) q).congr (fun z hz => (hdiff z hz m hm i j q).symm)
  have hv := hf.2.choose_spec.1
  refine ⟨fun z hz m hm =>
    ⟨height_angularPartial_smooth (hf.1 z hz m hm).1,
      n04NegativeHeight_angularPartial_periodic (hf.1 z hz m hm).1 (hf.1 z hz m hm).2⟩,
    J, ⟨hv.choose + 1, fun s => ?_⟩, fun k => ?_⟩
  · have hs := hv.choose_spec (s + 1)
    refine ⟨hs.choose, hs.choose_spec.1, fun z hz m hm q i j hij => ?_⟩
    apply (congrArg abs (hdiff z hz m hm i j q)).trans_le
    have ho : (s + 1) + hv.choose = s + (hv.choose + 1) := by omega
    simpa only [ho] using hs.choose_spec.2 z hz m hm q i (j + 1) (by omega)
  · have ht := hf.2.choose_spec.2 k
    refine ⟨ht.choose + 1, fun s => ?_⟩
    have hs := ht.choose_spec (s + 1)
    refine ⟨hs.choose, hs.choose_spec.1, fun z hz v m hm q i j hij => ?_⟩
    have ho : (s + 1) + ht.choose = s + (ht.choose + 1) := by omega
    simpa only [J, SmoothDirections.congr, ho] using
      hs.choose_spec.2 z hz v m hm q i (j + 1) (by omega)

/-- Values equal on the selected open pieces have exactly the same
reference differences and the same genuine parameter towers. -/
theorem CurrentJetDataOn.height_congr
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hfg : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → EqOn (f z m) (g z m) unitStrip)
    (hfg₀ : ∀ m, P m → EqOn (f₀ m) (g₀ m) unitStrip) :
    CurrentJetDataOn S T cell P base ε g g₀ := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have he (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => f z m y - f₀ m y) q.val =
        mixedDerivative i j (fun y => g z m y - g₀ m y) q.val :=
    n07a_mixedDerivative_eqOn hU
      (fun y hy => congrArg₂ (fun a b : ℝ => a - b) (hfg z hz m hm hy) (hfg₀ m hm hy))
      i j q.property
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => g z m y - g₀ m y) q.val) :=
    fun m hm i j q =>
      (hf.2.choose m hm i j q).congr (fun z hz => he z hz m hm i j q)
  refine ⟨fun z hz m hm => ⟨(hf.1 z hz m hm).1.congr
    (fun q hq => (hfg z hz m hm hq).symm), ?_⟩, J, ?_, ?_⟩
  · intro q hq
    have hs : q + (0, Real.pi) ∈ unitStrip :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
    rw [← hfg z hz m hm hs, ← hfg z hz m hm hq]
    exact (hf.1 z hz m hm).2 q hq
  · have hv := hf.2.choose_spec.1
    refine ⟨hv.choose, fun s => ⟨(hv.choose_spec s).choose,
      (hv.choose_spec s).choose_spec.1, fun z hz m hm q i j hij => ?_⟩⟩
    exact (congrArg abs (he z hz m hm i j q).symm).trans_le
      ((hv.choose_spec s).choose_spec.2 z hz m hm q i j hij)
  · intro k
    have ht := hf.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    exact fun z hz v m hm q i j hij =>
      (ht.choose_spec s).choose_spec.2 z hz v m hm q i j hij

theorem N04HeightReferenceDataOn.height_congr
    (hf : N04HeightReferenceDataOn T cell P f₀)
    (hfg : ∀ m, P m → EqOn (f₀ m) (g₀ m) unitStrip) :
    N04HeightReferenceDataOn T cell P g₀ := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  refine ⟨fun m hm => ⟨(hf.1 m hm).1.congr (fun q hq => (hfg m hm hq).symm), ?_⟩,
    fun s => ?_⟩
  · intro q hq
    have hs : q + (0, Real.pi) ∈ unitStrip :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
    rw [← hfg m hm hs, ← hfg m hm hq]
    exact (hf.1 m hm).2 q hq
  · have h := hf.2 s
    refine ⟨h.choose, h.choose_spec.1, fun m hm q hq i j hij => ?_⟩
    rw [← n07a_mixedDerivative_eqOn hU (hfg m hm) i j hq]
    exact h.choose_spec.2 m hm q hq i j hij

/-- A piecewise constant reference scalar only needs its scalar
coefficient-envelope bound. -/
theorem n04HeightReferenceDataOn_pieceConstant (c : ℕ → ℝ)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hc : ∃ B : ℝ, 0 < B ∧ ∀ m, P m → |c m| ≤ B * T.E0 (T.sample (cell m)) ^ B) :
    N04HeightReferenceDataOn T cell P (fun m _ => c m) := by
  refine ⟨fun _ _ => ⟨contDiffOn_const, fun _ _ => rfl⟩,
    fun s => ⟨hc.choose, hc.choose_spec.1, fun m hm q hq i j hij => ?_⟩⟩
  have hconst : |mixedDerivative i j (fun _ : PolarPoint => c m) q| ≤ |c m| := by
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        simp only [spaces_mixedDerivative_zero, le_refl]
      · simp [mixedDerivative, iteratedDeriv_const, hj]
    · simp [mixedDerivative, iteratedDeriv_const, hi]
  exact hconst.trans (hc.choose_spec.2 m hm)

/-- A family fixed in the state has identically zero reference
differences, including every directional derivative. -/
theorem CurrentJetDataOn.height_fixed
    (hf₀ : N04HeightReferenceDataOn T cell P f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell P base ε (fun _ => f₀) f₀ := by
  have hU : IsOpen (sectorNeighborhood S base ε ε) := isOpen_sectorNeighborhood S base ε ε
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun (_z : Parameter S) => mixedDerivative i j (fun y => f₀ m y - f₀ m y) q.val) :=
    fun m _hm i j q =>
    (smoothDirections_constant hU (0 : ℝ)).congr (fun (_z : Parameter S) _ => by
      simp only [sub_self, mixedDerivative_fun_zero])
  have hc (m : ℕ) : 0 ≤ (1 : ℝ) * T.E0 (T.sample (cell m)) ^ (1 : ℝ) *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_one
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (Real.rpow_nonneg (hH m) _)
  refine ⟨fun _ _ m hm => hf₀.1 m hm, J,
    ⟨0, fun _ => ⟨1, zero_lt_one, fun z _ m _ q i j _ => ?_⟩⟩,
    fun k => ⟨0, fun s => ⟨1, zero_lt_one, fun z hz v m hm q i j _ => ?_⟩⟩⟩
  · simp only [sub_self, mixedDerivative_fun_zero, abs_zero]
    exact mul_nonneg (hc m) (apply_nonneg _ z)
  · have hzval : (J m hm i j q).D k z v = 0 := by
      change (smoothDirections_constant hU (0 : ℝ)).D k z v = 0
      by_cases hk : k = 0
      · subst k
        exact smoothDirections_D_zero_apply _ hz v
      · exact smoothDirections_D_constant _ (Nat.pos_of_ne_zero hk) hz v
    rw [hzval, abs_zero]
    exact mul_nonneg (hc m) (oneHighVariationWeight_nonneg _ _ _ _ _)

end Data

end ContinuousFlexibility.Analysis
