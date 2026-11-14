module

public import ContinuousFlexibility.Analysis.SobolevHalfLineJets
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Smooth cores with their actual Sobolev derivatives

The domain of the extension is the space of functions smooth up to the
boundary and with all their actual derivatives in `L²`. In particular,
membership never asks for an extension to the line. The function outside
the specified set is irrelevant; the extension respects equality on the
domain. The Sobolev completions identify the resulting zero-seminorm
representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The usual smooth core for the derivative definition of the Sobolev
norms on a closed interval, a closed half-line, or the whole line. -/
def smoothSobolevCore (s : Set ℝ) (hs : MeasurableSet s) (hu : UniqueDiffOn ℝ s) :
    Submodule ℝ (ℝ → F) where
  carrier := {f | ContDiffOn ℝ ∞ f s ∧
    ∀ n : ℕ, MemLp (iteratedDerivWithin n f s) 2 (volume.restrict s)}
  zero_mem' := by
    refine ⟨contDiffOn_const, fun n => ?_⟩
    have he : iteratedDerivWithin n (0 : ℝ → F) s = 0 := by
      funext x
      simp only [Pi.zero_def, iteratedDerivWithin_fun_const_zero]
    rw [he]
    exact MemLp.zero
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, fun n => ?_⟩
    have he : (iteratedDerivWithin n f s + iteratedDerivWithin n g s) =ᵐ[volume.restrict s]
        iteratedDerivWithin n (f + g) s := by
      filter_upwards [ae_restrict_mem hs] with x hx
      exact (iteratedDerivWithin_add hx hu ((hf.1 x hx).of_le (by simp))
        ((hg.1 x hx).of_le (by simp))).symm
    exact (memLp_congr_ae he).mp ((hf.2 n).add (hg.2 n))
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, fun n => ?_⟩
    have he : (c • iteratedDerivWithin n f s) =ᵐ[volume.restrict s]
        iteratedDerivWithin n (c • f) s := by
      filter_upwards [ae_restrict_mem hs] with x hx
      exact (iteratedDerivWithin_const_smul hx hu c ((hf.1 x hx).of_le (by simp))).symm
    exact (memLp_congr_ae he).mp ((hf.2 n).const_smul c)

/-- Function evaluation on the existing submodule carrier. -/
instance smoothSobolevCore.instCoeFun (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) : CoeFun (smoothSobolevCore F s hs hu) (fun _ => ℝ → F) :=
  ⟨fun f => f.val⟩

abbrev HalfLineSobolevCore : Submodule ℝ (ℝ → F) :=
  smoothSobolevCore F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0)

abbrev LineSobolevCore : Submodule ℝ (ℝ → F) :=
  smoothSobolevCore F univ MeasurableSet.univ uniqueDiffOn_univ

variable {F} [CompleteSpace F]

/-- The actual within-derivatives of a smooth Sobolev function form a
bounded half-line jet. Boundedness follows from `L²`, not from an input
extension or an extra pointwise assumption. -/
theorem isBoundedHalfLineJet_iteratedDerivWithin {f : ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (hL₂ : ∀ n : ℕ, MemLp (iteratedDerivWithin n f (Ici 0)) 2
      (volume.restrict (Ici 0))) :
    IsBoundedHalfLineJet (fun n => iteratedDerivWithin n f (Ici 0)) := by
  apply isBoundedHalfLineJet_of_memLp
  · intro n
    exact hf.continuousOn_iteratedDerivWithin (by simp) (uniqueDiffOn_Ici 0)
  · intro n x hx
    have hd := (hf.differentiableOn_iteratedDerivWithin
      (m := n) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
      (uniqueDiffOn_Ici 0) x hx.le).hasDerivWithinAt
    rw [iteratedDerivWithin_succ]
    exact hd.hasDerivAt (Ici_mem_nhds hx)
  · exact hL₂

theorem HalfLineSobolevCore.bounded (f : HalfLineSobolevCore F) :
    ∃ M : ℝ, ∀ x, 0 ≤ x → ‖f x‖ ≤ M := by
  simpa only [iteratedDerivWithin_zero] using
    (isBoundedHalfLineJet_iteratedDerivWithin f.property.1 f.property.2).bounded 0

theorem contDiff_seeleyExtend_of_contDiffOn {ι : Type*} (S : SeeleyData ι)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (hL₂ : ∀ n : ℕ, MemLp (iteratedDerivWithin n f (Ici 0)) 2
      (volume.restrict (Ici 0))) : ContDiff ℝ ∞ (seeleyExtend S f) := by
  simpa only [iteratedDerivWithin_zero] using
    contDiff_seeleyExtend S (isBoundedHalfLineJet_iteratedDerivWithin hf hL₂)

theorem iteratedDeriv_seeleyExtend_of_contDiffOn {ι : Type*} (S : SeeleyData ι)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (hL₂ : ∀ n : ℕ, MemLp (iteratedDerivWithin n f (Ici 0)) 2
      (volume.restrict (Ici 0))) (n : ℕ) :
    iteratedDeriv n (seeleyExtend S f) =
      seeleyExtensionJet S (fun k => iteratedDerivWithin k f (Ici 0)) n := by
  simpa only [iteratedDerivWithin_zero] using
    iteratedDeriv_seeleyExtend S (isBoundedHalfLineJet_iteratedDerivWithin hf hL₂) n

/-- The extension depends only on the function on the half-line. -/
theorem seeleyExtend_congr {ι : Type*} (S : SeeleyData ι) {f g : ℝ → F}
    (hfg : EqOn f g (Ici 0)) : seeleyExtend S f = seeleyExtend S g := by
  funext x
  by_cases hx : 0 ≤ x
  · simp only [seeleyExtend, if_pos hx, hfg hx]
  · simp only [seeleyExtend, if_neg hx, seeleyReflection]
    apply tsum_congr
    intro i
    rw [hfg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (S.b_nonneg i))
      (le_of_not_ge hx))]

theorem seeleyExtend_add {ι : Type*} (S : SeeleyData ι) {f g : ℝ → F}
    (hf : ∃ M : ℝ, ∀ x, 0 ≤ x → ‖f x‖ ≤ M)
    (hg : ∃ M : ℝ, ∀ x, 0 ≤ x → ‖g x‖ ≤ M) :
    seeleyExtend S (f + g) = seeleyExtend S f + seeleyExtend S g := by
  funext x
  by_cases hx : 0 ≤ x
  · simp only [seeleyExtend, if_pos hx, Pi.add_apply]
  · simp only [seeleyExtend, if_neg hx, Pi.add_apply, seeleyReflection, smul_add]
    exact (summable_seeleyReflection S 0 hf (le_of_not_ge hx)).tsum_add
      (summable_seeleyReflection S 0 hg (le_of_not_ge hx))

theorem seeleyExtend_smul {ι : Type*} (S : SeeleyData ι) (c : ℝ) (f : ℝ → F) :
    seeleyExtend S (c • f) = c • seeleyExtend S f := by
  funext x
  by_cases hx : 0 ≤ x
  · simp only [seeleyExtend, if_pos hx, Pi.smul_apply]
  · simp only [seeleyExtend, if_neg hx, Pi.smul_apply, seeleyReflection]
    calc
      (∑' i, (S.a i * (-S.b i) ^ 0) • (c • f (-S.b i * x))) =
          ∑' i, c • ((S.a i * (-S.b i) ^ 0) • f (-S.b i * x)) :=
        tsum_congr fun i => smul_comm _ _ _
      _ = _ := tsum_const_smul'' c

/-- One linear map on the smooth half-line core. Its definition contains
no Sobolev index. -/
def seeleyExtendLinear {ι : Type*} (S : SeeleyData ι) :
    HalfLineSobolevCore F →ₗ[ℝ] (ℝ → F) where
  toFun f := seeleyExtend S f
  map_add' f g := by
    simpa only [Submodule.coe_add] using seeleyExtend_add S (HalfLineSobolevCore.bounded f)
      (HalfLineSobolevCore.bounded g)
  map_smul' c f := by
    simpa only [Submodule.coe_smul, RingHom.id_apply] using seeleyExtend_smul S c (f : ℝ → F)

@[simp] theorem seeleyExtendLinear_apply {ι : Type*} (S : SeeleyData ι)
    (f : HalfLineSobolevCore F) (x : ℝ) : seeleyExtendLinear S f x = seeleyExtend S f x := rfl

theorem seeleyExtendLinear_contDiff {ι : Type*} (S : SeeleyData ι)
    (f : HalfLineSobolevCore F) : ContDiff ℝ ∞ (seeleyExtendLinear S f) :=
  contDiff_seeleyExtend_of_contDiffOn S f.property.1 f.property.2

theorem seeleyExtendLinear_rightInverse {ι : Type*} (S : SeeleyData ι)
    (f : HalfLineSobolevCore F) {x : ℝ} (hx : 0 ≤ x) : seeleyExtendLinear S f x = f x :=
  seeleyExtend_of_nonneg S f hx

end ContinuousFlexibility.Analysis
