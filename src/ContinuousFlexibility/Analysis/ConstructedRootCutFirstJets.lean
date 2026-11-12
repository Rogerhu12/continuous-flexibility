import ContinuousFlexibility.Analysis.N04bConstructedRootTransmission
import ContinuousFlexibility.Analysis.N04bRootInteriorRegularity
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Forward first jets at the genuine middle travel cut

The two root charts are evaluated at one actual middle-travel point.
Their signed radial derivatives agree after reversal. The height jump
follows by differentiating the exact identity h²(a v) = sqrt(ξ), so no
trace of an unconstrained inverse or transmission identity is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem n04Coordinates_rootHeight_square_density
    {b ξ : ℝ} (hb : 0 < b) (hξ : 0 < ξ) :
    ((Real.sqrt (b / Real.sqrt ξ))⁻¹) ^ 2 * b = Real.sqrt ξ := by
  have hs := Real.sqrt_pos.2 hξ
  rw [inv_pow, Real.sq_sqrt (div_pos hb hs).le]
  field_simp [hb.ne', hs.ne']

private theorem n04Coordinates_height_cut_first_derivative
    {B u v f g : PolarPoint → ℝ} {x : PolarPoint} {ρ : ℝ}
    (hB : DifferentiableAt ℝ B x)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hρ : 0 < ρ) (hBp : 0 < B x) (hup : 0 < u x)
    (hvalue : v x = u x) (hfx : f x = ρ) (hgx : g x = ρ)
    (hdf : fderiv ℝ g x = -(fderiv ℝ f x))
    (heqf : (fun y => u y ^ 2 * B y) =ᶠ[𝓝 x] (fun y => Real.sqrt (f y)))
    (heqg : (fun y => v y ^ 2 * B y) =ᶠ[𝓝 x] (fun y => Real.sqrt (g y))) :
    fderiv ℝ v x - fderiv ℝ u x =
      (-(u x / (2 * ρ))) • fderiv ℝ f x := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hnorm : u x ^ 2 * B x = Real.sqrt ρ := by
    simpa only [hfx] using heqf.self_of_nhds
  have hdfx : f x ≠ 0 := by rw [hfx]; exact hρ.ne'
  have hdgx : g x ≠ 0 := by rw [hgx]; exact hρ.ne'
  have hdleft := ((hu.hasFDerivAt.pow 2).fun_mul hB.hasFDerivAt).fderiv.symm.trans
    (heqf.fderiv_eq.trans (hf.hasFDerivAt.sqrt hdfx).fderiv)
  have hdright := ((hv.hasFDerivAt.pow 2).fun_mul hB.hasFDerivAt).fderiv.symm.trans
    (heqg.fderiv_eq.trans (hg.hasFDerivAt.sqrt hdgx).fderiv)
  apply ContinuousLinearMap.ext
  intro q
  have hl := DFunLike.congr_fun hdleft q
  have hr := DFunLike.congr_fun hdright q
  norm_num only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    nsmul_eq_mul, smul_eq_mul, hfx, hgx, hvalue, hdf,
    ContinuousLinearMap.neg_apply, Nat.reduceSub, pow_one] at hl hr
  have hdifference : (2 * u x * B x) *
      (fderiv ℝ v x q - fderiv ℝ u x q) =
        -(2 * (1 / (2 * Real.sqrt ρ))) * fderiv ℝ f x q := by
    nlinarith [hl, hr]
  have hcoefficient : (2 * u x * B x) * (-(u x / (2 * ρ))) =
      -(1 / Real.sqrt ρ) := by
    calc
      _ = -(u x ^ 2 * B x / ρ) := by field_simp [hρ.ne'] <;> ring
      _ = -(Real.sqrt ρ / ρ) := by rw [hnorm]
      _ = -(1 / Real.sqrt ρ) := by
        field_simp [hρ.ne', hs.ne'] <;> nlinarith [Real.sq_sqrt hρ.le]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ (show 2 * u x * B x ≠ 0 by positivity)
  calc
    (2 * u x * B x) * (fderiv ℝ v x q - fderiv ℝ u x q) =
        -(2 * (1 / (2 * Real.sqrt ρ))) * fderiv ℝ f x q := hdifference
    _ = -(1 / Real.sqrt ρ) * fderiv ℝ f x q := by
      field_simp [hs.ne']
    _ = (2 * u x * B x) * (-(u x / (2 * ρ)) * fderiv ℝ f x q) := by
      rw [← mul_assoc, hcoefficient]

theorem n04Coordinates_constructedRoot_cut_firstJets
    (A : SymmetricCoefficients) (v : PolarPoint → ℝ)
    (F : PolarPoint → PolarPoint) {T : ℝ} (hT : 0 < T)
    {x : PolarPoint} {θ : ℝ} (hpoint : F x = (T / 2, θ))
    (hF : ContDiffAt ℝ ∞ F x)
    (hB : ContDiffAt ℝ ∞ (fun y => A.a y * v y) x)
    (hBp : 0 < A.a x * v x) :
    let ρ := n04bRootCutRadius T
    let Fl := fun y : PolarPoint =>
      ((n04bRootPhysicalChart F T false y).1 - ρ,
        (n04bRootPhysicalChart F T false y).2)
    let Fr := fun y : PolarPoint =>
      (-((n04bRootPhysicalChart F T true y).1 - ρ),
        (n04bRootPhysicalChart F T true y).2)
    Fl x = (0, θ) ∧ Fr x = Fl x ∧
      fderiv ℝ Fl x = fderiv ℝ Fr x ∧
      n04bRootPhysicalHeight A v F T false x = n04bRootPhysicalHeight A v F T true x ∧
      fderiv ℝ (n04bRootPhysicalHeight A v F T true) x -
        fderiv ℝ (n04bRootPhysicalHeight A v F T false) x =
          (-(n04bRootPhysicalHeight A v F T false x / (2 * ρ))) •
            fderiv ℝ (fun y => (n04bRootPhysicalChart F T false y).1) x := by
  let ρ := n04bRootCutRadius T
  let X := n04bRootPhysicalChart F T
  let H := n04bRootPhysicalHeight A v F T
  have hρ : 0 < ρ := n04bRootCutRadius_pos hT
  have hX (side : Bool) : X side x = (ρ, θ) := by
    change n04bRootStripChart T side (F x) = (ρ, θ)
    rw [hpoint, n04b_rootStripChart_cut]
  have hXraw (side : Bool) : n04bRootPhysicalChart F T side x = (ρ, θ) := hX side
  have horient (side : Bool) : 0 < n04bTravelOrientation T side (F x).1 := by
    rw [hpoint, n04bTravelOrientation_middle]
    exact half_pos hT
  have hXs (side : Bool) : ContDiffAt ℝ ∞ (X side) x :=
    n04b_contDiffAt_rootPhysicalChart hF (horient side)
  have hξ (side : Bool) : 0 < (X side x).1 := by rw [hX]; exact hρ
  have hHs (side : Bool) : ContDiffAt ℝ ∞ (H side) x := by
    have hs := (hXs side).fst.sqrt (hξ side).ne'
    have hq : ContDiffAt ℝ ∞
        (fun y => A.a y * v y / Real.sqrt (X side y).1) x :=
      hB.fun_div hs (Real.sqrt_pos.2 (hξ side)).ne'
    have hqp : 0 < A.a x * v x / Real.sqrt (X side x).1 :=
      div_pos hBp (Real.sqrt_pos.2 (hξ side))
    exact (hq.sqrt hqp.ne').inv (Real.sqrt_pos.2 hqp).ne'
  have hHvalue : H true x = H false x := by
    simp only [H, n04bRootPhysicalHeight, hXraw]
  have hHpos : 0 < H false x :=
    inv_pos.mpr (Real.sqrt_pos.2 (div_pos hBp (Real.sqrt_pos.2 (hξ false))))
  have hDX (side : Bool) (q : PolarPoint) :
      fderiv ℝ (X side) x q =
        (((if side then (-1 : ℝ) else 1) / Real.sqrt ρ) * (fderiv ℝ F x q).1,
          (fderiv ℝ F x q).2) := by
    change fderiv ℝ (n04bRootPhysicalChart F T side) x q = _
    rw [n04b_fderiv_rootPhysicalChart_apply (hF.differentiableAt (by simp)) (horient side)]
    simp only [n04bRootDifferentialScale, hXraw]
  have hDf (side : Bool) (q : PolarPoint) :
      fderiv ℝ (fun y => (X side y).1) x q =
        ((if side then (-1 : ℝ) else 1) / Real.sqrt ρ) * (fderiv ℝ F x q).1 := by
    rw [((hXs side).differentiableAt (by simp)).hasFDerivAt.fst.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', hDX]
  have hDneg : fderiv ℝ (fun y => (X true y).1) x =
      -(fderiv ℝ (fun y => (X false y).1) x) := by
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearMap.neg_apply, hDf,
      Bool.false_eq_true, ite_false, ite_true, neg_div, neg_mul]
  have hnormal (side : Bool) :
      (fun y => H side y ^ 2 * (A.a y * v y)) =ᶠ[𝓝 x]
        (fun y => Real.sqrt (X side y).1) := by
    have hb : ∀ᶠ y in 𝓝 x, 0 < A.a y * v y :=
      hB.continuousAt.eventually (isOpen_Ioi.mem_nhds hBp)
    have hx : ∀ᶠ y in 𝓝 x, 0 < (X side y).1 :=
      (hXs side).fst.continuousAt.eventually (isOpen_Ioi.mem_nhds (hξ side))
    filter_upwards [hb, hx] with y hb hx
    exact n04Coordinates_rootHeight_square_density hb hx
  have hHl := (hXs false).differentiableAt (by simp)
  have hHr := (hXs true).differentiableAt (by simp)
  have hFl := (hHl.hasFDerivAt.fst.sub_const ρ).prodMk hHl.hasFDerivAt.snd
  have hFr := (hHr.hasFDerivAt.fst.sub_const ρ).neg.prodMk hHr.hasFDerivAt.snd
  simp only [Pi.neg_apply] at hFr
  refine ⟨?_, ?_, ?_, hHvalue.symm, ?_⟩
  · change ((X false x).1 - ρ, (X false x).2) = (0, θ)
    simp only [hX, sub_self]
  · change (-((X true x).1 - ρ), (X true x).2) = ((X false x).1 - ρ, (X false x).2)
    simp only [hX, sub_self, neg_zero]
  · change fderiv ℝ (fun y => ((X false y).1 - ρ, (X false y).2)) x =
      fderiv ℝ (fun y => (-((X true y).1 - ρ), (X true y).2)) x
    rw [hFl.fderiv, hFr.fderiv]
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.neg_apply, hDX,
      Bool.false_eq_true, ite_false, ite_true, neg_div, neg_mul, neg_neg]
  · exact n04Coordinates_height_cut_first_derivative
      (hB.differentiableAt (by simp))
      ((hHs false).differentiableAt (by simp)) ((hHs true).differentiableAt (by simp))
      hHl.fst hHr.fst hρ hBp hHpos hHvalue
      (congrArg Prod.fst (hX false)) (congrArg Prod.fst (hX true)) hDneg
      (hnormal false) (hnormal true)

end ContinuousFlexibility.Analysis
