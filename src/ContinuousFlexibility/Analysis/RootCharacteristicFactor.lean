import ContinuousFlexibility.Scalar.S05CalculusProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual factored characteristic field at a simple root

The radial factor uses the reference profile and its genuine smooth divided
derivative. The remaining factors are the actual discriminant and height Q.
The numerical bounds below come from the N01 intervals for Q/w and D.
This module does not assert a common root germ for a corrected N03 operator.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootProfileShift (r σ : ℝ) (p : PolarPoint) : PolarPoint :=
  (r + σ * p.1, p.2)

def rootProfileRadicand (w g : ℝ → ℝ) (r σ t : ℝ) : ℝ :=
  w (r + σ * t) * g t / (r + σ * t)

def referenceRootSpeedFactor (w g : ℝ → ℝ) (r σ t : ℝ) : ℝ :=
  Real.sqrt (rootProfileRadicand w g r σ t) / w (r + σ * t)

def factoredCharacteristicSpeed (wref g w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (r σ : ℝ) (p : PolarPoint) : ℝ :=
  Real.sqrt (rootProfileRadicand wref g r σ p.1) *
    Real.sqrt (polarDiscriminant w z (rootProfileShift r σ p)) /
      heightQ (profileEnergy w (rootProfileShift r σ p))
        (heightRadial z (rootProfileShift r σ p))
        (angularPartial (heightAngular z) (rootProfileShift r σ p))

def orientedCharacteristicDrift (w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (r σ : ℝ) (p : PolarPoint) : ℝ :=
  σ * characteristicDrift w z (rootProfileShift r σ p)

theorem rootProfileRadicand_pos
    {w g : ℝ → ℝ} {r σ t : ℝ}
    (hr : 0 < r + σ * t) (hw : 0 < w (r + σ * t)) (hg : 0 < g t) :
    0 < rootProfileRadicand w g r σ t :=
  div_pos (mul_pos hw hg) hr

theorem contDiffAt_rootProfileRadicand
    {w g : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    {r σ t : ℝ} (hr : r + σ * t ≠ 0) :
    ContDiffAt ℝ ∞ (rootProfileRadicand w g r σ) t := by
  have hρ : ContDiff ℝ ∞ (fun s : ℝ => r + σ * s) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  exact (((hw.comp hρ).contDiffAt).mul hg.contDiffAt).div hρ.contDiffAt hr

theorem contDiffAt_referenceRootSpeedFactor
    {w g : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    {r σ t : ℝ} (hr : 0 < r + σ * t)
    (hwpos : 0 < w (r + σ * t)) (hgpos : 0 < g t) :
    ContDiffAt ℝ ∞ (referenceRootSpeedFactor w g r σ) t := by
  have hρ : ContDiff ℝ ∞ (fun s : ℝ => r + σ * s) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  exact ((contDiffAt_rootProfileRadicand hw hg hr.ne').sqrt
    (rootProfileRadicand_pos hr hwpos hgpos).ne').div
      (hw.comp hρ).contDiffAt hwpos.ne'

theorem referenceRootSpeedFactor_pos
    {w g : ℝ → ℝ} {r σ t : ℝ}
    (hr : 0 < r + σ * t) (hw : 0 < w (r + σ * t)) (hg : 0 < g t) :
    0 < referenceRootSpeedFactor w g r σ t :=
  div_pos (Real.sqrt_pos.mpr (rootProfileRadicand_pos hr hw hg)) hw

/-- Both fields are genuinely smooth at every point where the displayed
actual denominators and reference radial factors are positive. -/
theorem contDiffAt_factoredCharacteristicField
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r σ : ℝ} {p : PolarPoint}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hwpos : 0 < wref (rootProfileShift r σ p).1) (hgpos : 0 < g p.1)
    (hD : 0 < polarDiscriminant w z (rootProfileShift r σ p))
    (hQ : 0 < heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p))) :
    ContDiffAt ℝ ∞ (factoredCharacteristicSpeed wref g w z r σ) p ∧
      ContDiffAt ℝ ∞ (orientedCharacteristicDrift w z r σ) p := by
  let y := rootProfileShift r σ p
  let Q : PolarPoint → ℝ := fun q =>
    heightQ (profileEnergy w q) (heightRadial z q) (angularPartial (heightAngular z) q)
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) y :=
    contDiffAt_const.add ((hw.contDiffAt.comp y contDiffAt_fst).pow 2)
  have hk := contDiffAt_heightRadial (x := y) hz.contDiffAt (m := ∞) (by simp)
  have hp := contDiffAt_heightAngular (x := y) hz.contDiffAt (m := ∞) (by simp) hr.ne'
  have hpt := contDiffAt_angularPartial hp (m := ∞) (by simp)
  have hkt := contDiffAt_angularPartial hk (m := ∞) (by simp)
  have hdisc : ContDiffAt ℝ ∞ (polarDiscriminant w z) y :=
    (hE.mul (contDiffAt_const.sub (hp.pow 2))).sub (hk.pow 2)
  have hq : ContDiffAt ℝ ∞ Q y := hk.add (hE.mul hpt)
  have hA : ContDiffAt ℝ ∞ (fun q : PolarPoint => rootProfileRadicand wref g r σ q.1) p :=
    (contDiffAt_rootProfileRadicand hwref hg hr.ne').comp p contDiffAt_fst
  have hApos : 0 < rootProfileRadicand wref g r σ p.1 :=
    rootProfileRadicand_pos hr hwpos hgpos
  have hDs : ContDiffAt ℝ ∞ (fun q => polarDiscriminant w z (rootProfileShift r σ q)) p := by
    simpa only [Function.comp_def] using hdisc.comp p hshift.contDiffAt
  have hQs : ContDiffAt ℝ ∞ (fun q => Q (rootProfileShift r σ q)) p := by
    simpa only [Function.comp_def] using hq.comp p hshift.contDiffAt
  have hd : ContDiffAt ℝ ∞ (characteristicDrift w z) y :=
    (hE.mul (hp.sub hkt)).div (contDiffAt_fst.mul hq) (mul_ne_zero hr.ne' hQ.ne')
  constructor
  · exact ((hA.sqrt hApos.ne').mul (hDs.sqrt hD.ne')).div hQs hQ.ne'
  · have hds : ContDiffAt ℝ ∞
        (fun q => characteristicDrift w z (rootProfileShift r σ q)) p := by
      simpa only [Function.comp_def] using hd.comp p hshift.contDiffAt
    exact contDiffAt_const.mul hds

theorem factoredCharacteristicSpeed_pos
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ} {r σ : ℝ} {p : PolarPoint}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hw : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hD : 0 < polarDiscriminant w z (rootProfileShift r σ p))
    (hQ : 0 < heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p))) :
    0 < factoredCharacteristicSpeed wref g w z r σ p :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (rootProfileRadicand_pos hr hw hg))
    (Real.sqrt_pos.mpr hD)) hQ

/-- The actual physical speed factors after the actual profile and its
first derivative have been identified on the common radial collar. -/
theorem characteristicSpeed_eq_sqrt_mul_factored
    {wref g w : ℝ → ℝ} (z : PolarPoint → ℝ) {r σ : ℝ} {p : PolarPoint}
    (hx : 0 ≤ p.1)
    (hw : w (rootProfileShift r σ p).1 = wref (rootProfileShift r σ p).1)
    (hdivide : -deriv w (rootProfileShift r σ p).1 = p.1 * g p.1) :
    characteristicSpeed w z (rootProfileShift r σ p) =
      Real.sqrt p.1 * factoredCharacteristicSpeed wref g w z r σ p := by
  have hrad :
      -w (rootProfileShift r σ p).1 * deriv w (rootProfileShift r σ p).1 /
          (rootProfileShift r σ p).1 =
        p.1 * rootProfileRadicand wref g r σ p.1 := by
    calc
      _ = w (rootProfileShift r σ p).1 * (-deriv w (rootProfileShift r σ p).1) /
          (rootProfileShift r σ p).1 := by ring
      _ = _ := by rw [hw, hdivide]; unfold rootProfileRadicand rootProfileShift; ring
  simp only [characteristicSpeed, hrad, Real.sqrt_mul hx,
    factoredCharacteristicSpeed]
  ring

private theorem root_normalized_discriminant_ratio_bounds
    {w Q D : ℝ} (hw : 0 < w)
    (hQl : (7 / 8 : ℝ) ≤ Q / w) (hQu : Q / w ≤ (9 / 8 : ℝ))
    (hDl : (1 / 2 : ℝ) ≤ D) (hDu : D ≤ (3 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ w * Real.sqrt D / Q ∧ w * Real.sqrt D / Q ≤ 2 := by
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hDl
  have hs := Real.sq_sqrt hD0
  have hsn := Real.sqrt_nonneg D
  have hsl : (9 / 16 : ℝ) ≤ Real.sqrt D := by nlinarith only [hs, hDl, hsn]
  have hsu : Real.sqrt D ≤ (7 / 4 : ℝ) := by nlinarith only [hs, hDu, hsn]
  have hQl' : (7 / 8 : ℝ) * w ≤ Q := (le_div_iff₀ hw).mp hQl
  have hQu' : Q ≤ (9 / 8 : ℝ) * w := (div_le_iff₀ hw).mp hQu
  have hQpos : 0 < Q := (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hw).trans_le hQl'
  constructor
  · apply (le_div_iff₀ hQpos).mpr
    have hm := mul_le_mul_of_nonneg_left hsl hw.le
    nlinarith only [hm, hQu']
  · apply (div_le_iff₀ hQpos).mpr
    have hm := mul_le_mul_of_nonneg_left hsu hw.le
    nlinarith only [hm, hQl']

/-- The fixed N01 intervals yield an explicit state-independent relative
bound, without assuming a bound for the factored speed itself. -/
theorem factoredCharacteristicSpeed_reference_bounds
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ} {r σ : ℝ} {p : PolarPoint}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hw : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hQl : (7 / 8 : ℝ) ≤
      heightQ (profileEnergy w (rootProfileShift r σ p))
        (heightRadial z (rootProfileShift r σ p))
        (angularPartial (heightAngular z) (rootProfileShift r σ p)) /
          wref (rootProfileShift r σ p).1)
    (hQu :
      heightQ (profileEnergy w (rootProfileShift r σ p))
        (heightRadial z (rootProfileShift r σ p))
        (angularPartial (heightAngular z) (rootProfileShift r σ p)) /
          wref (rootProfileShift r σ p).1 ≤ (9 / 8 : ℝ))
    (hDl : (1 / 2 : ℝ) ≤ polarDiscriminant w z (rootProfileShift r σ p))
    (hDu : polarDiscriminant w z (rootProfileShift r σ p) ≤ (3 / 2 : ℝ)) :
    referenceRootSpeedFactor wref g r σ p.1 / 2 ≤
        factoredCharacteristicSpeed wref g w z r σ p ∧
      factoredCharacteristicSpeed wref g w z r σ p ≤
        2 * referenceRootSpeedFactor wref g r σ p.1 := by
  let Q := heightQ (profileEnergy w (rootProfileShift r σ p))
    (heightRadial z (rootProfileShift r σ p))
    (angularPartial (heightAngular z) (rootProfileShift r σ p))
  let D := polarDiscriminant w z (rootProfileShift r σ p)
  have hbounds := root_normalized_discriminant_ratio_bounds hw hQl hQu hDl hDu
  have hc : 0 < referenceRootSpeedFactor wref g r σ p.1 :=
    referenceRootSpeedFactor_pos hr hw hg
  have hQpos : 0 < Q :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hw).trans_le ((le_div_iff₀ hw).mp hQl)
  have he : factoredCharacteristicSpeed wref g w z r σ p =
      referenceRootSpeedFactor wref g r σ p.1 *
        (wref (rootProfileShift r σ p).1 * Real.sqrt D / Q) := by
    change Real.sqrt (rootProfileRadicand wref g r σ p.1) * Real.sqrt D / Q =
      (Real.sqrt (rootProfileRadicand wref g r σ p.1) /
        wref (rootProfileShift r σ p).1) *
          (wref (rootProfileShift r σ p).1 * Real.sqrt D / Q)
    field_simp [hw.ne', hQpos.ne']
    <;> ring
  rw [he]
  constructor
  · calc
      referenceRootSpeedFactor wref g r σ p.1 / 2 =
          referenceRootSpeedFactor wref g r σ p.1 * (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbounds.1 hc.le
  · calc
      _ ≤ referenceRootSpeedFactor wref g r σ p.1 * 2 :=
        mul_le_mul_of_nonneg_left hbounds.2 hc.le
      _ = _ := mul_comm _ _

/-- Actual angular periodicity passes through the divided reference factor,
the actual height derivatives, and every totalized quotient. -/
theorem periodic_factoredCharacteristicField
    (wref g w : ℝ → ℝ) {z : PolarPoint → ℝ} {r σ T : ℝ}
    (hz : Function.Periodic z (0, T)) :
    Function.Periodic (factoredCharacteristicSpeed wref g w z r σ) (0, T) ∧
      Function.Periodic (orientedCharacteristicDrift w z r σ) (0, T) := by
  have hE : Function.Periodic (profileEnergy w) (0, T) := by
    intro q
    simp only [profileEnergy, Prod.fst_add, add_zero]
  have hk : Function.Periodic (heightRadial z) (0, T) := periodic_radialPartial hz
  have hp : Function.Periodic (heightAngular z) (0, T) := by
    intro q
    simp only [heightAngular, periodic_angularPartial hz q, Prod.fst_add, add_zero]
  have hpt := periodic_angularPartial hp
  have hkt := periodic_angularPartial hk
  have hD (q : PolarPoint) :
      polarDiscriminant w z (q + (0, T)) = polarDiscriminant w z q := by
    simp only [polarDiscriminant, hE q, hk q, hp q]
  have hQ (q : PolarPoint) :
      heightQ (profileEnergy w (q + (0, T))) (heightRadial z (q + (0, T)))
        (angularPartial (heightAngular z) (q + (0, T))) =
      heightQ (profileEnergy w q) (heightRadial z q)
        (angularPartial (heightAngular z) q) := by
    rw [hE q, hk q, hpt q]
  have hd : Function.Periodic (characteristicDrift w z) (0, T) := by
    intro q
    simp only [characteristicDrift, hE q, hp q, hkt q, hk q, hpt q,
      Prod.fst_add, add_zero]
  have hshift (q : PolarPoint) :
      rootProfileShift r σ (q + (0, T)) = rootProfileShift r σ q + (0, T) := by
    simp only [rootProfileShift, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, add_zero]
  constructor <;> intro q
  · simp only [factoredCharacteristicSpeed, Prod.fst_add, add_zero, hshift q,
      hD (rootProfileShift r σ q), hQ (rootProfileShift r σ q)]
  · simp only [orientedCharacteristicDrift, hshift q, hd (rootProfileShift r σ q)]

end ContinuousFlexibility.Analysis
