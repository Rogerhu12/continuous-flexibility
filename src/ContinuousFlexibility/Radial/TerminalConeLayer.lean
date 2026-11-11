import ContinuousFlexibility.Radial.TerminalConeEnergy
import ContinuousFlexibility.Radial.SelectedGrowingCone

/-!
# Placing a fixed-ratio layer deep in the actual retained cone

One Boolean handles the two orientations. The layer is strictly between
the retained inner endpoint and the old cut. The normalized growing
power is exponentially small there, with no change to its old join jet.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory Filter
open scoped ContDiff Topology ENNReal

def terminalConeLayerLeft (right : Bool) (c H : ℝ) : ℝ :=
  if right then c * exp (-H) else c * exp H / 2

theorem terminalConeLayerLeft_pos (right : Bool) {c : ℝ} (hc : 0 < c) (H : ℝ) :
    0 < terminalConeLayerLeft right c H := by
  cases right <;> simp only [terminalConeLayerLeft, Bool.false_eq_true, ite_false, ite_true] <;>
    positivity

theorem terminalConeLayerLeft_log (right : Bool) {c : ℝ} (hc : 0 < c) (H : ℝ) :
    log (terminalConeLayerLeft right c H) =
      if right then log c - H else log c + H - log 2 := by
  cases right
  · change log (c * exp H / 2) = log c + H - log 2
    rw [log_div (mul_ne_zero hc.ne' (exp_ne_zero _)) (by norm_num : (2 : ℝ) ≠ 0),
      log_mul hc.ne' (exp_ne_zero _), log_exp]
  · change log (c * exp (-H)) = log c - H
    rw [log_mul hc.ne' (exp_ne_zero _), log_exp]
    ring

/-- The actual logarithmic cone length places the whole layer strictly
inside the retained cone, on the inward side of the unchanged old cut. -/
theorem terminalConeLayer_inside (right : Bool) {c inner length H : ℝ}
    (hc : 0 < c) (hi : 0 < inner) (hH : log 2 < H) (hL : H < length)
    (hlen : if right then length ≤ log (c / inner) else length ≤ log (inner / c)) :
    let a := terminalConeLayerLeft right c H
    if right then inner < a ∧ 2 * a < c else c < a ∧ 2 * a < inner := by
  have ha := terminalConeLayerLeft_pos right hc H
  have htwo : 0 < 2 * terminalConeLayerLeft right c H := mul_pos (by norm_num) ha
  have hla := terminalConeLayerLeft_log right hc H
  have hlb : log (2 * terminalConeLayerLeft right c H) =
      log 2 + log (terminalConeLayerLeft right c H) :=
    log_mul (by norm_num) ha.ne'
  cases right
  · change length ≤ log (inner / c) at hlen
    change log (terminalConeLayerLeft false c H) = log c + H - log 2 at hla
    change c < terminalConeLayerLeft false c H ∧
      2 * terminalConeLayerLeft false c H < inner
    rw [log_div hi.ne' hc.ne'] at hlen
    constructor
    · apply (log_lt_log_iff hc ha).mp
      rw [hla]
      linarith only [hH]
    · apply (log_lt_log_iff htwo hi).mp
      rw [hlb, hla]
      linarith only [hlen, hL]
  · change length ≤ log (c / inner) at hlen
    change log (terminalConeLayerLeft true c H) = log c - H at hla
    change inner < terminalConeLayerLeft true c H ∧
      2 * terminalConeLayerLeft true c H < c
    rw [log_div hc.ne' hi.ne'] at hlen
    constructor
    · apply (log_lt_log_iff hi ha).mp
      rw [hla]
      linarith only [hlen, hL]
    · apply (log_lt_log_iff htwo hc).mp
      rw [hlb, hla]
      linarith only [hH]

/-- The power estimate follows from the actual positions of the old cut
and join; no residual or energy bound is an input. -/
theorem terminalConeLayer_power_bound (right : Bool) {c p H j r : ℝ}
    (hc : 0 < c) (hp : 0 < p) (hj : 0 ≤ j) (hH : 2 * log 2 ≤ H)
    (hcp : if right then c ≤ p else p ≤ c)
    (hr : r ∈ Icc (terminalConeLayerLeft right c H) (2 * terminalConeLayerLeft right c H)) :
    |r ^ (if right then j else -j) / p ^ (if right then j else -j)| ≤ exp (-(j * H / 2)) := by
  have ha := terminalConeLayerLeft_pos right hc H
  have hrpos : 0 < r := ha.trans_le hr.1
  have hla := terminalConeLayerLeft_log right hc H
  cases right
  · change p ≤ c at hcp
    change log (terminalConeLayerLeft false c H) = log c + H - log 2 at hla
    have hlogr := log_le_log ha hr.1
    have hlogp := log_le_log hp hcp
    rw [hla] at hlogr
    have hlog : log p - log r ≤ -H / 2 := by linarith only [hlogr, hlogp, hH]
    change |r ^ (-j) / p ^ (-j)| ≤ exp (-(j * H / 2))
    rw [abs_of_pos (div_pos (rpow_pos_of_pos hrpos _) (rpow_pos_of_pos hp _)),
      rpow_def_of_pos hrpos, rpow_def_of_pos hp, ← exp_sub]
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hlog hj
    nlinarith only [hm]
  · change c ≤ p at hcp
    change log (terminalConeLayerLeft true c H) = log c - H at hla
    have hlogr := log_le_log hrpos hr.2
    have hlogp := log_le_log hc hcp
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne', hla] at hlogr
    have hlog : log r - log p ≤ -H / 2 := by linarith only [hlogr, hlogp, hH]
    change |r ^ j / p ^ j| ≤ exp (-(j * H / 2))
    rw [abs_of_pos (div_pos (rpow_pos_of_pos hrpos _) (rpow_pos_of_pos hp _)),
      rpow_def_of_pos hrpos, rpow_def_of_pos hp, ← exp_sub]
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hlog hj
    nlinarith only [hm]

/-- Restricting the actual normalized growing stand-in gives both jets
needed by the source estimate on the chosen physical layer. -/
theorem terminalConeLayer_actual_jets (right : Bool) {c p inner length H j : ℝ}
    {u : ℝ → ℝ} (hc : 0 < c) (hp : 0 < p) (hi : 0 < inner)
    (hj : 0 ≤ j) (hH : 2 * log 2 ≤ H) (hH' : log 2 < H) (hL : H < length)
    (hlen : if right then length ≤ log (c / inner) else length ≤ log (inner / c))
    (hcp : if right then c ≤ p else p ≤ c)
    (hu : ContDiff ℝ ∞ u)
    (hpower : EqOn u (fun r => r ^ (if right then j else -j) /
      p ^ (if right then j else -j)) (uIcc inner p)) :
    let a := terminalConeLayerLeft right c H
    ∀ r ∈ Icc a (2 * a),
      deriv u r = (if right then j else -j) / r * u r ∧
        |u r| ≤ exp (-(j * H / 2)) := by
  let a := terminalConeLayerLeft right c H
  have ha0 : 0 < a := terminalConeLayerLeft_pos right hc H
  have hinside := terminalConeLayer_inside right hc hi hH' hL hlen
  have hsub : Icc a (2 * a) ⊆ uIcc inner p := by
    cases right
    · change c < a ∧ 2 * a < inner at hinside
      change p ≤ c at hcp
      have hpi : p < inner := by linarith only [hinside.1, hinside.2, hcp, ha0]
      rw [uIcc_of_ge hpi.le]
      intro r hr
      exact ⟨hcp.trans (hinside.1.le.trans hr.1), hr.2.trans hinside.2.le⟩
    · change inner < a ∧ 2 * a < c at hinside
      change c ≤ p at hcp
      have hip : inner < p := by linarith only [hinside.1, hinside.2, hcp, ha0]
      rw [uIcc_of_le hip.le]
      intro r hr
      exact ⟨hinside.1.le.trans hr.1, hr.2.trans (hinside.2.le.trans hcp)⟩
  have hne : inner ≠ p := by
    cases right
    · change c < a ∧ 2 * a < inner at hinside
      change p ≤ c at hcp
      intro he
      rw [he] at hinside
      linarith only [hinside.1, hinside.2, hcp, ha0]
    · change inner < a ∧ 2 * a < c at hinside
      change c ≤ p at hcp
      intro he
      rw [he] at hinside
      linarith only [hinside.1, hinside.2, hcp, ha0]
  change ∀ r ∈ Icc a (2 * a),
    deriv u r = (if right then j else -j) / r * u r ∧
      |u r| ≤ exp (-(j * H / 2))
  intro r hr
  refine ⟨radialConePower_deriv_of_eqOn hi hp hne hu hpower (hsub hr), ?_⟩
  rw [hpower (hsub hr)]
  exact terminalConeLayer_power_bound right hc hp hj hH hcp hr

/-- The actual cone profile and normalized stand-in construct the
attenuated Hilbert source on the original radial measure. -/
theorem terminalConeLayer_actual_source_L2 (D : Statements.ReferenceData) (right : Bool)
    {c p inner length H scale j : ℝ} {u : ℝ → ℝ}
    (hc : 0 < c) (hp : 0 < p) (hi : 0 < inner) (hs : 0 < scale) (hj : 1 ≤ j)
    (hH : 2 * log 2 ≤ H) (hH' : log 2 < H) (hL : H < length)
    (hlen : if right then length ≤ log (c / inner) else length ≤ log (inner / c))
    (hcp : if right then c ≤ p else p ≤ c)
    (hw : ContDiff ℝ ∞ D.w) (hu : ContDiff ℝ ∞ u)
    (hcone : ∀ r ∈ Icc (terminalConeLayerLeft right c H) (2 * terminalConeLayerLeft right c H),
      D.w =ᶠ[𝓝 r] (fun t => scale * t))
    (hpower : EqOn u (fun r => r ^ (if right then j else -j) /
      p ^ (if right then j else -j)) (uIcc inner p)) :
    let a := terminalConeLayerLeft right c H
    let f := terminalCapHilbertSource (j ^ 2 * scale) D.w
      (terminalPhysicalCutoff right a (2 * a)) u
    MemLp f 2 (Statements.radialHilbertMeasure D) ∧
      eLpNorm f 2 (Statements.radialHilbertMeasure D) ≤
        ENNReal.ofReal (terminalConeSourceConstant * exp (-(j * H / 2))) := by
  have hj0 : 0 ≤ j := le_trans (by norm_num) hj
  have hν : |(if right then j else -j)| ≤ j := by
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true, abs_neg,
      abs_of_nonneg hj0, le_refl]
  have hjet := terminalConeLayer_actual_jets right hc hp hi hj0 hH hH' hL hlen hcp hu hpower
  exact terminalCone_source_L2 D right (terminalConeLayerLeft_pos right hc H) hs hj hν hw hu
    hcone (fun r hr => (hjet r hr).1) (fun r hr => (hjet r hr).2)

/-- The same actual stand-in yields the relative energy error, with
two copies of its attenuation factor and the same d=1/j. -/
theorem terminalConeLayer_actual_energy (right : Bool)
    {c p inner length H scale j lo hi : ℝ} {w u : ℝ → ℝ}
    (hc : 0 < c) (hp : 0 < p) (hinner : 0 < inner) (hs : 0 < scale) (hj : 1 ≤ j)
    (hH : 2 * log 2 ≤ H) (hH' : log 2 < H) (hL : H < length)
    (hlen : if right then length ≤ log (c / inner) else length ≤ log (inner / c))
    (hcp : if right then c ≤ p else p ≤ c)
    (hlo : lo ≤ terminalConeLayerLeft right c H) (hhi : 2 * terminalConeLayerLeft right c H ≤ hi)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hcone : ∀ r ∈ Icc (terminalConeLayerLeft right c H) (2 * terminalConeLayerLeft right c H),
      w r = scale * r)
    (hpower : EqOn u (fun r => r ^ (if right then j else -j) /
      p ^ (if right then j else -j)) (uIcc inner p)) :
    let a := terminalConeLayerLeft right c H
    (∫ r in lo..hi, terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u r) /
        (j ^ 2 * scale) ≤
      (1 / j) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-(j * H)) := by
  have hjet := terminalConeLayer_actual_jets right hc hp hinner
    (le_trans (by norm_num) hj) hH hH' hL hlen hcp hu hpower
  have h := terminalCone_cutoffEnergy_relative right (terminalConeLayerLeft_pos right hc H)
    hs hj hlo hhi hw hu hcone (fun r hr => (hjet r hr).2)
  simpa only [show -2 * (j * H / 2) = -(j * H) by ring] using h

end ContinuousFlexibility.Radial
