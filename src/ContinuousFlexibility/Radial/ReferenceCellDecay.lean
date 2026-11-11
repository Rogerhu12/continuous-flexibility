import ContinuousFlexibility.Radial.ReferenceCellL2
import ContinuousFlexibility.Radial.R11bWeightEmbedding
import ContinuousFlexibility.Analysis.FlatExtension

/-!
# Endpoint limits from quantitative reference-cell decay

The cell distance bounds force the cell label to infinity at either endpoint.
A single filter argument then converts cellwise decay to both one-sided
limits.  In particular every fixed coefficient power is dominated by a
positive cubic attenuation margin.  The final extension theorem applies to
actual ordinary derivatives; estimates for those derivatives remain separate
analytic obligations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology
open ContinuousFlexibility.Statements

theorem reference_radialS_tendsto : Tendsto radialS atTop atTop := by
  have hle (n : ℕ) : (2 / 3 : ℝ) * n ≤ radialS n := by
    induction n with
    | zero => simp [radialS_zero]
    | succ n ih =>
      have hg := radialS_gap n
      push_cast
      linarith
  exact tendsto_atTop_mono hle
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 3))

theorem reference_exp_decay_tendsto (A : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => exp (A * radialQ n - γ * radialS n)) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := r11b_exp_weight_le A 0 (-γ / 2) (-γ / 4) (by linarith)
  have he : Tendsto (fun n : ℕ => exp (-(γ / 2 * radialS n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp
          (reference_radialS_tendsto.const_mul_atTop (by positivity : 0 < γ / 2)))
  have hbound (n : ℕ) :
      exp (A * radialQ n - γ * radialS n) ≤ K * exp (-(γ / 2 * radialS n)) := by
    convert hK n using 1 <;> congr 1 <;> ring
  apply squeeze_zero (fun n => (Real.exp_pos _).le) hbound
  simpa only [mul_zero] using he.const_mul K

/-- This statement is independent of the orientation of the endpoint. -/
theorem reference_cellIndex_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {α : Type*} {l : Filter α}
    {r : α → ℝ} {m : α → ℕ}
    (hc : ∀ᶠ x in l, r x ∈ D.cells (m x))
    (hd : Tendsto (fun x => min (r x - D.a) (D.b - r x)) l (𝓝 0)) :
    Tendsto (fun x => D.cellIndex (m x)) l atTop := by
  obtain ⟨C, _, _, hC, _, _, _, hdist, _⟩ := hD
  apply tendsto_atTop.2
  intro N
  have he : 0 < (C 0)⁻¹ * exp (-((N : ℝ) + 1) ^ 2) :=
    mul_pos (inv_pos.mpr (hC 0)) (exp_pos _)
  filter_upwards [hc, hd.eventually (Iio_mem_nhds he)] with x hx hsmall
  by_contra h
  have hn : (D.cellIndex (m x) : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_of_lt (not_le.mp h))
  have he' : exp (-((N : ℝ) + 1) ^ 2) ≤
      exp (-((D.cellIndex (m x) : ℝ) + 1) ^ 2) := by
    apply exp_le_exp.mpr
    nlinarith only [hn, Nat.cast_nonneg (D.cellIndex (m x)), Nat.cast_nonneg N]
  have hb := (mul_le_mul_of_nonneg_left he' (inv_nonneg.mpr (hC 0).le)).trans
    (hdist (m x) (r x) hx).1
  exact (not_lt_of_ge hb) hsmall

/-- Any decaying bound indexed by an actual containing cell gives a zero
limit when the distance to the endpoint tends to zero. -/
theorem reference_cellwise_tendsto_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {α : Type*} {l : Filter α}
    {r : α → ℝ} {f : ℝ → ℝ} {B : ℕ → ℝ}
    (hc : ∀ᶠ x in l, r x ∈ radialCore D)
    (hd : Tendsto (fun x => min (r x - D.a) (D.b - r x)) l (𝓝 0))
    (hB : Tendsto B atTop (𝓝 0))
    (hb : ∀ m x, x ∈ D.cells m → |f x| ≤ B (D.cellIndex m)) :
    Tendsto (fun x => f (r x)) l (𝓝 0) := by
  classical
  have hp : RadialPartition D := hD.choose_spec.2.1
  let m (x : α) : ℕ :=
    if hx : r x ∈ radialCore D then (hp.exists_localizer_ne_zero hx).choose else 0
  have hmem : ∀ᶠ x in l, r x ∈ D.cells (m x) := by
    filter_upwards [hc] with x hx
    dsimp only [m]
    rw [dif_pos hx]
    exact hp.2.2.1 _ (hp.exists_localizer_ne_zero hx).choose_spec
  have hi := reference_cellIndex_tendsto hD hmem hd
  apply tendsto_zero_iff_abs_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun x => abs_nonneg (f (r x)))
    (hmem.mono fun x hx => hb (m x) (r x) hx) (hB.comp hi)

/-- One proof supplies both endpoint limits. -/
theorem reference_cellwise_endpoint_limits {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ} {B : ℕ → ℝ}
    (hB : Tendsto B atTop (𝓝 0))
    (hb : ∀ m x, x ∈ D.cells m → |f x| ≤ B (D.cellIndex m)) :
    Tendsto f (𝓝[>] D.a) (𝓝 0) ∧ Tendsto f (𝓝[<] D.b) (𝓝 0) := by
  have hab : D.a < D.b := hD.choose_spec.1.2.1
  have hd : Continuous (fun x : ℝ => min (x - D.a) (D.b - x)) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  constructor
  · apply reference_cellwise_tendsto_zero hD (Ioo_mem_nhdsGT hab) _ hB hb
    simpa only [sub_self, min_eq_left (sub_nonneg.mpr hab.le)] using
      (hd.tendsto D.a).mono_left nhdsWithin_le_nhds
  · apply reference_cellwise_tendsto_zero hD (Ioo_mem_nhdsLT hab) _ hB hb
    simpa only [sub_self, min_eq_right (sub_nonneg.mpr hab.le)] using
      (hd.tendsto D.b).mono_left nhdsWithin_le_nhds

theorem reference_contDiff_zero_extension_of_cell_jets {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (radialCore D)) {γ : ℝ} (hγ : 0 < γ)
    (hjets : ∀ s : ℕ, ∃ C A : ℝ, ∀ m r, r ∈ D.cells m →
      |iteratedDeriv s f r| ≤
        C * exp (A * radialQ (D.cellIndex m) - γ * radialS (D.cellIndex m))) :
    ContDiff ℝ ∞ (Analysis.extendZeroOutside D.a D.b f) := by
  have hlim (s : ℕ) :
      Tendsto (iteratedDeriv s f) (𝓝[>] D.a) (𝓝 0) ∧
        Tendsto (iteratedDeriv s f) (𝓝[<] D.b) (𝓝 0) := by
    obtain ⟨C, A, hbound⟩ := hjets s
    apply reference_cellwise_endpoint_limits hD _ hbound
    simpa only [mul_zero] using (reference_exp_decay_tendsto A hγ).const_mul C
  exact Analysis.contDiff_extendZeroOutside hD.choose_spec.1.2.1 hf
    (fun s => (hlim s).1) (fun s => (hlim s).2)

end ContinuousFlexibility.Radial
