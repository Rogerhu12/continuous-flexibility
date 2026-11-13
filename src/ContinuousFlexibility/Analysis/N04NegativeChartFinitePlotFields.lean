import ContinuousFlexibility.Analysis.N04NegativeChartFullHalfFields
import ContinuousFlexibility.Analysis.N01cFlowAffineCompression
import ContinuousFlexibility.Analysis.PositivePowerMaterialJets

/-!
# Genuine finite-parameter representatives of the divided root fields

The actual fields admit globally smooth periodic representatives on each
finite state plot. Their full germs agree at every point of the closed
physical half. A scalar positive-power extension and a radial clamp are
used only outside those germs; no derivative bound for either extension
is used in the quantitative point-fiber flow theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- The same representatives retain the complete state-and-space germ
at every point of the actual closed half, including its root. -/
theorem fullHalfFields_finiteAffine_representatives_uniform
    {n : ℕ} (x : AnnularState W.S × ℝ)
    (hx : x ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState W.S × ℝ))
    (m : ℕ) (side : Bool) :
    ∃ d c : (Fin n → ℝ) × PolarPoint → ℝ,
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c ∧
      (∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi) ∧
      (∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi) ∧
      (∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
        d =ᶠ[𝓝 (0, p)] (fun q => F.fullHalfDrift (x + L q.1) m side q.2) ∧
        c =ᶠ[𝓝 (0, p)] (fun q => F.fullHalfSpeed (x + L q.1) m side q.2)) ∧
      ∃ V : Set (Fin n → ℝ), IsOpen V ∧ (0 : Fin n → ℝ) ∈ V ∧
        (∀ y ∈ V, x + L y ∈ stateNeighborhood W.S W.C W.base (W.ε / 2)) ∧
        ∀ y ∈ V, ∀ p : PolarPoint,
          p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
          d (y, p) = F.fullHalfDrift (x + L y) m side p ∧
          c (y, p) = F.fullHalfSpeed (x + L y) m side p := by
  let V : Set (Fin n → ℝ) :=
    (fun y => x + L y) ⁻¹' stateNeighborhood W.S W.C W.base (W.ε / 2)
  have hV : IsOpen V := (isOpen_stateNeighborhood W.S W.C W.base (W.ε / 2)).preimage
    (continuous_const.add L.continuous)
  have h0 : (0 : Fin n → ℝ) ∈ V := by
    simpa only [V, mem_preimage, map_zero, add_zero] using hx
  obtain ⟨ρ, hρ, hρ0, hρV, hρid⟩ := exists_smooth_neighbourhood_compression hV h0
  have hstate (y : Fin n → ℝ) :
      x + L (ρ y) ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) (hρV y)
  have hc := W.through03.1.1.2.2.2.1.1 m
  let a : ℝ := (W.D.a + W.C.left m) / 2
  let b : ℝ := (W.C.right m + W.D.b) / 2
  let ε : ℝ := min (W.C.left m - W.D.a) (W.D.b - W.C.right m) / 8
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2.2))
    (by norm_num)
  have hab : a ≤ b := by dsimp only [a, b]; linarith only [hc.1, hc.2.1, hc.2.2]
  have hleft : W.D.a < a - ε := by
    have h := min_le_left (W.C.left m - W.D.a) (W.D.b - W.C.right m)
    dsimp only [a, ε]
    linarith only [hc.1, h]
  have hright : b + ε < W.D.b := by
    have h := min_le_right (W.C.left m - W.D.a) (W.D.b - W.C.right m)
    dsimp only [b, ε]
    linarith only [hc.2.2, h]
  let R := circleFlowSmoothTimeClamp a b ε hab hε
  have hR : ContDiff ℝ ∞ R := contDiff_circleFlowSmoothTimeClamp hab hε
  have hRmem (r : ℝ) : R r ∈ Ioo W.D.a W.D.b :=
    ⟨hleft.trans (circleFlowSmoothTimeClamp_mem hab hε r).1,
      (circleFlowSmoothTimeClamp_mem hab hε r).2.trans hright⟩
  let Ψ : ((Fin n → ℝ) × PolarPoint) → (Fin n → ℝ) × PolarPoint :=
    fun q => (ρ q.1, (R (W.negativeInwardPoint m side q.2).1, q.2.2))
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (hρ.comp contDiff_fst).prodMk
      ((hR.comp (((W.negativeInwardPoint_contDiff m side).comp contDiff_snd).fst)).prodMk
        contDiff_snd.snd)
  have hA : N01PartA W.D W.T W.S W.C :=
    ⟨W.through03.1.1.1, W.through03.1.1.2.2.1, W.through03.1.1.2.2.2.1,
      W.through03.1.1.2.2.2.2.1, W.through03.1.1.2.2.2.2.2.1⟩
  have hB : N01PartB W.D W.S W.C W.base W.ε :=
    ⟨W.through03.1.1.2.2.2.2.2.2.1, W.through03.1.1.2.2.2.2.2.2.2.1,
      W.through03.1.1.2.2.2.2.2.2.2.2.1, W.through03.1.1.2.2.2.2.2.2.2.2.2.1,
      W.through03.1.1.2.2.2.2.2.2.2.2.2.2.1⟩
  let A : Fin 2 → ((Fin n → ℝ) × PolarPoint) → ℝ := fun i q =>
    normalizedSpeedFactor W.D W.S W.C i (x + L (Ψ q).1) (Ψ q).2
  have hAs (i : Fin 2) : ContDiff ℝ ∞ (A i) :=
    (contDiffOn_normalizedSpeedFactor_finiteAffine W.hS W.hT hA hB x L i).comp_contDiff
      hΨ (fun q => ⟨hstate q.1, hRmem _, mem_univ _⟩)
  let q : ((Fin n → ℝ) × PolarPoint) → ℝ := fun y =>
    F.stateSquare (x + L (ρ y.1)) m side y.2.1
  have hk : ContDiff ℝ ∞ (fun y : Fin n → ℝ => stateKappa W.S (x + L (ρ y)).1 m) :=
    (W.negativeKappa_finiteAffine_contDiff x L m).comp hρ
  have hq : ContDiff ℝ ∞ q :=
    ((F.reference_smooth m side).comp contDiff_snd.fst).sub
      ((hk.comp contDiff_fst).mul ((F.control_smooth m side).comp contDiff_snd.fst))
  obtain ⟨Bi, Ai, hBi, _, hinv⟩ := F.stateSquare_inverse_material
  obtain ⟨Bu, Au, hBu, _, hupper⟩ := F.stateSquare_material_jets 0
  let E : ℝ := W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side)))))
  have hE : 0 < E := zero_lt_one.trans_le (W.floor _)
  let l : ℝ := (Bi * E ^ Ai)⁻¹
  let u : ℝ := 1 + l + Bu * E ^ Au
  have hl : 0 < l := inv_pos.mpr (mul_pos hBi (Real.rpow_pos_of_pos hE _))
  have hlu : l ≤ u := by
    have hb := mul_pos hBu (Real.rpow_pos_of_pos hE Au)
    dsimp only [u]
    linarith only [hb]
  obtain ⟨Φ, hΦ, hΦeq, _⟩ := exists_smooth_positivePower_extension hl hlu (1 / 2 : ℝ)
  have hqrange (y : Fin n → ℝ) (p : PolarPoint)
      (hp : p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) : q (y, p) ∈ Icc l u := by
    have hpq := F.stateSquare_pos (hρV y) m side hp
    have hlo := inv_le_of_inv_le₀ hpq (hinv (x + L (ρ y)) (hρV y) m side p.1 hp)
    have hhi : q (y, p) ≤ Bu * E ^ Au := (le_abs_self _).trans (by
      simpa only [iteratedDeriv_zero] using
        hupper (x + L (ρ y)) (hρV y) m side p.1 hp)
    exact ⟨hlo, hhi.trans (by dsimp only [u]; linarith only [hl])⟩
  let d : ((Fin n → ℝ) × PolarPoint) → ℝ := fun y =>
    -n01ComponentRootOrientation side * A 0 y
  let c : ((Fin n → ℝ) × PolarPoint) → ℝ := fun y => Φ (q y) * A 1 y
  have hperiod (i : Fin 2) (y : Fin n → ℝ) (r θ : ℝ) :
      A i (y, (r, θ + Real.pi)) = A i (y, (r, θ)) := by
    simpa only [A, Ψ, negativeInwardPoint, Prod.mk_add_mk, add_zero] using
      normalizedSpeedFactor_periodic (C := W.C) W.hS (x + L (ρ y)) i
        (R (W.negativeInwardPoint m side (r, θ)).1, θ)
  refine ⟨d, c, contDiff_const.mul (hAs 0), (hΦ.comp hq).mul (hAs 1),
    fun y r θ => congrArg (fun z => -n01ComponentRootOrientation side * z) (hperiod 0 y r θ),
    fun y r θ => congrArg (fun z => Φ (q (y, (r, θ))) * z) (hperiod 1 y r θ), ?_, ?_⟩
  · intro p hp
    have hin := inwardComponentPoint_mem side
      (show p.1 ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) from
        ⟨hp.1, hp.2.trans (W.negativeOpticalWidth_le_component m side)⟩)
    have hpab : (W.negativeInwardPoint m side p).1 ∈ Ioo a b := by
      change a < inwardComponentPoint _ _ _ _ ∧ inwardComponentPoint _ _ _ _ < b
      dsimp only [a, b]
      constructor <;> linarith only [hin.1, hin.2, hc.1, hc.2.2]
    have hρg : (fun y : (Fin n → ℝ) × PolarPoint => ρ y.1) =ᶠ[𝓝 (0, p)]
        (fun y => y.1) := hρid.comp_tendsto continuousAt_fst
    have hRg : ∀ᶠ y : (Fin n → ℝ) × PolarPoint in 𝓝 (0, p),
        R (W.negativeInwardPoint m side y.2).1 = (W.negativeInwardPoint m side y.2).1 := by
      filter_upwards [((((W.negativeInwardPoint_contDiff m side).comp
        contDiff_snd).fst).continuous.continuousAt).tendsto.eventually
          (isOpen_Ioo.mem_nhds hpab)] with y hy
      exact circleFlowSmoothTimeClamp_eq hab hε ⟨hy.1.le, hy.2.le⟩
    have hAg (i : Fin 2) : A i =ᶠ[𝓝 (0, p)] (fun y =>
        normalizedSpeedFactor W.D W.S W.C i (x + L y.1) (W.negativeInwardPoint m side y.2)) := by
      filter_upwards [hρg, hRg] with y hy hz
      simp only [A, Ψ, hy, hz, negativeInwardPoint]
    have hΦg : (fun y => Φ (q y)) =ᶠ[𝓝 (0, p)] (fun y => Real.sqrt (q y)) := by
      simpa only [Real.sqrt_eq_rpow] using (hΦeq (q (0, p)) (hqrange 0 p hp)).comp_tendsto
        hq.continuous.continuousAt
    constructor
    · filter_upwards [hAg 0] with y hy
      exact congrArg (fun z => -n01ComponentRootOrientation side * z) hy
    · filter_upwards [hΦg, hAg 1, hρg] with y hφ ha hρy
      change Φ (q y) * A 1 y = _
      rw [hφ, ha]
      simp only [q, hρy, fullHalfSpeed, opticalSpeed]

  · obtain ⟨V₀, hV₀, hV₀open, h0V₀⟩ := mem_nhds_iff.mp hρid
    have hρeq (y : Fin n → ℝ) (hy : y ∈ V₀) : ρ y = y := hV₀ hy
    refine ⟨V₀, hV₀open, h0V₀, ?_, ?_⟩
    · intro y hy
      simpa only [hρeq y hy] using hρV y
    · intro y hy p hp
      have hin := inwardComponentPoint_mem side
        (show p.1 ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) from
          ⟨hp.1, hp.2.trans (W.negativeOpticalWidth_le_component m side)⟩)
      have hpab : (W.negativeInwardPoint m side p).1 ∈ Icc a b := by
        change a ≤ inwardComponentPoint _ _ _ _ ∧ inwardComponentPoint _ _ _ _ ≤ b
        dsimp only [a, b]
        constructor <;> linarith only [hin.1, hin.2, hc.1, hc.2.2]
      have hRid : R (W.negativeInwardPoint m side p).1 =
          (W.negativeInwardPoint m side p).1 := circleFlowSmoothTimeClamp_eq hab hε hpab
      have ha (i : Fin 2) : A i (y, p) =
          normalizedSpeedFactor W.D W.S W.C i (x + L y)
            (W.negativeInwardPoint m side p) := by
        simp only [A, Ψ, hρeq y hy, hRid, negativeInwardPoint]
      have hφ : Φ (q (y, p)) = Real.sqrt (q (y, p)) := by
        simpa only [Real.sqrt_eq_rpow] using (hΦeq (q (y, p)) (hqrange y p hp)).self_of_nhds
      constructor
      · exact congrArg (fun a => -n01ComponentRootOrientation side * a) (ha 0)
      · change Φ (q (y, p)) * A 1 (y, p) = _
        rw [hφ, ha 1]
        simp only [q, hρeq y hy, fullHalfSpeed, opticalSpeed]

/-- The pointwise germ interface is retained for existing callers. -/
theorem fullHalfFields_finiteAffine_representatives
    {n : ℕ} (x : AnnularState W.S × ℝ)
    (hx : x ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState W.S × ℝ))
    (m : ℕ) (side : Bool) :
    ∃ d c : (Fin n → ℝ) × PolarPoint → ℝ,
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c ∧
      (∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi) ∧
      (∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi) ∧
      (∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
        d =ᶠ[𝓝 (0, p)] (fun q => F.fullHalfDrift (x + L q.1) m side q.2) ∧
        c =ᶠ[𝓝 (0, p)] (fun q => F.fullHalfSpeed (x + L q.1) m side q.2)) := by
  obtain ⟨d, c, hd, hc, hdp, hcp, hg, _⟩ :=
    F.fullHalfFields_finiteAffine_representatives_uniform x hx L m side
  exact ⟨d, c, hd, hc, hdp, hcp, hg⟩

end ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_finiteAffine_representatives'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_finiteAffine_representatives
