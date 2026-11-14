module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05OpticalRootActual
public import ContinuousFlexibility.Analysis.N05OpticalProfileSecondDerivative
public import ContinuousFlexibility.Analysis.N05NegativeTravel
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative geometry of the actual negative reference halves

The optical root-distance lower bound is an explicit sufficient input
certificate. It is not asserted for the frozen N05 witnesses here. All
five chart and height bounds are derived for the actual N04 halves.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Radial

/-- Physical radius measured inward from either endpoint. -/
def n05OpticalInward (l u : ℝ) (right : Bool) (x : ℝ) : ℝ :=
  if right then u - x else l + x

theorem n05OpticalInward_deriv (f : ℝ → ℝ) (l u : ℝ) (right : Bool) (x : ℝ) :
    deriv (fun t => f (n05OpticalInward l u right t)) x =
      (if right then (-1 : ℝ) else 1) * deriv f (n05OpticalInward l u right x) := by
  cases right
  · simpa [n05OpticalInward] using deriv_comp_const_add f l x
  · simpa [n05OpticalInward] using deriv_comp_const_sub f u x

theorem n05OpticalInward_secondDeriv (f : ℝ → ℝ) (l u : ℝ) (right : Bool) (x : ℝ) :
    deriv (deriv (fun t => f (n05OpticalInward l u right t))) x =
      deriv (deriv f) (n05OpticalInward l u right x) := by
  have he : deriv (fun t => f (n05OpticalInward l u right t)) =
      fun t => (if right then (-1 : ℝ) else 1) *
        deriv f (n05OpticalInward l u right t) :=
    funext (n05OpticalInward_deriv f l u right)
  rw [he, deriv_const_mul_field, n05OpticalInward_deriv]
  cases right <;> simp

theorem n05OpticalInward_abs_deriv (f : ℝ → ℝ) (l u : ℝ) (right : Bool) (x : ℝ) :
    |deriv (fun t => f (n05OpticalInward l u right t)) x| =
      |deriv f (n05OpticalInward l u right x)| := by
  rw [n05OpticalInward_deriv]
  cases right <;> simp

private theorem n05_optical_coarse_five_bound {Λ L κ P q H d : ℝ}
    (hΛ : 1 ≤ Λ) (hL : 0 < L) (hLΛ : L ≤ Λ) (hκ : 0 < κ)
    (hκinv : 1 / κ = 2 * Λ ^ 3 * L) (hP : P = 1 + Λ + 1 / κ)
    (hq : q ≤ P) (hqi : q⁻¹ ≤ P)
    (hH : H ≤ Real.sqrt (Λ * P)) (hHi : H⁻¹ ≤ Real.sqrt (Λ * P))
    (hd : |d| ≤ Real.sqrt (Λ * P) / 2 * (Λ ^ 2 + Λ / κ)) :
    q + q⁻¹ + H + H⁻¹ + |d| ≤ 100 * Λ ^ 8 := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hp14 : Λ ≤ Λ ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hΛ (by decide : (1 : ℕ) ≤ 4)
  have hp04 : 1 ≤ Λ ^ 4 := one_le_pow₀ hΛ
  have hki : 1 / κ ≤ 2 * Λ ^ 4 := by
    rw [hκinv]
    calc
      2 * Λ ^ 3 * L ≤ 2 * Λ ^ 3 * Λ :=
        mul_le_mul_of_nonneg_left hLΛ (by positivity)
      _ = 2 * Λ ^ 4 := by ring
  have hPB : P ≤ 4 * Λ ^ 4 := by
    rw [hP]
    linarith only [hki, hp14, hp04]
  have hsqrt : Real.sqrt (Λ * P) ≤ 2 * Λ ^ 3 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hPB hΛpos.le
    have hp56 := pow_le_pow_right₀ hΛ (by decide : (5 : ℕ) ≤ 6)
    nlinarith only [hm, hp56]
  have hMκ : Λ / κ ≤ 2 * Λ ^ 5 := by
    calc
      Λ / κ = Λ * (1 / κ) := by ring
      _ ≤ Λ * (2 * Λ ^ 4) := mul_le_mul_of_nonneg_left hki hΛpos.le
      _ = 2 * Λ ^ 5 := by ring
  have hf : Λ ^ 2 + Λ / κ ≤ 3 * Λ ^ 5 := by
    have hp25 := pow_le_pow_right₀ hΛ (by decide : (2 : ℕ) ≤ 5)
    linarith only [hMκ, hp25]
  have hder : |d| ≤ 3 * Λ ^ 8 := hd.trans (by
    calc
      Real.sqrt (Λ * P) / 2 * (Λ ^ 2 + Λ / κ) ≤
          (2 * Λ ^ 3) / 2 * (3 * Λ ^ 5) :=
        mul_le_mul (div_le_div_of_nonneg_right hsqrt (by norm_num)) hf
          (by positivity) (by positivity)
      _ = 3 * Λ ^ 8 := by ring)
  have hqB := hq.trans hPB
  have hqiB := hqi.trans hPB
  have hHB := hH.trans hsqrt
  have hHiB := hHi.trans hsqrt
  have hp38 := pow_le_pow_right₀ hΛ (by decide : (3 : ℕ) ≤ 8)
  have hp48 := pow_le_pow_right₀ hΛ (by decide : (4 : ℕ) ≤ 8)
  have hp8 := pow_nonneg hΛpos.le 8
  nlinarith only [hqB, hqiB, hHB, hHiB, hder, hp38, hp48, hp8]

/-- A sufficient lower certificate for the actual optical radicand on
one entire negative component, including its two roots. -/
def N05ComponentOpticalLower (D : ReferenceData) (l u α : ℝ) : Prop :=
  ∀ r ∈ Icc l u,
    α * min (r - l) (u - r) ≤ -deriv D.w r / (r * D.w r)

/-- A single genuine negative component with a common physical envelope.
The input bounds concern only the physical profile, its optical radicand
and the original travel. Neither chart derivatives nor height bounds are
assumed. The conclusion concerns both actual closed N04 cut halves. -/
theorem n05_negative_component_first_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hDb : D.b ≤ Λ)
    (htravel : 1 / Λ ≤ C.travel m)
    (hlower : N05ComponentOpticalLower D (C.left m) (C.right m) (1 / Λ))
    (hjet : ∀ r ∈ Icc (C.left m) (C.right m),
      |(-deriv D.w r / (r * D.w r))| ≤ Λ ∧
        |deriv (fun t => -deriv D.w t / (t * D.w t)) r| ≤ Λ ∧
        |deriv (deriv (fun t => -deriv D.w t / (t * D.w t))) r| ≤ Λ)
    (hweight : ∀ r ∈ Icc (C.left m) (C.right m), 1 / Λ ≤ D.w r ∧ D.w r ≤ Λ) :
    ∀ (right : Bool) (r : ℝ),
      r ∈ Icc
        (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) →
      ∀ θ : ℝ,
      let i := if right then (K.cutPair m).2 else (K.cutPair m).1
      let H := K.height (C.referenceState, 0) i (r, θ)
      let J := planeJacobian (K.chart (C.referenceState, 0) i) (r, θ)
      H + H⁻¹ + |deriv (fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)) r| +
        |J| + |J⁻¹| ≤ 100 * Λ ^ 8 := by
  let l := C.left m
  let u := C.right m
  let c := K.physicalRight (K.cutPair m).1
  let ℓ := u - l
  let F : ℝ → ℝ := fun t => -deriv D.w t / (t * D.w t)
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hC := h.1.1.1.2.2.2.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hclosed := n05_reference_closed_properties h04
  have hcuts := h04.2.1.1.1
  obtain ⟨hnegL, hnegR, hleft, hright, hmeet, _, _, _, _⟩ := hcuts m
  have hlc : l < c := by
    change C.left m < K.physicalRight (K.cutPair m).1
    rw [← hleft]
    exact (hpieces (K.cutPair m).1).1
  have hcu : c < u := by
    change K.physicalRight (K.cutPair m).1 < C.right m
    rw [hmeet, ← hright]
    exact (hpieces (K.cutPair m).2).1
  have hℓ : 0 < ℓ := sub_pos.mpr (hlc.trans hcu)
  have hcore : Icc l u ⊆ radialCore D := by
    intro t ht
    exact ⟨(hC.1 m).1.trans_le ht.1, ht.2.trans_lt (hC.1 m).2.2⟩
  have hlpos : 0 < l := hD.choose_spec.1.1.trans (hC.1 m).1
  have hℓΛ : ℓ ≤ Λ := by
    have hu := (hC.1 m).2.2.le.trans hDb
    dsimp only [ℓ]
    linarith only [hlpos, hu]
  have hw : ContDiff ℝ ∞ D.w := hD.choose_spec.1.2.2.1.1
  have hFC : ContDiffOn ℝ ∞ F (radialCore D) :=
    (n05_referenceModerate_opticalRadicand hD).1.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs := n05_referenceState_sector h.1.1.1.2.2.1
  intro right r hr θ
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let root := if right then u else l
  let σ : ℝ := if right then -1 else 1
  let a := if right then u - c else c - l
  let ρ := n05OpticalInward l u right
  let G := fun x : ℝ => F (ρ x)
  let ξ := fun x : ℝ => (K.chart (C.referenceState, 0) i (ρ x, θ)).1
  let H := fun x : ℝ => K.height (C.referenceState, 0) i (ρ x, θ)
  let w := fun x : ℝ => D.w (ρ x)
  have hi : K.positive i = false := by
    cases right
    · exact hnegL
    · exact hnegR
  have ha : 0 < a := by
    cases right
    · change 0 < c - l
      exact sub_pos.mpr hlc
    · change 0 < u - c
      exact sub_pos.mpr hcu
  have haℓ : a < ℓ := by
    cases right
    · change c - l < u - l
      linarith only [hcu]
    · change u - c < u - l
      linarith only [hlc]
  have hρeq (x : ℝ) : ρ x = root + σ * x := by
    cases right
    · change l + x = l + (1 : ℝ) * x
      ring
    · change u - x = u + (-1 : ℝ) * x
      ring
  have hρC : ContDiff ℝ ∞ ρ := by
    cases right
    · change ContDiff ℝ ∞ (fun x : ℝ => l + x)
      exact contDiff_const.add contDiff_id
    · change ContDiff ℝ ∞ (fun x : ℝ => u - x)
      exact contDiff_const.sub contDiff_id
  have hmap (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : ρ x ∈ Icc l u := by
    dsimp only [ℓ] at hx
    cases right
    · change l ≤ l + x ∧ l + x ≤ u
      constructor <;> linarith only [hx.1, hx.2]
    · change l ≤ u - x ∧ u - x ≤ u
      constructor <;> linarith only [hx.1, hx.2]
  have hmapHalf (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) :
      ρ x ∈ Icc (K.physicalLeft i) (K.physicalRight i) := by
    cases right
    · change l + x ∈ Icc (K.physicalLeft (K.cutPair m).1) (K.physicalRight (K.cutPair m).1)
      rw [hleft]
      change l ≤ l + x ∧ l + x ≤ c
      change x ∈ Icc (0 : ℝ) (c - l) at hx
      constructor <;> linarith only [hx.1, hx.2]
    · change u - x ∈ Icc (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2)
      rw [← hmeet, hright]
      change c ≤ u - x ∧ u - x ≤ u
      change x ∈ Icc (0 : ℝ) (u - c) at hx
      constructor <;> linarith only [hx.1, hx.2]
  have hmapOpen (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) :
      ρ x ∈ Ioo (K.physicalLeft i) (K.physicalRight i) := by
    cases right
    · change l + x ∈ Ioo (K.physicalLeft (K.cutPair m).1) (K.physicalRight (K.cutPair m).1)
      rw [hleft]
      change l < l + x ∧ l + x < c
      change x ∈ Ioo (0 : ℝ) (c - l) at hx
      constructor <;> linarith only [hx.1, hx.2]
    · change u - x ∈ Ioo (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2)
      rw [← hmeet, hright]
      change c < u - x ∧ u - x < u
      change x ∈ Ioo (0 : ℝ) (u - c) at hx
      constructor <;> linarith only [hx.1, hx.2]
  have hsub : Icc (0 : ℝ) a ⊆ Icc (0 : ℝ) ℓ := Icc_subset_Icc le_rfl haℓ.le
  have hGc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : ContDiffAt ℝ 2 G x :=
    ((hFC.contDiffAt (isOpen_Ioo.mem_nhds (hcore (hmap x hx)))).comp x
      hρC.contDiffAt).of_le (by simp)
  have hξc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : ContDiffAt ℝ 2 ξ x :=
    (ContDiffAt.fun_comp (f := fun t : ℝ => (ρ t, θ))
      (g := fun p : PolarPoint => (K.chart (C.referenceState, 0) i p).1) x
      (hclosed hmem hs i (ρ x, θ) (hmapHalf x hx)).1.fst
      (hρC.contDiffAt.prodMk contDiffAt_const)).of_le (by simp)
  have hHc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : ContDiffAt ℝ 1 H x :=
    (ContDiffAt.fun_comp (f := fun t : ℝ => (ρ t, θ))
      (g := K.height (C.referenceState, 0) i) x
      (hclosed hmem hs i (ρ x, θ) (hmapHalf x hx)).2.1
      (hρC.contDiffAt.prodMk contDiffAt_const)).of_le (by simp)
  have hwc (x : ℝ) (_hx : x ∈ Icc (0 : ℝ) a) : DifferentiableAt ℝ w x :=
    (hw.comp hρC).differentiable (by simp) x
  have hzero : G 0 = 0 := by
    cases right
    · simp only [G, ρ, n05OpticalInward, Bool.false_eq_true, if_false, add_zero,
        F, l, (hC.2.1 m).1, neg_zero, zero_div]
    · simp only [G, ρ, n05OpticalInward, if_true, sub_zero,
        F, u, (hC.2.1 m).2.1, neg_zero, zero_div]
  have hdist (x : ℝ) : min (ρ x - l) (u - ρ x) = min x (ℓ - x) := by
    cases right
    · change min (l + x - l) (u - (l + x)) = min x ((u - l) - x)
      congr 1 <;> ring
    · change min (u - x - l) (u - (u - x)) = min x ((u - l) - x)
      rw [min_comm]
      congr 1 <;> ring
  have hGlow (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      (1 / Λ) * min x (ℓ - x) ≤ G x := by
    have hb := hlower (ρ x) (hmap x hx)
    change (1 / Λ) * min (ρ x - l) (u - ρ x) ≤ G x at hb
    simpa only [hdist] using hb
  have hGupper (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : G x ≤ Λ ^ 2 := by
    have hb : G x ≤ Λ := (le_abs_self _).trans (hjet _ (hmap x hx)).1
    nlinarith only [hb, hΛ, sq_nonneg (Λ - 1)]
  have hGfirst (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : |deriv G x| ≤ Λ := by
    change |deriv (fun t => F (n05OpticalInward l u right t)) x| ≤ Λ
    rw [n05OpticalInward_abs_deriv]
    exact (hjet _ (hmap x hx)).2.1
  have hGsecond (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : |deriv (deriv G) x| ≤ Λ := by
    change |deriv (deriv (fun t => F (n05OpticalInward l u right t))) x| ≤ Λ
    rw [n05OpticalInward_secondDeriv]
    exact (hjet _ (hmap x hx)).2.2
  have htime (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) :
      (∫ t in (0 : ℝ)..x, Real.sqrt (G t)) =
        (2 / 3 : ℝ) * ξ x * Real.sqrt (ξ x) := by
    have hactual : root + σ * x ∈ Icc (K.physicalLeft i) (K.physicalRight i) := by
      rw [← hρeq]
      exact hmapHalf x hx
    have ht := n05_cut_reference_inward_optical_time hT hS h m right x θ hactual
    change (∫ t in (0 : ℝ)..x, Real.sqrt (F (root + σ * t))) =
      (2 / 3 : ℝ) * (K.chart (C.referenceState, 0) i (root + σ * x, θ)).1 *
        Real.sqrt (K.chart (C.referenceState, 0) i (root + σ * x, θ)).1 at ht
    simpa only [← hρeq] using ht
  have hpositive (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) : 0 < ξ x ∧ 0 < deriv ξ x := by
    have hp := n05_cut_reference_inward_deriv_pos hT hS h m right (hmapOpen x hx) θ
    refine ⟨hp.1, ?_⟩
    change 0 < deriv (fun t =>
      (K.chart (C.referenceState, 0) i (n05OpticalInward l u right t, θ)).1) x
    rw [n05OpticalInward_deriv
      (fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1) l u right x]
    exact hp.2
  have hsymbol (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) : ξ x * (deriv ξ x) ^ 2 = G x := by
    have hd := n05_negative_reference_density_closed hT hS h hi
      (hmapHalf x (Ioo_subset_Icc_self hx)) θ
    have he := n05OpticalInward_abs_deriv
      (fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1) l u right x
    change |deriv ξ x| = _ at he
    rw [← sq_abs (deriv ξ x), he]
    exact hd.2.2.1
  have hnormal (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : H x ^ 2 * w x * |deriv ξ x| = 1 := by
    have he := n05OpticalInward_abs_deriv
      (fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1) l u right x
    change |deriv ξ x| = _ at he
    rw [he]
    exact (n05_negative_reference_density_closed hT hS h hi (hmapHalf x hx) θ).2.1
  have hHpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : 0 < H x :=
    (hclosed hmem hs i (ρ x, θ) (hmapHalf x hx)).2.2.2
  have hweightIn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : 1 / Λ ≤ w x ∧ w x ≤ Λ :=
    hweight _ (hmap x (hsub hx))
  have hwlog (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : |deriv w x / w x| ≤ Λ ^ 2 := by
    have hxD := hcore (hmap x (hsub hx))
    have hrpos : 0 < ρ x := hD.choose_spec.1.1.trans hxD.1
    have hwpos : 0 < D.w (ρ x) := (one_div_pos.mpr hΛpos).trans_le (hweightIn x hx).1
    have he : deriv D.w (ρ x) / D.w (ρ x) = -(ρ x * F (ρ x)) := by
      dsimp only [F]
      field_simp [hrpos.ne', hwpos.ne'] <;> ring
    have hrad : |ρ x| ≤ Λ := by rw [abs_of_pos hrpos]; exact hxD.2.le.trans hDb
    have hew : |deriv w x| = |deriv D.w (ρ x)| :=
      n05OpticalInward_abs_deriv D.w l u right x
    calc
      |deriv w x / w x| = |deriv D.w (ρ x) / D.w (ρ x)| := by
        change |deriv w x / D.w (ρ x)| = |deriv D.w (ρ x) / D.w (ρ x)|
        rw [abs_div, abs_div, hew]
      _ = |ρ x| * |F (ρ x)| := by rw [he, abs_neg, abs_mul]
      _ ≤ Λ * Λ := mul_le_mul hrad (hjet _ (hmap x (hsub hx))).1 (abs_nonneg _) hΛpos.le
      _ = Λ ^ 2 := (pow_two _).symm
  have hcut : ρ a = c := by
    cases right
    · change l + (c - l) = c
      ring
    · change u - (u - c) = c
      ring
  have hfull : (∫ t in (0 : ℝ)..ℓ, Real.sqrt (G t)) = C.travel m := by
    cases right
    · change (∫ t in (0 : ℝ)..ℓ, opticalSpeed D.w (l + t)) = C.travel m
      rw [intervalIntegral.integral_comp_add_left, add_zero,
        show l + ℓ = u by dsimp only [ℓ]; ring]
      exact (n05_controlTravel_eq_opticalTravel hC m).symm
    · change (∫ t in (0 : ℝ)..ℓ, opticalSpeed D.w (u - t)) = C.travel m
      rw [intervalIntegral.integral_comp_sub_left, sub_zero,
        show u - ℓ = l by dsimp only [ℓ]; ring]
      exact (n05_controlTravel_eq_opticalTravel hC m).symm
  have hhalf : (∫ t in (0 : ℝ)..a, Real.sqrt (G t)) = C.travel m / 2 := by
    have ht := htime a ⟨ha.le, le_rfl⟩
    have hiPair : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 := by
      cases right
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hc := n05_cut_reference_image hT hS h m hiPair θ
    have hξa : ξ a = K.cutRadius m := by
      change (K.chart (C.referenceState, 0) i (ρ a, θ)).1 = _
      rw [hcut]
      exact hc
    rw [hξa] at ht
    have htotal := n05_cut_totalTravel_eq_time hT hS h m
    dsimp only [n05TricomiTime] at htotal
    nlinarith only [ht, htotal]
  have hGcontinuous : ContinuousOn (fun x => Real.sqrt (G x)) (Icc (0 : ℝ) ℓ) :=
    Real.continuous_sqrt.comp_continuousOn
      (fun x hx => (hGc x hx).continuousAt.continuousWithinAt)
  have hleftTravel : (1 / Λ) / 2 ≤ ∫ t in (0 : ℝ)..a, Real.sqrt (G t) := by
    rw [hhalf]
    exact div_le_div_of_nonneg_right htravel (by norm_num)
  have hrightTravel : (1 / Λ) / 2 ≤ ∫ t in a..ℓ, Real.sqrt (G t) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((hGcontinuous.mono hsub).intervalIntegrable_of_Icc (μ := volume) ha.le)
      ((hGcontinuous.mono (Icc_subset_Icc ha.le le_rfl)).intervalIntegrable_of_Icc
        (μ := volume) haℓ.le)
    rw [hhalf, hfull] at hadd
    linarith only [hadd, htravel]
  let M : NNReal := ⟨Λ, hΛpos.le⟩
  have hbound := n05_optical_equal_cut_height_geometry ha haℓ (one_div_pos.mpr hΛpos)
    (one_div_pos.mpr hΛpos) hΛpos hΛpos.le hΛpos (sq_nonneg Λ)
    hGc hξc hwc hHc hzero hGlow hGupper hGfirst (M := M) hGsecond
    hleftTravel hrightTravel (fun x hx => (hpositive x hx).1)
    (fun x hx => (hpositive x hx).2) hsymbol htime hweightIn hwlog hHpos hnormal
  let κ := (1 / Λ) * ((1 / Λ) / (2 * Λ)) / ℓ
  let P := 1 + Λ + 1 / κ
  change _ ∧ _ ∧ 0 < κ ∧ ∀ x ∈ Icc (0 : ℝ) a,
    1 / P ≤ deriv ξ x ∧ deriv ξ x ≤ P ∧ (deriv ξ x)⁻¹ ≤ P ∧
      |deriv (deriv ξ) x| ≤ (Λ / κ) * deriv ξ x ∧
      H x ≤ Real.sqrt (Λ * P) ∧ (H x)⁻¹ ≤ Real.sqrt (Λ * P) ∧
      |deriv H x| ≤ Real.sqrt (Λ * P) / 2 * (Λ ^ 2 + Λ / κ) at hbound
  let x := if right then u - r else r - l
  have hκ : 0 < κ := hbound.2.2.1
  have hx : x ∈ Icc (0 : ℝ) a := by
    cases right
    · change r ∈ Icc (K.physicalLeft (K.cutPair m).1) (K.physicalRight (K.cutPair m).1) at hr
      rw [hleft] at hr
      change 0 ≤ r - l ∧ r - l ≤ c - l
      constructor <;> linarith only [hr.1, hr.2]
    · change r ∈ Icc (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2) at hr
      rw [← hmeet, hright] at hr
      change 0 ≤ u - r ∧ u - r ≤ u - c
      constructor <;> linarith only [hr.1, hr.2]
  have hρx : ρ x = r := by
    cases right
    · change l + (r - l) = r
      ring
    · change u - (u - r) = r
      ring
  have hb := hbound.2.2.2 x hx
  have hκinv : 1 / κ = 2 * Λ ^ 3 * ℓ := by
    dsimp only [κ]
    field_simp [hΛpos.ne', hℓ.ne'] <;> ring
  have hfive := n05_optical_coarse_five_bound hΛ hℓ hℓΛ hκ hκinv
    (show P = 1 + Λ + 1 / κ from rfl) hb.2.1 hb.2.2.1
    hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2
  have hqpos : 0 < deriv ξ x :=
    (one_div_pos.mpr (by dsimp only [P]; positivity)).trans_le hb.1
  have hJ : deriv ξ x = |planeJacobian (K.chart (C.referenceState, 0) i) (r, θ)| := by
    have he := n05OpticalInward_abs_deriv
      (fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1) l u right x
    change |deriv ξ x| =
      |deriv (fun t : ℝ => (K.chart (C.referenceState, 0) i (t, θ)).1) (ρ x)| at he
    rw [abs_of_pos hqpos, hρx] at he
    exact he.trans (congrArg abs
      (n05_negative_reference_density_closed hT hS h hi hr θ).1.symm)
  have hHd : |deriv H x| =
      |deriv (fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)) r| := by
    have he := n05OpticalInward_abs_deriv
      (fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)) l u right x
    change |deriv H x| =
      |deriv (fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)) (ρ x)| at he
    simpa only [hρx] using he
  have hHx : H x = K.height (C.referenceState, 0) i (r, θ) := by
    change K.height (C.referenceState, 0) i (ρ x, θ) = _
    rw [hρx]
  rw [hJ, hHd, hHx] at hfive
  change K.height (C.referenceState, 0) i (r, θ) +
    (K.height (C.referenceState, 0) i (r, θ))⁻¹ +
    |deriv (fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)) r| +
    |planeJacobian (K.chart (C.referenceState, 0) i) (r, θ)| +
    |(planeJacobian (K.chart (C.referenceState, 0) i) (r, θ))⁻¹| ≤ 100 * Λ ^ 8
  rw [abs_inv]
  linarith only [hfive]

private theorem n05_moderate_closed_cell_bound {D : ReferenceData} {f : ℝ → ℝ}
    (hf : ReferenceModerate D f) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ (j : ℕ) (l u : ℝ),
      l < u → Ioo l u ⊆ D.cells j → Icc l u ⊆ radialCore D →
      ∀ r ∈ Icc l u, |f r| ≤ B * radialE (D.cellIndex j) ^ A := by
  obtain ⟨hc, B₀, A₀, hB₀, hb⟩ := hf
  let B := B₀ + 1
  let A := |A₀| + 1
  have hB : 0 < B := by dsimp only [B]; linarith only [hB₀]
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨B, A, hB, hA, fun j l u hlu hcell hcore r hr => ?_⟩
  have ho (x : ℝ) (hx : x ∈ Ioo l u) : |f x| ≤ B * radialE (D.cellIndex j) ^ A := by
    have hpow : Real.exp (A₀ * radialQ (D.cellIndex j)) ≤
        Real.exp (A * radialQ (D.cellIndex j)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (by dsimp only [A]; linarith only [le_abs_self A₀]) (radialQ_nonneg _))
    calc
      |f x| ≤ B₀ * Real.exp (A₀ * radialQ (D.cellIndex j)) := hb j x (hcell hx)
      _ ≤ B * Real.exp (A * radialQ (D.cellIndex j)) :=
        mul_le_mul (by dsimp only [B]; linarith) hpow (Real.exp_pos _).le hB.le
      _ = B * radialE (D.cellIndex j) ^ A := by
        rw [radialE, ← Real.exp_mul]
        congr 1
        congr 1
        ring
  apply le_on_closure ho
    (by simpa only [closure_Ioo hlu.ne] using (hc.continuousOn.abs.mono hcore))
    continuousOn_const
  simpa only [closure_Ioo hlu.ne] using hr

/-- The physical envelope uses the real carrier supplied by return
margins. Its constants are uniform before the component and carrier are
selected; no relation to the old canonical tag `K.cell` is asserted. -/
theorem n05_negative_component_physical_envelope
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : IsRadialReference D) (hC : controlGeometryConditions D S C) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m : ℕ, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      let Λ := B * radialE (D.cellIndex j) ^ A
      1 ≤ Λ ∧ D.b ≤ Λ ∧ 1 / Λ ≤ C.travel m ∧
        (∀ r ∈ Icc (C.left m) (C.right m),
          |(-deriv D.w r / (r * D.w r))| ≤ Λ ∧
            |deriv (fun t => -deriv D.w t / (t * D.w t)) r| ≤ Λ ∧
            |deriv (deriv (fun t => -deriv D.w t / (t * D.w t))) r| ≤ Λ) ∧
        (∀ r ∈ Icc (C.left m) (C.right m), 1 / Λ ≤ D.w r ∧ D.w r ≤ Λ) := by
  obtain ⟨BF, AF, hBF, hAF, hF⟩ := n05_opticalRadicand_cell_derivatives_bound hD.1
  have hwMod : ReferenceModerate D D.w := by
    simpa only [iteratedDeriv_zero] using referenceModerate_profile_jet hD.1 0
  have hiMod : ReferenceModerate D (fun r => (D.w r)⁻¹) := by
    simpa only [iteratedDeriv_zero] using referenceModerate_reciprocal_profile_jet hD.1 0
  obtain ⟨Bw, Aw, hBw, hAw, hwb⟩ := n05_moderate_closed_cell_bound hwMod
  obtain ⟨Bi, Ai, hBi, hAi, hib⟩ := n05_moderate_closed_cell_bound hiMod
  obtain ⟨AT, hAT, hreturn⟩ := hD.2.2.1.2
  let B := BF + Bw + Bi + |D.b| + 2
  let A := AF + Aw + Ai + AT + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith only [hBF, hBw, hBi, abs_nonneg D.b]
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨B, A, hB, hA, fun m => ?_⟩
  have hcomponent : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
      (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩
  obtain ⟨j, hcell, c, hc, hci, hsin⟩ := (hreturn _ _ hcomponent).2
  let E := radialE (D.cellIndex j)
  let Λ := B * E ^ A
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (radialQ_nonneg _)
  have hEA : 1 ≤ E ^ A := Real.one_le_rpow hE1 hA.le
  have hΛpos : 0 < Λ := mul_pos hB (Real.rpow_pos_of_pos hEpos _)
  have hBΛ : B ≤ Λ := by
    have hb := mul_le_mul_of_nonneg_left hEA hB.le
    simpa only [mul_one] using hb
  have hdom {b a : ℝ} (hbB : b ≤ B) (haA : a ≤ A) : b * E ^ a ≤ Λ :=
    mul_le_mul hbB (Real.rpow_le_rpow_of_exponent_le hE1 haA)
      (Real.rpow_nonneg hEpos.le _) hB.le
  have hBFΛ : BF * E ^ AF ≤ Λ := hdom
    (by dsimp only [B]; linarith only [hBw, hBi, abs_nonneg D.b])
    (by dsimp only [A]; linarith only [hAw, hAi, hAT])
  have hBwΛ : Bw * E ^ Aw ≤ Λ := hdom
    (by dsimp only [B]; linarith only [hBF, hBi, abs_nonneg D.b])
    (by dsimp only [A]; linarith only [hAF, hAi, hAT])
  have hBiΛ : Bi * E ^ Ai ≤ Λ := hdom
    (by dsimp only [B]; linarith only [hBF, hBw, abs_nonneg D.b])
    (by dsimp only [A]; linarith only [hAF, hAw, hAT])
  have hETΛ : E ^ AT ≤ Λ := by
    simpa only [one_mul] using hdom hB1
      (by dsimp only [A]; linarith only [hAF, hAw, hAi] : AT ≤ A)
  have hcore : Icc (C.left m) (C.right m) ⊆ radialCore D := by
    intro r hr
    exact ⟨(hC.1 m).1.trans_le hr.1, hr.2.trans_lt (hC.1 m).2.2⟩
  have htravelEq : C.travel m = radialTravel D (C.left m) (C.right m) :=
    n05_controlTravel_eq_opticalTravel hC m
  have htravelNonneg : 0 ≤ C.travel m := by
    rw [htravelEq]
    exact intervalIntegral.integral_nonneg_of_forall (hC.1 m).2.1.le
      (fun r => Real.sqrt_nonneg _)
  have hcTravel : c ≤ C.travel m := by
    have hsin1 : c ≤ |Real.sin (C.travel m)| := by
      simpa only [Nat.cast_one, div_one, one_mul, ← htravelEq] using hsin 1 le_rfl
    exact hsin1.trans (by
      simpa only [abs_of_nonneg htravelNonneg] using
        (Real.abs_sin_le_abs (x := C.travel m)))
  refine ⟨j, hcell, hB1.trans hBΛ, ?_, ?_, ?_, ?_⟩
  · exact (le_abs_self D.b).trans
      ((by dsimp only [B]; linarith only [hBF, hBw, hBi] : |D.b| ≤ B).trans hBΛ)
  · have hrecip : 1 / c ≤ Λ := by simpa only [one_div] using hci.trans hETΛ
    exact ((one_div_le hΛpos hc).mpr hrecip).trans hcTravel
  · intro r hr
    have hb := hF j (C.left m) (C.right m) (hC.1 m).2.1 hcell hcore r hr
    exact ⟨hb.1.trans hBFΛ, hb.2.1.trans hBFΛ, hb.2.2.trans hBFΛ⟩
  · intro r hr
    have hrpos : 0 < D.w r := hD.1.choose_spec.1.2.2.2.2.1 r (hcore hr)
    have hb := (hwb j _ _ (hC.1 m).2.1 hcell hcore r hr).trans hBwΛ
    have hi := (hib j _ _ (hC.1 m).2.1 hcell hcore r hr).trans hBiΛ
    refine ⟨(one_div_le hΛpos hrpos).mpr ?_, (le_abs_self _).trans hb⟩
    simpa only [one_div, abs_of_pos (inv_pos.mpr hrpos)] using hi

/-- The five actual first-geometry coefficients, evaluated on a physical
reference slice. This definition contains no independently chosen jets. -/
def n05NegativeReferenceFirstSize (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (i : ℕ) (r θ : ℝ) : ℝ :=
  let H := K.height (C.referenceState, 0) i (r, θ)
  let J := planeJacobian (K.chart (C.referenceState, 0) i) (r, θ)
  H + H⁻¹ + |deriv (fun t : ℝ => K.height (C.referenceState, 0) i (t, θ)) r| +
    |J| + |J⁻¹|

/-- Uniform actual-cell costs with the optical lower constant kept
visible. The carrier and all other constants are selected before that
lower constant, the orientation and the evaluation point. -/
theorem n05_negative_component_first_bound_of_opticalLower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m : ℕ, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ α : ℝ, 0 < α → N05ComponentOpticalLower D (C.left m) (C.right m) α →
        ∀ (right : Bool) (r : ℝ),
          r ∈ Icc
            (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
            (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) →
          ∀ θ : ℝ,
          n05NegativeReferenceFirstSize S C K
            (if right then (K.cutPair m).2 else (K.cutPair m).1) r θ ≤
              B * (1 + α⁻¹) ^ 8 * radialE (D.cellIndex j) ^ A := by
  obtain ⟨B₀, A₀, hB₀, hA₀, hphysical⟩ :=
    n05_negative_component_physical_envelope hD h.1.1.1.2.2.2.1
  refine ⟨100 * B₀ ^ 8, A₀ * 8, by positivity, by positivity, fun m => ?_⟩
  obtain ⟨j, hcell, hbase⟩ := hphysical m
  let E := radialE (D.cellIndex j)
  let baseEnvelope := B₀ * E ^ A₀
  change 1 ≤ baseEnvelope ∧ D.b ≤ baseEnvelope ∧ 1 / baseEnvelope ≤ C.travel m ∧ _ at hbase
  have hbasePos : 0 < baseEnvelope := lt_of_lt_of_le zero_lt_one hbase.1
  have hEpos : 0 < E := Real.exp_pos _
  refine ⟨j, hcell, fun α hα hlow right r hr θ => ?_⟩
  let Λ := baseEnvelope * (1 + α⁻¹)
  have hfactor : 0 < 1 + α⁻¹ := by positivity
  have hbaseΛ : baseEnvelope ≤ Λ := by
    have hf : 1 ≤ 1 + α⁻¹ := by linarith only [inv_pos.mpr hα]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hbasePos.le
  have hΛ1 : 1 ≤ Λ := hbase.1.trans hbaseΛ
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  have hrecip : 1 / Λ ≤ 1 / baseEnvelope :=
    one_div_le_one_div_of_le hbasePos hbaseΛ
  have hαinv : α⁻¹ ≤ Λ := by
    calc
      α⁻¹ ≤ 1 + α⁻¹ := by linarith
      _ = 1 * (1 + α⁻¹) := (one_mul _).symm
      _ ≤ baseEnvelope * (1 + α⁻¹) :=
        mul_le_mul_of_nonneg_right hbase.1 hfactor.le
  have hsmall : 1 / Λ ≤ α := (one_div_le hΛpos hα).mpr (by
    simpa only [one_div] using hαinv)
  have hlowΛ : N05ComponentOpticalLower D (C.left m) (C.right m) (1 / Λ) := by
    intro x hx
    exact (mul_le_mul_of_nonneg_right hsmall
      (le_min (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))).trans (hlow x hx)
  have hjetΛ : ∀ x ∈ Icc (C.left m) (C.right m),
      |(-deriv D.w x / (x * D.w x))| ≤ Λ ∧
        |deriv (fun t => -deriv D.w t / (t * D.w t)) x| ≤ Λ ∧
        |deriv (deriv (fun t => -deriv D.w t / (t * D.w t))) x| ≤ Λ := by
    intro x hx
    have hb := hbase.2.2.2.1 x hx
    exact ⟨hb.1.trans hbaseΛ, hb.2.1.trans hbaseΛ, hb.2.2.trans hbaseΛ⟩
  have hweightΛ : ∀ x ∈ Icc (C.left m) (C.right m), 1 / Λ ≤ D.w x ∧ D.w x ≤ Λ := by
    intro x hx
    have hb := hbase.2.2.2.2 x hx
    exact ⟨hrecip.trans hb.1, hb.2.trans hbaseΛ⟩
  have hb := n05_negative_component_first_geometry hD.1 hT hS h m hΛ1
    (hbase.2.1.trans hbaseΛ) (hrecip.trans hbase.2.2.1) hlowΛ hjetΛ hweightΛ right r hr θ
  change n05NegativeReferenceFirstSize S C K
    (if right then (K.cutPair m).2 else (K.cutPair m).1) r θ ≤ 100 * Λ ^ 8 at hb
  have he : 100 * Λ ^ 8 = (100 * B₀ ^ 8) * (1 + α⁻¹) ^ 8 * E ^ (A₀ * 8) := by
    dsimp only [Λ, baseEnvelope]
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hEpos.le A₀ 8]
    ring
  exact hb.trans_eq he

/-- The sufficient optical lower certificate is expressed in the actual
carrier cell. It is deliberately separate from every frozen N05 predicate. -/
def N05ActualCarrierOpticalLower (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) : Prop :=
  ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ (m j : ℕ),
    Ioo (C.left m) (C.right m) ⊆ D.cells j →
      N05ComponentOpticalLower D (C.left m) (C.right m)
        ((B * radialE (D.cellIndex j) ^ A)⁻¹)

/-- With the explicit optical certificate, all five first-geometry
coefficients have one fixed power of the actual physical-cell scale.
No estimate is transported to an unrelated canonical enumeration tag. -/
theorem n05_negative_reference_first_geometry_of_actualCarrierLower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hoptical : N05ActualCarrierOpticalLower D C) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m : ℕ, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ (right : Bool) (r : ℝ),
        r ∈ Icc
          (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
          (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) →
        ∀ θ : ℝ,
        n05NegativeReferenceFirstSize S C K
          (if right then (K.cutPair m).2 else (K.cutPair m).1) r θ ≤
            B * radialE (D.cellIndex j) ^ A := by
  obtain ⟨B₀, A₀, hB₀, hA₀, hlow⟩ := hoptical
  obtain ⟨B₁, A₁, hB₁, hA₁, hb⟩ :=
    n05_negative_component_first_bound_of_opticalLower hD hT hS h
  refine ⟨B₁ * (1 + B₀) ^ 8, A₁ + A₀ * 8, by positivity, by positivity, fun m => ?_⟩
  obtain ⟨j, hcell, hbound⟩ := hb m
  let E := radialE (D.cellIndex j)
  let α := (B₀ * E ^ A₀)⁻¹
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (radialQ_nonneg _)
  have hα : 0 < α := inv_pos.mpr (mul_pos hB₀ (Real.rpow_pos_of_pos hEpos _))
  have hEA : 1 ≤ E ^ A₀ := Real.one_le_rpow hE1 hA₀
  have hfactor : 1 + α⁻¹ ≤ (1 + B₀) * E ^ A₀ := by
    dsimp only [α]
    rw [inv_inv]
    nlinarith only [hEA]
  have hfactor8 : (1 + α⁻¹) ^ 8 ≤ ((1 + B₀) * E ^ A₀) ^ 8 :=
    pow_le_pow_left₀ (by positivity) hfactor 8
  refine ⟨j, hcell, fun right r hr θ => ?_⟩
  calc
    n05NegativeReferenceFirstSize S C K
        (if right then (K.cutPair m).2 else (K.cutPair m).1) r θ ≤
        B₁ * (1 + α⁻¹) ^ 8 * E ^ A₁ :=
      hbound α hα (hlow m j hcell) right r hr θ
    _ ≤ B₁ * ((1 + B₀) * E ^ A₀) ^ 8 * E ^ A₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor8 hB₁.le)
        (Real.rpow_nonneg hEpos.le _)
    _ = (B₁ * (1 + B₀) ^ 8) * E ^ (A₁ + A₀ * 8) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hEpos.le A₀ 8,
        Real.rpow_add hEpos]
      ring

end ContinuousFlexibility.Statements
