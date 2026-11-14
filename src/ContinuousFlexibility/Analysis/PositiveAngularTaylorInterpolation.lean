module

public import ContinuousFlexibility.Analysis.PositiveAngularTaylorPatch

/-!
# A common positive angular interpolation for a family of endpoint jets

The same two disjoint cutoffs handle the endpoints. Their width is
chosen from a uniform bound on finitely many actual boundary jets,
before the family index is selected. The construction is the identity
off the two collars and preserves degree-one lifts and reflection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveAngularTaylorInterpolation (n : ℕ) (l r δ : ℝ)
    (A : Bool → ℕ → ℝ → ℝ) (p : PolarPoint) : ℝ :=
  positiveAngularTaylorPatch n l δ (A false) p +
    positiveAngularTaylorPatch n r δ (A true) p - p.2

theorem contDiff_positiveAngularTaylorInterpolation
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ}
    (hA : ∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j)) (l r δ : ℝ) :
    ContDiff ℝ ∞ (positiveAngularTaylorInterpolation n l r δ A) :=
  ((contDiff_positiveAngularTaylorPatch (hA false) l δ).add
    (contDiff_positiveAngularTaylorPatch (hA true) r δ)).sub contDiff_snd

/-- At either endpoint the opposite cutoff vanishes on a neighborhood.
Thus the actual radial derivatives equal the prescribed data. -/
theorem positiveAngularTaylorInterpolation_radial_germ
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (A : Bool → ℕ → ℝ → ℝ) (side : Bool) (θ : ℝ) :
    (fun x => positiveAngularTaylorInterpolation n l r δ A (x, θ)) =ᶠ[
      𝓝 (if side then r else l)]
      (fun x => boundaryTaylorPolynomial n (if side then r else l) (A side) (x, θ)) := by
  let c : ℝ := if side then r else l
  let d : ℝ := if side then l else r
  have hsep : 0 ≤ r - l := by linarith
  have hcd : δ ≤ |c - d| := by
    cases side with
    | false =>
        change δ ≤ |l - r|
        rw [abs_sub_comm, abs_of_nonneg hsep]
        linarith
    | true =>
        change δ ≤ |r - l|
        rw [abs_of_nonneg hsep]
        linarith
  have hother := positiveEndpointCutoff_zero_germ_of_separation hδ hcd
  filter_upwards [positiveEndpointCutoff_one_germ c δ, hother] with x hx hy
  cases side <;> simp only [c, d, Bool.false_eq_true, ite_false, ite_true] at hx hy ⊢
  <;> simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
    hx, hy, Pi.one_apply, Pi.zero_apply, one_mul, zero_mul, add_zero]
  <;> ring

theorem iteratedDeriv_positiveAngularTaylorInterpolation
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (A : Bool → ℕ → ℝ → ℝ) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => positiveAngularTaylorInterpolation n l r δ A (x, θ))
      (if side then r else l) = A side k θ :=
  ((positiveAngularTaylorInterpolation_radial_germ n hδ hgap A side θ).iteratedDeriv k).eq_of_nhds.trans
    (iteratedDeriv_boundaryTaylorPolynomial n
      (if side then r else l) (A side) hk θ)

/-- Disjointness means that the angular map at a fixed radius is one
of the two individual patches. No radial cutoff derivative occurs. -/
theorem deriv_positiveAngularTaylorInterpolation_lower
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ} {l r δ κ M : ℝ}
    (hA : ∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hgap : 2 * δ ≤ r - l)
    (hκone : κ ≤ 1) (hM : 0 ≤ M)
    (hzero : ∀ side θ, κ ≤ deriv (A side 0) θ)
    (hbound : ∀ side j, 0 < j → j ≤ n → ∀ θ, |deriv (A side j) θ| ≤ M)
    (hsmall : ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2) (x θ : ℝ) :
    κ / 2 ≤ deriv (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η)) θ := by
  by_cases hxL : positiveEndpointCutoff l δ x = 0
  · have he : (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η)) =
        (fun η => positiveAngularTaylorPatch n r δ (A true) (x, η)) := by
      funext η
      simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
        hxL, zero_mul, add_zero]
      ring
    rw [he]
    exact deriv_positiveAngularTaylorPatch_lower (hA true) hδ hδone hκone hM
      (hzero true) (hbound true) hsmall x θ
  · have hxLs : x ∈ tsupport (positiveEndpointCutoff l δ) :=
      subset_tsupport _ (Function.mem_support.mpr hxL)
    have hxRs : x ∉ tsupport (positiveEndpointCutoff r δ) :=
      fun hx => (Set.disjoint_left.mp
        (disjoint_tsupport_positiveEndpointCutoff hδ hgap)) hxLs hx
    have hxR := image_eq_zero_of_notMem_tsupport hxRs
    have he : (fun η => positiveAngularTaylorInterpolation n l r δ A (x, η)) =
        (fun η => positiveAngularTaylorPatch n l δ (A false) (x, η)) := by
      funext η
      simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
        hxR, zero_mul, add_zero]
      ring
    rw [he]
    exact deriv_positiveAngularTaylorPatch_lower (hA false) hδ hδone hκone hM
      (hzero false) (hbound false) hsmall x θ

theorem positiveAngularTaylorInterpolation_eq_angle_of_not_mem_balls
    (n : ℕ) {l r δ x : ℝ} (hδ : 0 < δ) (A : Bool → ℕ → ℝ → ℝ)
    (hxL : x ∉ Metric.ball l δ) (hxR : x ∉ Metric.ball r δ) (θ : ℝ) :
    positiveAngularTaylorInterpolation n l r δ A (x, θ) = θ := by
  rw [positiveAngularTaylorInterpolation,
    positiveAngularTaylorPatch_eq_angle_of_not_mem_ball n hδ (A false) hxL,
    positiveAngularTaylorPatch_eq_angle_of_not_mem_ball n hδ (A true) hxR]
  ring

theorem positiveAngularTaylorInterpolation_period_add
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ} {T : ℝ}
    (hzero : ∀ side θ, A side 0 (θ + T) = A side 0 θ + T)
    (hperiod : ∀ side j, 0 < j → j ≤ n → Function.Periodic (A side j) T)
    (l r δ x θ : ℝ) :
    positiveAngularTaylorInterpolation n l r δ A (x, θ + T) =
      positiveAngularTaylorInterpolation n l r δ A (x, θ) + T := by
  simp only [positiveAngularTaylorInterpolation,
    positiveAngularTaylorPatch_period_add (hzero false) (hperiod false),
    positiveAngularTaylorPatch_period_add (hzero true) (hperiod true)]
  ring

theorem positiveAngularTaylorInterpolation_reflect
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ}
    (hodd : ∀ side j, j ≤ n → ∀ θ, A side j (-θ) = -A side j θ)
    (l r δ x θ : ℝ) :
    positiveAngularTaylorInterpolation n l r δ A (x, -θ) =
      -positiveAngularTaylorInterpolation n l r δ A (x, θ) := by
  simp only [positiveAngularTaylorInterpolation,
    positiveAngularTaylorPatch_reflect (hodd false),
    positiveAngularTaylorPatch_reflect (hodd true)]
  ring

/-- The choice of radius uses only fixed finite-jet constants and the
forbidden set. In particular it precedes every state or family index. -/
theorem exists_positiveAngularTaylor_collar
    {F : Set ℝ} (hF : IsClosed F) {l r ρ κ M : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r) (hρ : 0 < ρ)
    (hκ : 0 < κ) (hM : 0 ≤ M) (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧
      Disjoint (Metric.ball l δ) F ∧ Disjoint (Metric.ball r δ) F ∧
      ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2 := by
  let C : ℝ := ((n + 1 : ℕ) : ℝ) * (M + 1)
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hC : 0 < C := mul_pos hn (by linarith)
  have hε : 0 < min ρ (min 1 (κ / (2 * C))) :=
    lt_min hρ (lt_min zero_lt_one (div_pos hκ (by positivity)))
  obtain ⟨δ, hδ, hδε, hgap, hFL, hFR⟩ :=
    exists_positiveEndpoint_collars_avoiding hF hl hr hlr hε
  have hδρ : δ < ρ := hδε.trans_le (min_le_left _ _)
  have hδone : δ ≤ 1 :=
    (hδε.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδC : δ < κ / (2 * C) :=
    hδε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hprod := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp hδC
  have hcoef : ((n + 1 : ℕ) : ℝ) * M ≤ C :=
    mul_le_mul_of_nonneg_left (by linarith : M ≤ M + 1) hn.le
  have hsmall : ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2 :=
    (mul_le_mul_of_nonneg_right hcoef hδ.le).trans (by nlinarith only [hprod])
  exact ⟨δ, hδ, hδρ, hδone, hgap, hFL, hFR, hsmall⟩

/-- A single radius works for an arbitrary indexed family. The hypotheses
are bounds on the given endpoint data, not on the constructed chart. -/
theorem exists_positiveAngularTaylorInterpolation_family
    {ι : Type*} {n : ℕ} {A : ι → Bool → ℕ → ℝ → ℝ}
    {F : Set ℝ} (hF : IsClosed F) {l r ρ κ M : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r) (hρ : 0 < ρ)
    (hκ : 0 < κ) (hκone : κ ≤ 1) (hM : 0 ≤ M)
    (hA : ∀ i side j, j ≤ n → ContDiff ℝ ∞ (A i side j))
    (hzero : ∀ i side θ, κ ≤ deriv (A i side 0) θ)
    (hbound : ∀ i side j, 0 < j → j ≤ n → ∀ θ, |deriv (A i side j) θ| ≤ M)
    (hlift : ∀ i side θ, A i side 0 (θ + Real.pi) = A i side 0 θ + Real.pi)
    (hperiod : ∀ i side j, 0 < j → j ≤ n → Function.Periodic (A i side j) Real.pi)
    (hodd : ∀ i side j, j ≤ n → ∀ θ, A i side j (-θ) = -A i side j θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ 2 * δ < r - l ∧
      Disjoint (Metric.ball l δ) F ∧ Disjoint (Metric.ball r δ) F ∧
      ∀ i : ι, let φ := positiveAngularTaylorInterpolation n l r δ (A i);
      ContDiff ℝ ∞ φ ∧
      (∀ x θ, κ / 2 ≤ deriv (fun η => φ (x, η)) θ) ∧
      (∀ side k, k ≤ n → ∀ θ,
        iteratedDeriv k (fun x => φ (x, θ)) (if side then r else l) = A i side k θ) ∧
      (∀ x θ, φ (x, θ + Real.pi) = φ (x, θ) + Real.pi) ∧
      (∀ x θ, φ (x, -θ) = -φ (x, θ)) ∧
      (∀ x ∈ F, ∀ θ, φ (x, θ) = θ) := by
  obtain ⟨δ, hδ, hδρ, hδone, hgap, hFL, hFR, hsmall⟩ :=
    exists_positiveAngularTaylor_collar hF hl hr hlr hρ hκ hM n
  refine ⟨δ, hδ, hδρ, hgap, hFL, hFR, ?_⟩
  intro i
  refine ⟨contDiff_positiveAngularTaylorInterpolation (hA i) l r δ,
    deriv_positiveAngularTaylorInterpolation_lower (hA i) hδ hδone hgap.le
      hκone hM (hzero i) (hbound i) hsmall,
    fun side k hk θ => iteratedDeriv_positiveAngularTaylorInterpolation n hδ hgap.le
      (A i) side hk θ,
    positiveAngularTaylorInterpolation_period_add (hlift i) (hperiod i) l r δ,
    positiveAngularTaylorInterpolation_reflect (hodd i) l r δ, ?_⟩
  intro x hx θ
  exact positiveAngularTaylorInterpolation_eq_angle_of_not_mem_balls n hδ (A i)
    (fun h => Set.disjoint_left.mp hFL h hx) (fun h => Set.disjoint_left.mp hFR h hx) θ

end ContinuousFlexibility.Analysis

