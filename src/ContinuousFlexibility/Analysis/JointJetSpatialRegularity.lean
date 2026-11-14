module

public import ContinuousFlexibility.Analysis.SmoothDirectionsFixedLast
public import ContinuousFlexibility.Analysis.ScalarPlaneJetRegularity
public import ContinuousFlexibility.Analysis.MixedDerivativeLocality
public import ContinuousFlexibility.Analysis.MixedDerivativeHierarchy
public import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Spatial regularity of the actual joint directional jets

A genuine tower on the parameter and spatial variables already supplies
the continuous first partial derivatives of every fixed jet. Finite
induction yields spatial smoothness without an extra regularity
assumption. Fixing one spatial direction in the last slot gives the
same derivatives while preserving the order of the parameter inputs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}

def _root_.ContinuousFlexibility.Statements.SmoothDirections.freezeSpatial (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (p : PolarPoint) (hp : p ∈ V) :
    SmoothDirections U (fun x => f (x, p)) := by
  let L : E →L[ℝ] E × PolarPoint :=
    (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] PolarPoint)
  have hmap : MapsTo (fun x => (0, p) + L x) U (U ×ˢ V) := by
    intro x hx
    change (0 + x, p + 0) ∈ U ×ˢ V
    simpa only [zero_add, add_zero] using
      (show (x, p) ∈ U ×ˢ V from ⟨hx, hp⟩)
  exact (J.compAffine L (0, p) hU hmap).congrOn (fun x _ => by
    change f (0 + x, p + 0) = f (x, p)
    rw [zero_add, add_zero])

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.freezeSpatial_apply (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (p : PolarPoint) (hp : p ∈ V)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (J.freezeSpatial hU p hp).D n x v = J.D n (x, p) (fun i => (v i, 0)) := by
  change J.D n (0 + x, p + 0) (fun i => (v i, 0)) = _
  rw [zero_add, add_zero]

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.pointTower_eq_jointJet
    (J : SmoothDirections (U ×ˢ V) f) (hU : IsOpen U)
    (p : PolarPoint) (hp : p ∈ V) (K : SmoothDirections U (fun x => f (x, p)))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = J.D n (x, p) (fun i => (v i, 0)) := by
  rw [K.unique (J.freezeSpatial hU p hp) n x hx]
  exact J.freezeSpatial_apply hU p hp n x v

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_spatial_continuousOn
    (J : SmoothDirections (U ×ˢ V) f) (n : ℕ) (x : E) (hx : x ∈ U)
    (v : Fin n → E × PolarPoint) :
    ContinuousOn (fun p => J.D n (x, p) v) V := by
  have hmap : Continuous (fun p : PolarPoint => ((x, p), v)) :=
    (continuous_const.prodMk continuous_id).prodMk continuous_const
  simpa only [Function.comp_def] using
    (J.continuous n).comp hmap.continuousOn (fun p hp => ⟨⟨hx, hp⟩, mem_univ _⟩)

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_spatial_hasDerivAt_fst
    (J : SmoothDirections (U ×ˢ V) f) (n : ℕ) (x : E) (hx : x ∈ U)
    (v : Fin n → E × PolarPoint) {p : PolarPoint} (hp : p ∈ V) :
    HasDerivAt (fun r => J.D n (x, (r, p.2)) v)
      (J.D (n + 1) (x, p) (Fin.cons (0, (1, 0)) v)) p.1 := by
  have hline (t : ℝ) : (x, ((0 : ℝ), p.2)) + t • (0, ((1 : ℝ), 0)) =
      (x, (t, p.2)) := by
    ext <;> simp [smul_eq_mul]
  have hmem : (x, ((0 : ℝ), p.2)) + p.1 • (0, ((1 : ℝ), 0)) ∈ U ×ˢ V := by
    rw [hline]
    exact ⟨hx, hp⟩
  simpa only [hline, Prod.mk.eta] using J.hasDerivAt_line_jet
    (x, ((0 : ℝ), p.2)) (0, ((1 : ℝ), 0)) n v hmem

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_spatial_hasDerivAt_snd
    (J : SmoothDirections (U ×ˢ V) f) (n : ℕ) (x : E) (hx : x ∈ U)
    (v : Fin n → E × PolarPoint) {p : PolarPoint} (hp : p ∈ V) :
    HasDerivAt (fun θ => J.D n (x, (p.1, θ)) v)
      (J.D (n + 1) (x, p) (Fin.cons (0, (0, 1)) v)) p.2 := by
  have hline (t : ℝ) : (x, (p.1, (0 : ℝ))) + t • (0, ((0 : ℝ), 1)) =
      (x, (p.1, t)) := by
    ext <;> simp [smul_eq_mul]
  have hmem : (x, (p.1, (0 : ℝ))) + p.2 • (0, ((0 : ℝ), 1)) ∈ U ×ˢ V := by
    rw [hline]
    exact ⟨hx, hp⟩
  simpa only [hline, Prod.mk.eta] using J.hasDerivAt_line_jet
    (x, (p.1, (0 : ℝ))) (0, ((0 : ℝ), 1)) n v hmem

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_spatial_contDiffOn
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E × PolarPoint) :
    ContDiffOn ℝ ∞ (fun p => J.D n (x, p) v) V := by
  have hfinite : ∀ k n : ℕ, ∀ v : Fin n → E × PolarPoint,
      ContDiffOn ℝ k (fun p => J.D n (x, p) v) V := by
    intro k
    induction k with
    | zero =>
        intro n v
        exact contDiffOn_zero.mpr (J.jointJet_spatial_continuousOn n x hx v)
    | succ k ih =>
        intro n v p hp
        let a : PolarPoint → ℝ := fun q => J.D (n + 1) (x, q) (Fin.cons (0, (1, 0)) v)
        let b : PolarPoint → ℝ := fun q => J.D (n + 1) (x, q) (Fin.cons (0, (0, 1)) v)
        have ha : ContDiffOn ℝ k a V := ih (n + 1) (Fin.cons (0, (1, 0)) v)
        have hb : ContDiffOn ℝ k b V := ih (n + 1) (Fin.cons (0, (0, 1)) v)
        have hd (q : PolarPoint) (hq : q ∈ V) :
            HasFDerivAt (fun r => J.D n (x, r) v)
              (a q • ContinuousLinearMap.fst ℝ ℝ ℝ +
                b q • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
          (scalarPlane_hasStrictFDerivAt_of_partials hV ha.continuousOn hb.continuousOn
            (fun r hr => J.jointJet_spatial_hasDerivAt_fst n x hx v hr)
            (fun r hr => J.jointJet_spatial_hasDerivAt_snd n x hx v hr) hq).hasFDerivAt
        apply ContDiffAt.contDiffWithinAt
        apply contDiffAt_succ_iff_hasFDerivAt.mpr
        refine ⟨fun q => a q • ContinuousLinearMap.fst ℝ ℝ ℝ +
          b q • ContinuousLinearMap.snd ℝ ℝ ℝ,
          ⟨V, hV.mem_nhds hp, hd⟩, ?_⟩
        exact ((ha.contDiffAt (hV.mem_nhds hp)).smul contDiffAt_const).add
          ((hb.contDiffAt (hV.mem_nhds hp)).smul contDiffAt_const)
  intro p hp
  exact (contDiffAt_infty.mpr (fun k =>
    (hfinite k n v).contDiffAt (hV.mem_nhds hp))).contDiffWithinAt

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_radialPartial_eq_fixedLast
    (J : SmoothDirections (U ×ˢ V) f) (hc : Convex ℝ (U ×ˢ V))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E × PolarPoint)
    {p : PolarPoint} (hp : p ∈ V) :
    ContinuousFlexibility.radialPartial (fun q => J.D n (x, q) v) p =
      (J.fixedLast (0, (1, 0))).D n (x, p) v := by
  rw [J.fixedLast_eq_cons hc _ n (x, p) ⟨hx, hp⟩ v]
  have hV : IsOpen V := by
    have heq : (fun q : PolarPoint => (x, q)) ⁻¹' (U ×ˢ V) = V := by
      ext q
      simp only [mem_preimage, mem_prod, hx, true_and]
    rw [← heq]
    exact J.open_domain.preimage (continuous_const.prodMk continuous_id)
  have hd := ((J.jointJet_spatial_contDiffOn hV n x hx v).contDiffAt
    (hV.mem_nhds hp)).differentiableAt (by simp)
  exact (hasDerivAt_radial_slice_of_differentiableAt hd).unique
    (J.jointJet_spatial_hasDerivAt_fst n x hx v hp)

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_angularPartial_eq_fixedLast
    (J : SmoothDirections (U ×ˢ V) f) (hc : Convex ℝ (U ×ˢ V))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E × PolarPoint)
    {p : PolarPoint} (hp : p ∈ V) :
    ContinuousFlexibility.angularPartial (fun q => J.D n (x, q) v) p =
      (J.fixedLast (0, (0, 1))).D n (x, p) v := by
  rw [J.fixedLast_eq_cons hc _ n (x, p) ⟨hx, hp⟩ v]
  have hV : IsOpen V := by
    have heq : (fun q : PolarPoint => (x, q)) ⁻¹' (U ×ˢ V) = V := by
      ext q
      simp only [mem_preimage, mem_prod, hx, true_and]
    rw [← heq]
    exact J.open_domain.preimage (continuous_const.prodMk continuous_id)
  have hd := ((J.jointJet_spatial_contDiffOn hV n x hx v).contDiffAt
    (hV.mem_nhds hp)).differentiableAt (by simp)
  exact (hasDerivAt_angular_slice_of_differentiableAt hd).unique
    (J.jointJet_spatial_hasDerivAt_snd n x hx v hp)

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_mixed_radial_step
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E × PolarPoint)
    {p : PolarPoint} (hp : p ∈ V) :
    mixedDerivative (a + 1) b (fun q => J.D n (x, q) v) p =
      mixedDerivative a b (fun q => (J.fixedLast (0, (1, 0))).D n (x, q) v) p := by
  rw [← mixedDerivative_radialPartial hV (J.jointJet_spatial_contDiffOn hV n x hx v) a b hp]
  exact mixedDerivative_congr_on_open hV
    (fun q hq => J.jointJet_radialPartial_eq_fixedLast hc n x hx v hq) a b hp

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_mixed_angular_step
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E × PolarPoint)
    {p : PolarPoint} (hp : p ∈ V) :
    mixedDerivative a (b + 1) (fun q => J.D n (x, q) v) p =
      mixedDerivative a b (fun q => (J.fixedLast (0, (0, 1))).D n (x, q) v) p := by
  rw [← mixedDerivative_angularPartial hV (J.jointJet_spatial_contDiffOn hV n x hx v) a b hp]
  exact mixedDerivative_congr_on_open hV
    (fun q hq => J.jointJet_angularPartial_eq_fixedLast hc n x hx v hq) a b hp

private theorem jointJet_mixed_line_by_order
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V)) :
    ∀ k : ℕ, ∀ f : E × PolarPoint → ℝ, ∀ J : SmoothDirections (U ×ˢ V) f,
    ∀ a b : ℕ, a + b ≤ k → ∀ n : ℕ, ∀ x w : E, ∀ t : ℝ,
    x + t • w ∈ U → ∀ v : Fin n → E × PolarPoint, ∀ p : PolarPoint, p ∈ V →
      HasDerivAt (fun s => mixedDerivative a b (fun q => J.D n (x + s • w, q) v) p)
        (mixedDerivative a b (fun q => J.D (n + 1) (x + t • w, q)
          (Fin.cons (w, 0) v)) p) t := by
  have hzero (f : E × PolarPoint → ℝ) (J : SmoothDirections (U ×ˢ V) f)
      (n : ℕ) (x w : E) (t : ℝ) (ht : x + t • w ∈ U)
      (v : Fin n → E × PolarPoint) (p : PolarPoint) (hp : p ∈ V) :
      HasDerivAt (fun s => mixedDerivative 0 0 (fun q => J.D n (x + s • w, q) v) p)
        (mixedDerivative 0 0 (fun q => J.D (n + 1) (x + t • w, q)
          (Fin.cons (w, 0) v)) p) t := by
    have heq (s : ℝ) : (x, p) + s • (w, (0 : PolarPoint)) = (x + s • w, p) := by
      ext <;> simp
    have hmem : (x, p) + t • (w, (0 : PolarPoint)) ∈ U ×ˢ V := by
      rw [heq]
      exact ⟨ht, hp⟩
    simpa only [mixedDerivative, iteratedDeriv_zero, heq] using
      J.hasDerivAt_line_jet (x, p) (w, (0 : PolarPoint)) n v hmem
  intro k
  induction k with
  | zero =>
      intro f J a b hab n x w t ht v p hp
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      exact hzero f J n x w t ht v p hp
  | succ k ih =>
      intro f J a b hab n x w t ht v p hp
      have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
          (hU.mem_nhds ht)
      cases a with
      | succ a =>
          rw [J.jointJet_mixed_radial_step hV hc a b (n + 1)
            (x + t • w) ht (Fin.cons (w, 0) v) hp]
          apply (ih _ (J.fixedLast (0, (1, 0))) a b (by omega)
            n x w t ht v p hp).congr_of_eventuallyEq
          filter_upwards [hnear] with s hs
          exact J.jointJet_mixed_radial_step hV hc a b n (x + s • w) hs v hp
      | zero =>
          cases b with
          | zero => exact hzero f J n x w t ht v p hp
          | succ b =>
              rw [J.jointJet_mixed_angular_step hV hc 0 b (n + 1)
                (x + t • w) ht (Fin.cons (w, 0) v) hp]
              apply (ih _ (J.fixedLast (0, (0, 1))) 0 b (by omega)
                n x w t ht v p hp).congr_of_eventuallyEq
              filter_upwards [hnear] with s hs
              exact J.jointJet_mixed_angular_step hV hc 0 b n (x + s • w) hs v hp

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.jointJet_mixed_hasDerivAt_line
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b n : ℕ) (x w : E) {t : ℝ} (ht : x + t • w ∈ U)
    (v : Fin n → E × PolarPoint) {p : PolarPoint} (hp : p ∈ V) :
    HasDerivAt (fun s => mixedDerivative a b (fun q => J.D n (x + s • w, q) v) p)
      (mixedDerivative a b (fun q => J.D (n + 1) (x + t • w, q)
        (Fin.cons (w, 0) v)) p) t :=
  jointJet_mixed_line_by_order hU hV hc (a + b) f J a b le_rfl n x w t ht v p hp

end ContinuousFlexibility.Analysis
