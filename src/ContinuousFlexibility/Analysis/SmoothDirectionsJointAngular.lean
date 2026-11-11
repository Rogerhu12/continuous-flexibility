import ContinuousFlexibility.Analysis.AngularJetExpansion
import ContinuousFlexibility.Analysis.ScalarPlaneJetRegularity

/-!
# Genuine joint parameter and angular directional towers

The angular hierarchy of genuine parameter jets determines a genuine
directional tower on the product with the angle. The construction uses
finite multilinear expansions and ordinary calculus on each parameter
line crossed with the angular coordinate. No norm is placed on the
original parameter space.
-/

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : ℕ → ℝ → E → ℝ}

/-- The actual derivative when the parameter and angle move together. -/
theorem angularTower_jointLine_hasDerivAt
    (J : ∀ b θ, SmoothDirections U (f b θ))
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) => (J b p.1).D k p.2.1 p.2.2)
        (univ ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (fun ψ => (J b ψ).D k y v) ((J (b + 1) θ).D k y v) θ)
    (b k : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ)
    (v : Fin k → E) (w : E × ℝ) :
    HasDerivAt (fun t : ℝ => (J b (θ + t * w.2)).D k (x + t • w.1) v)
      ((J b θ).D (k + 1) x (Fin.cons w.1 v) +
        w.2 * (J (b + 1) θ).D k x v) 0 := by
  let V : Set PolarPoint := {p | x + p.1 • w.1 ∈ U}
  let F : PolarPoint → ℝ := fun p => (J b p.2).D k (x + p.1 • w.1) v
  let a : PolarPoint → ℝ := fun p =>
    (J b p.2).D (k + 1) (x + p.1 • w.1) (Fin.cons w.1 v)
  let c : PolarPoint → ℝ := fun p => (J (b + 1) p.2).D k (x + p.1 • w.1) v
  have hV : IsOpen V := (J 0 0).open_domain.preimage
    (continuous_const.add (continuous_fst.smul continuous_const))
  have ha : ContinuousOn a V := by
    have hmap : Continuous (fun p : PolarPoint =>
        (p.2, (x + p.1 • w.1, (Fin.cons w.1 v : Fin (k + 1) → E)))) :=
      continuous_snd.prodMk
        ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk
          (continuous_const (y := (Fin.cons w.1 v : Fin (k + 1) → E))))
    exact (hjoint (k + 1) b).comp hmap.continuousOn
      (fun p hp => ⟨mem_univ _, hp, mem_univ _⟩)
  have hc : ContinuousOn c V := by
    have hmap : Continuous (fun p : PolarPoint => (p.2, (x + p.1 • w.1, v))) :=
      continuous_snd.prodMk
        ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk continuous_const)
    exact (hjoint k (b + 1)).comp hmap.continuousOn
      (fun p hp => ⟨mem_univ _, hp, mem_univ _⟩)
  have hfirst (p : PolarPoint) (hp : p ∈ V) :
      HasDerivAt (fun t => F (t, p.2)) (a p) p.1 :=
    (J b p.2).hasDerivAt_line_jet x w.1 k v hp
  have hsecond (p : PolarPoint) (hp : p ∈ V) :
      HasDerivAt (fun t => F (p.1, t)) (c p) p.2 :=
    hangular k b p.2 (x + p.1 • w.1) hp v
  have hp : (0, θ) ∈ V := by
    change x + (0 : ℝ) • w.1 ∈ U
    simpa only [zero_smul, add_zero] using hx
  have hplane := (scalarPlane_hasStrictFDerivAt_of_partials hV ha hc hfirst hsecond hp).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ + t * w.2)) (1, w.2) 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (0 : ℝ)).prodMk (((hasDerivAt_id (0 : ℝ)).mul_const w.2).const_add θ)
  have hplane' : HasFDerivAt F
      (a (0, θ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        c (0, θ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((fun t : ℝ => (t, θ + t * w.2)) 0) := by
    simpa only [zero_mul, add_zero] using hplane
  have hd := hplane'.comp_hasDerivAt (0 : ℝ) hcurve
  have he : (a (0, θ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        c (0, θ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, w.2) =
      a (0, θ) + w.2 * c (0, θ) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one]
    ring
  rw [he] at hd
  simpa only [Function.comp_def, F, a, c, zero_smul, add_zero] using hd

/-- Actual joint jets, with each new parameter direction inserted first. -/
def angularTowerJointDirections
    (J : ∀ b θ, SmoothDirections U (f b θ))
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) => (J b p.1).D k p.2.1 p.2.2)
        (univ ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (fun ψ => (J b ψ).D k y v) ((J (b + 1) θ).D k y v) θ) :
    SmoothDirections (U ×ˢ univ) (fun z : E × ℝ => f 0 z.2 z.1) where
  open_domain := (J 0 0).open_domain.prod isOpen_univ
  D n z := scalarAngularContinuousExpansion (fun b k => (J b z.2).D k z.1) n
  zero z hz := (J 0 z.2).zero z.1 hz.1
  continuous n := by
    simp only [scalarAngularContinuousExpansion_apply]
    apply continuousOn_scalarAngularExpansion n
      (fun z : E × ℝ => fun b k => ((J b z.2).D k z.1).toMultilinearMap)
    intro b k
    have hmap : Continuous (fun p : (E × ℝ) × (Fin k → E) =>
        (p.1.2, (p.1.1, p.2))) :=
      continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd)
    simpa only [ContinuousMultilinearMap.coe_coe, Function.comp_def] using
      (hjoint k b).comp hmap.continuousOn
        (fun p hp => ⟨mem_univ _, hp.1.1, mem_univ _⟩)
  derivative n z hz v w := by
    let A : ScalarAngularJetData E := fun b k => ((J b z.2).D k z.1).toMultilinearMap
    let B : ScalarAngularJetData E := scalarAngularHead A w + w.2 • scalarAngularShift A
    let C : ℝ → ScalarAngularJetData E := fun t b k =>
      ((J b (z.2 + t * w.2)).D k (z.1 + t • w.1)).toMultilinearMap
    have hC (b k : ℕ) (vs : Fin k → E) :
        HasDerivAt (fun t => C t b k vs) (B b k vs) 0 := by
      simpa only [C, B, A, Pi.add_apply, Pi.smul_apply,
        MultilinearMap.add_apply, MultilinearMap.smul_apply,
        scalarAngularHead_apply, scalarAngularShift_apply, smul_eq_mul,
        ContinuousMultilinearMap.coe_coe] using
        angularTower_jointLine_hasDerivAt J hjoint hangular b k z.1 hz.1 z.2 vs w
    have hd := hasDerivAt_scalarAngularExpansion n C B hC v
    have he : scalarAngularExpansion n B v =
        scalarAngularExpansion (n + 1) A (Fin.cons w v) := by
      rw [scalarAngularExpansion_succ_apply]
      simp only [B, map_add, map_smul, MultilinearMap.add_apply,
        MultilinearMap.smul_apply, Fin.cons_zero, Fin.tail_cons, smul_eq_mul]
    rw [he] at hd
    change HasProjectiveCurveDerivAt
      (fun t : ℝ => scalarAngularExpansion n (C t) v)
      (scalarAngularExpansion (n + 1) A (Fin.cons w v)) 0
    simpa only [HasProjectiveCurveDerivAt, smul_eq_mul] using
      hasDerivAt_iff_tendsto_slope_zero.mp hd

theorem angularTowerJointDirections_apply
    (J : ∀ b θ, SmoothDirections U (f b θ))
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) => (J b p.1).D k p.2.1 p.2.2)
        (univ ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (fun ψ => (J b ψ).D k y v) ((J (b + 1) θ).D k y v) θ)
    (n : ℕ) (z : E × ℝ) (v : Fin n → E × ℝ) :
    (angularTowerJointDirections J hjoint hangular).D n z v =
      scalarAngularExpansion n (fun b k => ((J b z.2).D k z.1).toMultilinearMap) v := rfl

end ContinuousFlexibility.Analysis
