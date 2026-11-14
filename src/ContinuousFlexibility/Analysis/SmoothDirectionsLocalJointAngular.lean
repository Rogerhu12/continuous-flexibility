module

public import ContinuousFlexibility.Analysis.SmoothDirectionsLocalAngularJets
public import ContinuousFlexibility.Analysis.AngularJetExpansion
public import ContinuousFlexibility.Analysis.ScalarPlaneJetRegularity

/-!
# Joint towers on an open spatial interval

A spatial variable can be added to the actual parameter space without
extending the spatial smoothness through either endpoint. Uniform scalar
jet bounds give joint continuity, and the local spatial FTC gives the
mixed derivatives entering the finite multilinear expansion.
-/

@[expose] public section

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

private theorem continuousOn_joint_of_equicontinuous_local_slices
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {V : Set X} {W : Set Y} {F : Y → X → ℝ}
    (hV : IsOpen V) (hW : IsOpen W)
    (heq : EquicontinuousOn (fun y : W => F y) V)
    (hpoint : ∀ x ∈ V, ContinuousOn (fun y => F y x) W) :
    ContinuousOn (fun p : Y × X => F p.1 p.2) (W ×ˢ V) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have heqAt : EquicontinuousAt (fun y : W => F y) p.2 := by
    simpa only [EquicontinuousWithinAt, EquicontinuousAt,
      nhdsWithin_eq_nhds.mpr (hV.mem_nhds hp.2)] using heq p.2 hp.2
  have hX := Metric.equicontinuousAt_iff_right.mp heqAt (ε / 2) (by positivity)
  have hY : ∀ᶠ y in 𝓝 p.1, dist (F y p.2) (F p.1 p.2) < ε / 2 :=
    ((hpoint p.2 hp.2).continuousAt (hW.mem_nhds hp.1)).eventually
      (Metric.ball_mem_nhds _ (by positivity))
  have hX' : ∀ᶠ q : Y × X in 𝓝 p,
      ∀ y : W, dist (F y p.2) (F y q.2) < ε / 2 :=
    continuous_snd.continuousAt.eventually hX
  have hY' : ∀ᶠ q : Y × X in 𝓝 p,
      dist (F q.1 p.2) (F p.1 p.2) < ε / 2 :=
    continuous_fst.continuousAt.eventually hY
  have hW' : ∀ᶠ q : Y × X in 𝓝 p, q.1 ∈ W :=
    continuous_fst.continuousAt.eventually (hW.mem_nhds hp.1)
  filter_upwards [hX', hY', hW'] with q hqx hqy hqw
  have hqx' : dist (F q.1 q.2) (F q.1 p.2) < ε / 2 := by
    simpa only [dist_comm] using hqx (⟨q.1, hqw⟩ : W)
  exact (dist_triangle _ (F q.1 p.2) _).trans_lt
    ((add_lt_add hqx' hqy).trans_eq (by ring))

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set ℝ}

theorem localScalarJet_joint_continuousOn_of_uniform_bounds
    {f : ℝ → E → ℝ} (J : ∀ θ, θ ∈ V → SmoothDirections U (f θ))
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hf : ∀ x ∈ U, ContinuousOn (fun θ => f θ x) V)
    (hbound : UniformScalarJetSeminormBounds (fun θ : V => J θ θ.property)) (n : ℕ) :
    ContinuousOn (fun p : ℝ × (E × (Fin n → E)) =>
      localScalarJet J n p.2.1 p.2.2 p.1) (V ×ˢ (U ×ˢ univ)) := by
  apply continuousOn_joint_of_equicontinuous_local_slices
    (F := fun θ (z : E × (Fin n → E)) => localScalarJet J n z.1 z.2 θ)
    (hU.prod isOpen_univ) hV
  · have heq := equicontinuous_jets_of_uniform_seminorm_bounds
      (fun θ : V => J θ θ.property) hU hc hbound n
    convert heq using 1
    funext θ z
    exact localScalarJet_of_mem J n z.1 z.2 θ.property
  · intro z hz
    exact localScalarJet_continuousOn_of_uniform_bounds J hU hc hf hbound n z.1 hz.1 z.2

/-- The continuous multilinear map underlying the existing local scalar
jet, with the same harmless zero extension outside its spatial domain. -/
def localScalarJetMap {f : ℝ → E → ℝ}
    (J : ∀ θ, θ ∈ V → SmoothDirections U (f θ))
    (n : ℕ) (x : E) (θ : ℝ) : E [×n]→L[ℝ] ℝ := by
  classical
  exact if hθ : θ ∈ V then (J θ hθ).D n x else 0

theorem localScalarJetMap_apply {f : ℝ → E → ℝ}
    (J : ∀ θ, θ ∈ V → SmoothDirections U (f θ))
    (n : ℕ) (x : E) (θ : ℝ) (v : Fin n → E) :
    localScalarJetMap J n x θ v = localScalarJet J n x v θ := by
  classical
  by_cases hθ : θ ∈ V
  · simp only [localScalarJetMap, localScalarJet, dif_pos hθ]
  · simp only [localScalarJetMap, localScalarJet, dif_neg hθ, ContinuousMultilinearMap.zero_apply]

variable {f : ℕ → ℝ → E → ℝ}

theorem localAngularTower_jointLine_hasDerivAt
    (J : ∀ b θ, θ ∈ V → SmoothDirections U (f b θ))
    (hU : IsOpen U) (hV : IsOpen V)
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) =>
        localScalarJet (J b) k p.2.1 p.2.2 p.1) (V ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ, θ ∈ V → ∀ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (localScalarJet (J b) k y v)
        (localScalarJet (J (b + 1)) k y v θ) θ)
    (b k : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ) (hθ : θ ∈ V)
    (v : Fin k → E) (w : E × ℝ) :
    HasDerivAt (fun t : ℝ => localScalarJet (J b) k (x + t • w.1) v (θ + t * w.2))
      (localScalarJet (J b) (k + 1) x (Fin.cons w.1 v) θ +
        w.2 * localScalarJet (J (b + 1)) k x v θ) 0 := by
  let W : Set PolarPoint := {p | x + p.1 • w.1 ∈ U ∧ p.2 ∈ V}
  let F : PolarPoint → ℝ := fun p => localScalarJet (J b) k (x + p.1 • w.1) v p.2
  let a : PolarPoint → ℝ := fun p =>
    localScalarJet (J b) (k + 1) (x + p.1 • w.1) (Fin.cons w.1 v) p.2
  let c : PolarPoint → ℝ := fun p => localScalarJet (J (b + 1)) k (x + p.1 • w.1) v p.2
  have hW : IsOpen W :=
    (hU.preimage (continuous_const.add (continuous_fst.smul continuous_const))).inter
      (hV.preimage continuous_snd)
  have ha : ContinuousOn a W := by
    have hmap : Continuous (fun p : PolarPoint =>
        (p.2, (x + p.1 • w.1, Fin.cons (α := fun _ : Fin (k + 1) => E) w.1 v))) :=
      continuous_snd.prodMk
        ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk
          (continuous_const : Continuous (fun _ : PolarPoint =>
            Fin.cons (α := fun _ : Fin (k + 1) => E) w.1 v)))
    exact (hjoint (k + 1) b).comp hmap.continuousOn
      (fun p hp => ⟨hp.2, hp.1, mem_univ _⟩)
  have hc : ContinuousOn c W := by
    have hmap : Continuous (fun p : PolarPoint => (p.2, (x + p.1 • w.1, v))) :=
      continuous_snd.prodMk
        ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk
          (continuous_const : Continuous (fun _ : PolarPoint => v)))
    exact (hjoint k (b + 1)).comp hmap.continuousOn
      (fun p hp => ⟨hp.2, hp.1, mem_univ _⟩)
  have hfirst (p : PolarPoint) (hp : p ∈ W) :
      HasDerivAt (fun t => F (t, p.2)) (a p) p.1 := by
    simpa only [F, a, localScalarJet, dif_pos hp.2] using
      (J b p.2 hp.2).hasDerivAt_line_jet x w.1 k v hp.1
  have hsecond (p : PolarPoint) (hp : p ∈ W) :
      HasDerivAt (fun t => F (p.1, t)) (c p) p.2 :=
    hangular k b p.2 hp.2 (x + p.1 • w.1) hp.1 v
  have hp : (0, θ) ∈ W := by
    change x + (0 : ℝ) • w.1 ∈ U ∧ θ ∈ V
    simpa only [zero_smul, add_zero] using And.intro hx hθ
  have hplane := (scalarPlane_hasStrictFDerivAt_of_partials hW ha hc hfirst hsecond hp).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ + t * w.2)) (1, w.2) 0 := by
    simpa only [one_mul, id_eq] using
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

def localAngularTowerJointDirections
    (J : ∀ b θ, θ ∈ V → SmoothDirections U (f b θ))
    (hU : IsOpen U) (hV : IsOpen V)
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) =>
        localScalarJet (J b) k p.2.1 p.2.2 p.1) (V ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ, θ ∈ V → ∀ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (localScalarJet (J b) k y v)
        (localScalarJet (J (b + 1)) k y v θ) θ) :
    SmoothDirections (U ×ˢ V) (fun z : E × ℝ => f 0 z.2 z.1) where
  open_domain := hU.prod hV
  D n z := scalarAngularContinuousExpansion (fun b k => localScalarJetMap (J b) k z.1 z.2) n
  zero z hz := by
    rw [scalarAngularContinuousExpansion_apply, scalarAngularExpansion_zero_apply]
    change localScalarJetMap (J 0) 0 z.1 z.2 Fin.elim0 = _
    rw [localScalarJetMap_apply, localScalarJet_of_mem (J 0) 0 z.1 Fin.elim0 hz.2]
    exact (J 0 z.2 hz.2).zero z.1 hz.1
  continuous n := by
    simp only [scalarAngularContinuousExpansion_apply]
    apply continuousOn_scalarAngularExpansion n
      (fun z : E × ℝ => fun b k => (localScalarJetMap (J b) k z.1 z.2).toMultilinearMap)
    intro b k
    have hmap : Continuous (fun p : (E × ℝ) × (Fin k → E) =>
        (p.1.2, (p.1.1, p.2))) :=
      continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd)
    have h : ContinuousOn
        (fun p : (E × ℝ) × (Fin k → E) =>
          localScalarJet (J b) k p.1.1 p.2 p.1.2) ((U ×ˢ V) ×ˢ univ) :=
      (hjoint k b).comp hmap.continuousOn
        (fun p hp => ⟨hp.1.2, hp.1.1, mem_univ _⟩)
    convert h using 1
    funext p
    exact localScalarJetMap_apply (J b) k p.1.1 p.1.2 p.2
  derivative n z hz v w := by
    let A : ScalarAngularJetData E := fun b k =>
      (localScalarJetMap (J b) k z.1 z.2).toMultilinearMap
    let B : ScalarAngularJetData E := scalarAngularHead A w + w.2 • scalarAngularShift A
    let C : ℝ → ScalarAngularJetData E := fun t b k =>
      (localScalarJetMap (J b) k (z.1 + t • w.1) (z.2 + t * w.2)).toMultilinearMap
    have hC (b k : ℕ) (vs : Fin k → E) :
        HasDerivAt (fun t => C t b k vs) (B b k vs) 0 := by
      have heqC (t : ℝ) : C t b k vs =
          localScalarJet (J b) k (z.1 + t • w.1) vs (z.2 + t * w.2) :=
        localScalarJetMap_apply (J b) k _ _ vs
      have heqB : B b k vs = localScalarJet (J b) (k + 1) z.1 (Fin.cons w.1 vs) z.2 +
          w.2 * localScalarJet (J (b + 1)) k z.1 vs z.2 := by
        change (localScalarJetMap (J b) (k + 1) z.1 z.2) (Fin.cons w.1 vs) +
          w.2 * (localScalarJetMap (J (b + 1)) k z.1 z.2) vs = _
        rw [localScalarJetMap_apply, localScalarJetMap_apply]
      simp only [heqC, heqB]
      exact localAngularTower_jointLine_hasDerivAt J hU hV hjoint hangular
        b k z.1 hz.1 z.2 hz.2 vs w
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

theorem localAngularTowerJointDirections_apply
    (J : ∀ b θ, θ ∈ V → SmoothDirections U (f b θ))
    (hU : IsOpen U) (hV : IsOpen V)
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) =>
        localScalarJet (J b) k p.2.1 p.2.2 p.1) (V ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ, θ ∈ V → ∀ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (localScalarJet (J b) k y v)
        (localScalarJet (J (b + 1)) k y v θ) θ)
    (n : ℕ) (z : E × ℝ) (v : Fin n → E × ℝ) :
    (localAngularTowerJointDirections J hU hV hjoint hangular).D n z v =
      scalarAngularExpansion n
        (fun b k => (localScalarJetMap (J b) k z.1 z.2).toMultilinearMap) v := rfl

/-- A genuine joint tower obtained directly from the original scalar
functions, their first spatial derivatives, and uniform seminorm bounds. -/
def localAngularTowerJointDirectionsOfUniform
    (J : ∀ b θ, θ ∈ V → SmoothDirections U (f b θ))
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hf : ∀ b x, x ∈ U → ContinuousOn (fun θ => f b θ x) V)
    (hbound : ∀ b, UniformScalarJetSeminormBounds (fun θ : V => J b θ θ.property))
    (hderiv : ∀ b θ, θ ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun t => f b t x) (f (b + 1) θ x) θ) :
    SmoothDirections (U ×ˢ V) (fun z : E × ℝ => f 0 z.2 z.1) := by
  have hlocal (b : ℕ) : LocalUniformScalarJetSeminormBounds (J b) :=
    fun θ hθ => ⟨V, subset_rfl, hV, hθ, hbound b⟩
  exact localAngularTowerJointDirections J hU hV
    (fun k b => localScalarJet_joint_continuousOn_of_uniform_bounds
      (J b) hU hc hV (hf b) (hbound b) k)
    (fun k b θ hθ x hx v => localScalarJet_hasDerivAt_along (J b) (J (b + 1))
      hU hc (hf b) (hf (b + 1)) (hlocal b) (hlocal (b + 1))
      (fun t => t) continuous_id (fun t ht y hy => hderiv b t ht y hy)
      k hθ x hx v)

end ContinuousFlexibility.Analysis
