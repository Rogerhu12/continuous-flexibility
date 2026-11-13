import ContinuousFlexibility.Analysis.N04NegativeGeometryImplicitJets
import ContinuousFlexibility.Analysis.N04NegativeGeometryFiniteAffineDirections
import ContinuousFlexibility.Analysis.N01cFiniteAffineJets
import ContinuousFlexibility.Analysis.N04NegativeGeometryPlanarParameterInverse
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
import ContinuousFlexibility.Analysis.TameProductDirections

/-!
# Genuine implicit towers from finite affine inverse germs

The recursively defined implicit jets are identified with the actual
derivatives on every finite affine slice.  The implicit equation kills
the full partition sum; its unique highest block is the spatial
linearization applied to the unknown derivative.  Applying the actual
inverse linearization proves the recursive formula.  Joint evaluation
continuity then supplies a genuine tower on the original parameter
topology.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

namespace N04NegativeGeometryImplicitJet

section Graph

variable {P Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- At the origin, the ordinary graph jets agree with the graph-slot
formula at every order, including the value. -/
theorem iteratedFDeriv_graph_zero {g : P → Y}
    (hg : ContDiffAt ℝ ∞ g 0) (n : ℕ) (v : Fin n → P) :
    iteratedFDeriv ℝ n (fun p => (p, g p)) 0 v =
      graph n (iteratedFDeriv ℝ n g 0) v := by
  have hid : iteratedFDeriv ℝ n (id : P → P) 0 =
      continuousLinearJets (ContinuousLinearMap.id ℝ P) n 0 :=
    ((hasProjectiveJetsOn_continuousLinear (ContinuousLinearMap.id ℝ P) univ).eq_iteratedFDeriv_finiteDimensional
      isOpen_univ n (mem_univ 0)).symm
  change iteratedFDeriv ℝ n (fun p => ((id : P → P) p, g p)) 0 v = _
  rw [iteratedFDeriv_prodMk (contDiffAt_id : ContDiffAt ℝ ∞ (id : P → P) 0)
    hg (by simp)]
  change (iteratedFDeriv ℝ n (id : P → P) 0 v, iteratedFDeriv ℝ n g 0 v) = _
  rw [hid]
  cases n with
  | zero =>
      change ((0 : P), iteratedFDeriv ℝ 0 g 0 v) =
        (0 : P × Y) + (0, iteratedFDeriv ℝ 0 g 0 v)
      rw [zero_add]
  | succ n =>
      cases n with
      | zero =>
          change (v 0, iteratedFDeriv ℝ 1 g 0 v) =
            (v 0, (0 : Y)) + (0, iteratedFDeriv ℝ 1 g 0 v)
          simp only [Prod.mk_add_mk, add_zero, zero_add]
      | succ n =>
          change ((0 : P), iteratedFDeriv ℝ (n + 2) g 0 v) =
            (0 : P × Y) + (0, iteratedFDeriv ℝ (n + 2) g 0 v)
          rw [zero_add]

end Graph

section Identification

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}

/-- The actual implicit equation yields the exact ordered-partition
identity on a finite affine slice of the original parameter space. -/
theorem finiteAffine_partition_sum_zero
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hmap : MapsTo g U V) (hzero : ∀ x ∈ U, H (x, g x) = 0)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (hg : ContDiffAt ℝ ∞ (fun p => g (x + L p)) 0)
    (n : ℕ) (hn : 0 < n) (v : Fin n → P) :
    (∑ c : _root_.OrderedFinpartition n,
      J.D c.length (x, g x)
        (fun i => (L.prodMap (ContinuousLinearMap.id ℝ Y))
          (graph (c.partSize i)
            (iteratedFDeriv ℝ (c.partSize i) (fun p => g (x + L p)) 0)
            (v ∘ c.emb i)))) = 0 := by
  classical
  let M : (P × Y) →L[ℝ] E × Y := L.prodMap (ContinuousLinearMap.id ℝ Y)
  let F : P × Y → Y := fun p => H ((x, (0 : Y)) + M p)
  let G : P → P × Y := fun p => (p, g (x + L p))
  have hG : ContDiffAt ℝ ∞ G 0 := contDiffAt_id.prodMk hg
  have hGzero : G 0 = (0, g x) := by
    simp only [G, map_zero, add_zero]
  have hpoint : (x, (0 : Y)) + M (0, g x) = (x, g x) := by
    change (x, (0 : Y)) + (L 0, g x) = (x, g x)
    simp only [map_zero, Prod.mk_add_mk, add_zero, zero_add]
  have hF : ContDiffAt ℝ ∞ F (G 0) := by
    rw [hGzero]
    apply (smoothDirections_contDiffOn_finiteAffine J (x, (0 : Y)) M).contDiffAt
    have hopen : IsOpen ((fun p : P × Y => (x, (0 : Y)) + M p) ⁻¹' (U ×ˢ V)) :=
      J.open_domain.preimage (continuous_const.add M.continuous)
    apply hopen.mem_nhds
    change (x, (0 : Y)) + M (0, g x) ∈ U ×ˢ V
    rw [hpoint]
    exact ⟨hx, hmap hx⟩
  have heq : F ∘ G =ᶠ[𝓝 (0 : P)] (fun _ => (0 : Y)) := by
    have hcont : ContinuousAt (fun p : P => x + L p) 0 :=
      (continuous_const.add L.continuous).continuousAt
    have ht : Tendsto (fun p : P => x + L p) (𝓝 0) (𝓝 x) := by
      simpa only [map_zero, add_zero] using hcont.tendsto
    have hnear : ∀ᶠ p : P in 𝓝 0, x + L p ∈ U := ht.eventually (hU.mem_nhds hx)
    filter_upwards [hnear] with p hp
    change H (x + L p, (0 : Y) + g (x + L p)) = 0
    rw [zero_add]
    exact hzero (x + L p) hp
  have hformula : iteratedFDeriv ℝ n (F ∘ G) 0 =
      ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length F (G 0))
          (fun i => iteratedFDeriv ℝ (c.partSize i) G 0) :=
    iteratedFDeriv_comp hF hG (by simp : (n : ℕ∞ω) ≤ ∞)
  have hcomp := congrArg (fun A : P [×n]→L[ℝ] Y => A v) hformula
  simp only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply] at hcomp
  have hzeroJet : iteratedFDeriv ℝ n (F ∘ G) 0 v = 0 := by
    rw [(heq.iteratedFDeriv ℝ n).self_of_nhds,
      iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn), ContinuousMultilinearMap.zero_apply]
  rw [hzeroJet] at hcomp
  refine (Finset.sum_congr rfl (fun c _ => ?_)).trans hcomp.symm
  have ho := smoothDirections_iteratedFDeriv_finiteAffine J (x, (0 : Y)) M
    c.length (y := (0, g x))
    (by rw [hpoint]; exact ⟨hx, hmap hx⟩)
    (fun i => iteratedFDeriv ℝ (c.partSize i) G 0 (v ∘ c.emb i))
  rw [hpoint] at ho
  rw [hGzero]
  change _ = iteratedFDeriv ℝ c.length F (0, g x) _
  rw [ho]
  congr 1
  funext i
  congr 1
  exact (iteratedFDeriv_graph_zero hg (c.partSize i) (v ∘ c.emb i)).symm

/-- The continuous multilinear implicit candidates are the actual
ordinary derivatives on every finite affine slice. -/
theorem tower_eq_finiteAffine
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (hleft : ∀ x ∈ U, ∀ y : Y,
      A x (J.D 1 (x, g x) (fun _ : Fin 1 => (0, y))) = y)
    (hzero : ∀ x ∈ U, H (x, g x) = 0)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (hs : ContDiffAt ℝ ∞ (fun p => g (x + L p)) 0)
    (n : ℕ) (v : Fin n → P) :
    iteratedFDeriv ℝ n (fun p => g (x + L p)) 0 v =
      (tower J hg hmap A hA n).value x (fun i => L (v i)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        rw [iteratedFDeriv_zero_apply, tower_zero_apply]
        simp only [map_zero, add_zero]
    | succ n =>
        let M : (P × Y) →L[ℝ] E × Y := L.prodMap (ContinuousLinearMap.id ℝ Y)
        let D : (k : ℕ) → P [×k]→L[ℝ] Y :=
          fun k => iteratedFDeriv ℝ k (fun p => g (x + L p)) 0
        let B : ∀ k : ℕ, k < n + 1 → N04NegativeGeometryImplicitJet U Y k :=
          fun k _ => tower J hg hmap A hA k
        let R : (k : ℕ) → P [×k]→L[ℝ] (E × Y) :=
          fun k => M.compContinuousMultilinearMap (graph k (D k))
        let S : (k : ℕ) → P [×k]→L[ℝ] (E × Y) := fun k =>
          (graph k ((lower B k).value x)).compContinuousLinearMap (fun _ => L)
        have hRS : ∀ k, k < n + 1 → R k = S k := by
          intro k hk
          apply ContinuousMultilinearMap.ext
          intro w
          change M (graph k (D k) w) =
            graph k ((lower B k).value x) (fun i => L (w i))
          rw [lower_of_lt B hk]
          exact graph_natural L k (D k) ((tower J hg hmap A hA k).value x) w
            (ih k hk w)
        have hpart := n04NegativeGeometry_partition_highest_difference
          (Nat.succ_pos n) (fun k => J.D k (x, g x)) R S hRS v
        have hsumR : (∑ c : _root_.OrderedFinpartition (n + 1),
            J.D c.length (x, g x) (fun i => R (c.partSize i) (v ∘ c.emb i))) = 0 :=
          finiteAffine_partition_sum_zero J hU hmap hzero x hx L hs
            (n + 1) (Nat.succ_pos n) v
        have hsumS : (∑ c : _root_.OrderedFinpartition (n + 1),
            J.D c.length (x, g x) (fun i => S (c.partSize i) (v ∘ c.emb i))) =
            forcing J g B x (fun i => L (v i)) := by
          rw [forcing_apply]
          rfl
        have hparam : M (parameter (Y := Y) (n + 1) v) =
            parameter (Y := Y) (n + 1) (fun i => L (v i)) := by
          have h := graph_natural L (n + 1)
            (0 : P [×(n + 1)]→L[ℝ] Y) (0 : E [×(n + 1)]→L[ℝ] Y) v (by simp)
          simpa only [graph_apply, ContinuousMultilinearMap.zero_apply,
            Prod.mk_zero_zero, add_zero] using h
        have hdiff : R (n + 1) v - S (n + 1) v = (0, D (n + 1) v) := by
          change M (graph (n + 1) (D (n + 1)) v) -
            graph (n + 1) ((lower B (n + 1)).value x) (fun i => L (v i)) = _
          rw [lower_self, graph_apply, graph_apply, map_add, hparam]
          change (_ + (L 0, D (n + 1) v)) - (_ + (0, (0 : Y))) = _
          simp only [map_zero, Prod.mk_zero_zero, add_zero, add_sub_cancel_left]
        rw [hsumR, hsumS, hdiff, zero_sub] at hpart
        have hap := congrArg (A x) hpart
        rw [map_neg, hleft x hx] at hap
        rw [tower_succ_apply]
        exact hap.symm

/-- Finite affine implicit germs and the actual inverse linearization
construct a genuine implicit tower on the original topological space. -/
def smoothDirections
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (hleft : ∀ x ∈ U, ∀ y : Y,
      A x (J.D 1 (x, g x) (fun _ : Fin 1 => (0, y))) = y)
    (hzero : ∀ x ∈ U, H (x, g x) = 0)
    (hsmooth : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0) : SmoothDirections U g :=
  n04NegativeGeometry_smoothDirections_of_finiteAffine_germs hU
    (fun n x => (tower J hg hmap A hA n).value x)
    (fun x _ => tower_zero_apply J hg hmap A hA x Fin.elim0)
    (fun n => (tower J hg hmap A hA n).continuous) hsmooth
    (fun m x hx L n v => tower_eq_finiteAffine J hU hg hmap A hA hleft hzero
      x hx L (hsmooth m x hx L) n v)

theorem smoothDirections_D_apply
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (hleft : ∀ x ∈ U, ∀ y : Y,
      A x (J.D 1 (x, g x) (fun _ : Fin 1 => (0, y))) = y)
    (hzero : ∀ x ∈ U, H (x, g x) = 0)
    (hsmooth : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirections J hU hg hmap A hA hleft hzero hsmooth).D n x v =
      (tower J hg hmap A hA n).value x v := rfl

/-- The first spatial differential is extracted from the actual joint
tower, retaining norm continuity in its finite-dimensional domain. -/
def spatialDifferential (J : SmoothDirections (U ×ˢ V) H) (x : E × Y) : Y →L[ℝ] Y :=
  ((ContinuousMultilinearMap.ofSubsingleton ℝ (E × Y) Y (0 : Fin 1)).symm
    (J.D 1 x)).comp (ContinuousLinearMap.inr ℝ E Y)

theorem spatialDifferential_apply (J : SmoothDirections (U ×ˢ V) H)
    (x : E × Y) (y : Y) :
    spatialDifferential J x y = J.D 1 x (fun _ : Fin 1 => (0, y)) := by
  simp only [spatialDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousMultilinearMap.ofSubsingleton_symm_apply_apply]

theorem spatialDifferential_continuousOn (J : SmoothDirections (U ×ˢ V) H) :
    ContinuousOn (spatialDifferential J) (U ×ˢ V) := by
  apply continuousOn_clm_apply.mpr
  intro y
  simp only [spatialDifferential_apply]
  exact (J.continuous 1).comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hx => ⟨hx, mem_univ _⟩)

theorem spatialDifferential_eq_fderiv (J : SmoothDirections (U ×ˢ V) H)
    (x : E × Y) (hx : x ∈ U ×ˢ V) :
    spatialDifferential J x = fderiv ℝ (fun y => H (x.1, y)) x.2 := by
  apply ContinuousLinearMap.ext
  intro y
  rw [spatialDifferential_apply]
  have h := smoothDirections_iteratedFDeriv_finiteAffine J (x.1, (0 : Y))
    (ContinuousLinearMap.inr ℝ E Y) 1 (y := x.2)
    (by simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add, Prod.eta] using hx)
    (fun _ : Fin 1 => y)
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add,
    Prod.eta, iteratedFDeriv_one_apply] using h.symm

/-- An invertible spatial differential supplies its continuous inverse;
the inverse operator is derived rather than supplied as a hypothesis. -/
def smoothDirections_of_invertible
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (hD : ∀ x ∈ U, (fderiv ℝ (fun y => H (x, y)) (g x)).IsInvertible)
    (hzero : ∀ x ∈ U, H (x, g x) = 0)
    (hsmooth : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0) : SmoothDirections U g := by
  let D : E → Y →L[ℝ] Y := fun x => spatialDifferential J (x, g x)
  have hDc : ContinuousOn D U :=
    (spatialDifferential_continuousOn J).comp (continuousOn_id.prodMk hg)
      (fun _ hx => ⟨hx, hmap hx⟩)
  have hDi (x : E) (hx : x ∈ U) : (D x).IsInvertible := by
    dsimp only [D]
    rw [spatialDifferential_eq_fderiv J (x, g x) ⟨hx, hmap hx⟩]
    exact hD x hx
  let A : E → Y →L[ℝ] Y := fun x => (D x).inverse
  have hA : ContinuousOn A U := by
    intro x hx
    exact ((hDi x hx).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      (hDc x hx)
  apply smoothDirections J hU hg hmap A hA (fun x hx y => ?_) hzero hsmooth
  change (D x).inverse _ = y
  rw [← spatialDifferential_apply]
  exact (hDi x hx).inverse_apply_self y

end Identification
end N04NegativeGeometryImplicitJet

section PlanarInverse

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V W : Set PolarPoint} {F G : E × PolarPoint → PolarPoint}

/-- The actual inverse of a planar family has a genuine joint tower in
the original state topology. Smoothness on finite affine slices follows
from the forward tower and the local implicit function theorem. -/
def n04NegativeInverse_jointTower
    (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hG : ContinuousOn G (U ×ˢ W))
    (hJac : ∀ x ∈ U ×ˢ V, planeJacobian (fun y => F (x.1, y)) x.2 ≠ 0)
    (hInj : ∀ x ∈ U, InjOn (fun y => F (x, y)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ x ∈ U ×ˢ W, F (x.1, G x) = x.2) :
    SmoothDirections (U ×ˢ W) G := by
  let H : (E × PolarPoint) × PolarPoint → PolarPoint := fun x => F (x.1.1, x.2) - x.1.2
  let L : ((E × PolarPoint) × PolarPoint) →L[ℝ] E × PolarPoint :=
    ((ContinuousLinearMap.fst ℝ E PolarPoint).comp
      (ContinuousLinearMap.fst ℝ (E × PolarPoint) PolarPoint)).prod
      (ContinuousLinearMap.snd ℝ (E × PolarPoint) PolarPoint)
  let R : ((E × PolarPoint) × PolarPoint) →L[ℝ] PolarPoint :=
    (ContinuousLinearMap.snd ℝ E PolarPoint).comp
      (ContinuousLinearMap.fst ℝ (E × PolarPoint) PolarPoint)
  let JF := J.compLinear L ((hU.prod hW).prod hV)
    (fun x hx => ⟨hx.1.1, hx.2⟩)
  let JR := smoothDirectionsLinearOn R ((hU.prod hW).prod hV)
  let S : (PolarPoint × PolarPoint) →L[ℝ] PolarPoint :=
    ContinuousLinearMap.fst ℝ PolarPoint PolarPoint -
      ContinuousLinearMap.snd ℝ PolarPoint PolarPoint
  let JH : SmoothDirections ((U ×ˢ W) ×ˢ V) H :=
    (smoothDirections_postcompCLM (smoothDirectionsProd JF JR) S).congrOn
      (fun _ _ => rfl)
  have hD : ∀ x ∈ U ×ˢ W,
      (fderiv ℝ (fun y => H (x, y)) (G x)).IsInvertible := by
    intro x hx
    let B : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ (fun y => F (x.1, y)) (G x)
    have hj : B.det ≠ 0 := by
      simpa only [B, planeJacobian_eq_fderiv_det] using
        hJac (x.1, G x) ⟨hx.1, hMaps hx⟩
    have hb : B.IsInvertible := by
      let e : PolarPoint ≃L[ℝ] PolarPoint := B.toContinuousLinearEquivOfDetNeZero hj
      exact ⟨e, by simp only [e, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]⟩
    have hsp := smoothDirections_contDiffOn_finiteAffine J (x.1, (0 : PolarPoint))
      (ContinuousLinearMap.inr ℝ E PolarPoint)
    have hp : (x.1, (0 : PolarPoint)) +
        (ContinuousLinearMap.inr ℝ E PolarPoint) (G x) ∈ U ×ˢ V := by
      simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
        (show (x.1, G x) ∈ U ×ˢ V from ⟨hx.1, hMaps hx⟩)
    have hs : ContDiffAt ℝ ∞ (fun y => F (x.1, y)) (G x) := by
      simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
        hsp.contDiffAt ((J.open_domain.preimage
          (continuous_const.add (ContinuousLinearMap.inr ℝ E PolarPoint).continuous)).mem_nhds hp)
    have hd : fderiv ℝ (fun y => H (x, y)) (G x) = B :=
      ((hs.differentiableAt (by simp)).hasFDerivAt.sub_const x.2).fderiv
    rw [hd]
    exact hb
  apply N04NegativeGeometryImplicitJet.smoothDirections_of_invertible JH (hU.prod hW)
    hG hMaps hD (fun x hx => sub_eq_zero.mpr (hRight x hx))
  intro m x hx A
  let A₁ : (Fin m → ℝ) →L[ℝ] E := (ContinuousLinearMap.fst ℝ E PolarPoint).comp A
  let A₂ : (Fin m → ℝ) →L[ℝ] PolarPoint :=
    (ContinuousLinearMap.snd ℝ E PolarPoint).comp A
  have hs := n04NegativeGeometry_inverse_contDiffOn_finiteAffine J hU hV hW
    hJac hInj hMaps hRight x.1 A₁
  have hmem : ((0 : Fin m → ℝ), x.2) ∈
      (((fun p => x.1 + A₁ p) ⁻¹' U) ×ˢ W) := by
    simpa only [mem_prod, mem_preimage, map_zero, add_zero] using hx
  have hsAt := hs.contDiffAt
    (((hU.preimage (continuous_const.add A₁.continuous)).prod hW).mem_nhds hmem)
  have ha : ContDiffAt ℝ ∞ (fun p : Fin m → ℝ => (p, x.2 + A₂ p)) 0 :=
    contDiffAt_id.prodMk (contDiffAt_const.add A₂.contDiff.contDiffAt)
  have hsAt' : ContDiffAt ℝ ∞
      (fun z : (Fin m → ℝ) × PolarPoint => G (x.1 + A₁ z.1, z.2))
      ((fun p : Fin m → ℝ => (p, x.2 + A₂ p)) 0) := by
    simpa only [map_zero, add_zero] using hsAt
  have hc := hsAt'.comp (0 : Fin m → ℝ) ha
  change ContDiffAt ℝ ∞ (fun p : Fin m → ℝ =>
    G (x.1 + (A p).1, x.2 + (A p).2)) 0
  exact hc

end PlanarInverse
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeInverse_jointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeInverse_jointTower
