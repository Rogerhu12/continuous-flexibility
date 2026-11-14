module

public import ContinuousFlexibility.Analysis.SmoothDirectionsJetLimits
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Assembling actual directional towers at a limit

The pointwise limits retain the multilinear identities. Equicontinuity
of the joint jet evaluations supplies continuity, and the uniform
second-line bounds identify every derivative of the limit tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {ι : Type*} {l : Filter ι} [NeBot l]

/-- A continuous pointwise limit of multilinear maps is multilinear. -/
def scalarContinuousMultilinearLimit {n : ℕ}
    (A : ι → E [×n]→L[ℝ] ℝ) (a : (Fin n → E) → ℝ)
    (ha : ∀ v, Tendsto (fun i => A i v) l (𝓝 (a v)))
    (hc : Continuous a) : E [×n]→L[ℝ] ℝ where
  toFun := a
  map_update_add' v j x y := by
    have hsum := (ha (Function.update v j x)).add (ha (Function.update v j y))
    have hsum' : Tendsto (fun i => A i (Function.update v j (x + y))) l
        (𝓝 (a (Function.update v j x) + a (Function.update v j y))) := by
      simpa only [ContinuousMultilinearMap.map_update_add] using hsum
    exact tendsto_nhds_unique (ha (Function.update v j (x + y))) hsum'
  map_update_smul' v j c x := by
    have hsmul := (ha (Function.update v j x)).const_smul c
    have hsmul' : Tendsto (fun i => A i (Function.update v j (c • x))) l
        (𝓝 (c • a (Function.update v j x))) := by
      simpa only [ContinuousMultilinearMap.map_update_smul] using hsmul
    exact tendsto_nhds_unique (ha (Function.update v j (c • x))) hsmul'
  cont := hc

/-- Local uniform bounds and equicontinuity produce a genuine smooth
directional tower for the pointwise limit, with convergence of every jet. -/
theorem exists_smoothDirections_of_equicontinuous_limits
    {U : Set E} {f : ι → E → ℝ} {g : E → ℝ}
    (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i))
    (hzero : ∀ x ∈ U, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hbound : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
        (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
        ∀ i t, |t| < δ →
          |(J i).D (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))| ≤ B)
    (hequi : ∀ n, EquicontinuousOn
      (fun i (p : E × (Fin n → E)) => (J i).D n p.1 p.2) (U ×ˢ univ)) :
    ∃ K : SmoothDirections U g, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Tendsto (fun i => (J i).D n x v) l (𝓝 (K.D n x v)) := by
  classical
  have hex := exists_tendsto_all_directional_jets J hzero hbound
  let G : ∀ n : ℕ, E → (Fin n → E) → ℝ := fun n x v =>
    if hx : x ∈ U then (hex n x hx v).choose else 0
  have hG (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
      Tendsto (fun i => (J i).D n x v) l (𝓝 (G n x v)) := by
    dsimp only [G]
    rw [dif_pos hx]
    exact (hex n x hx v).choose_spec
  have hGc (n : ℕ) :
      ContinuousOn (fun p : E × (Fin n → E) => G n p.1 p.2) (U ×ˢ univ) :=
    Filter.Tendsto.continuousOn_of_equicontinuousOn
      (fun p hp => hG n p.1 hp.1 p.2) (hequi n)
  have hGx (n : ℕ) (x : E) (hx : x ∈ U) : Continuous (G n x) :=
    (hGc n).comp_continuous (continuous_const.prodMk continuous_id)
      (fun v => ⟨hx, mem_univ v⟩)
  let D : ∀ n : ℕ, E → E [×n]→L[ℝ] ℝ := fun n x =>
    if hx : x ∈ U then scalarContinuousMultilinearLimit
      (fun i => (J i).D n x) (G n x) (hG n x hx) (hGx n x hx) else 0
  have hD (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) : D n x v = G n x v := by
    dsimp only [D]
    rw [dif_pos hx]
    rfl
  have hDzero (x : E) (hx : x ∈ U) : D 0 x Fin.elim0 = g x := by
    rw [hD 0 x hx Fin.elim0]
    apply tendsto_nhds_unique (hG 0 x hx Fin.elim0)
    simpa only [(J _).zero x hx] using hzero x hx
  have hDc (n : ℕ) :
      ContinuousOn (fun p : E × (Fin n → E) => D n p.1 p.2) (U ×ˢ univ) := by
    apply (hGc n).congr
    intro p hp
    exact hD n p.1 hp.1 p.2
  have hDd (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) :
      HasProjectiveLineDerivAt (fun y => D n y v)
        (D (n + 1) x (Fin.cons w v)) x w := by
    obtain ⟨δ, B, hδ, hB, hmem, hsecond⟩ := hbound n x hx v w
    obtain ⟨a, ha, hd⟩ := exists_tendsto_next_directional_jet J x v w
      (fun y hy => hG n y hy v) hδ hB hmem hsecond
    have ha' : a = G (n + 1) x (Fin.cons w v) :=
      tendsto_nhds_unique ha (hG (n + 1) x hx (Fin.cons w v))
    rw [ha'] at hd
    have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x + t • w ∈ U := by
      have hc : Continuous (fun t : ℝ => x + t • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      exact hc.continuousAt.eventually (hU.mem_nhds
        (by simpa only [zero_smul, add_zero] using hx))
    have heq : (fun t : ℝ => D n (x + t • w) v) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => G n (x + t • w) v) := by
      filter_upwards [hnear] with t ht
      exact hD n (x + t • w) ht v
    have hd' := hd.congr_of_eventuallyEq heq
    rw [hD (n + 1) x hx (Fin.cons w v)]
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt] using
      hasDerivAt_iff_tendsto_slope_zero.mp hd'
  refine ⟨⟨hU, D, hDzero, hDc, hDd⟩, ?_⟩
  intro n x hx v
  change Tendsto (fun i => (J i).D n x v) l (𝓝 (D n x v))
  rw [hD n x hx v]
  exact hG n x hx v

end ContinuousFlexibility.Analysis
