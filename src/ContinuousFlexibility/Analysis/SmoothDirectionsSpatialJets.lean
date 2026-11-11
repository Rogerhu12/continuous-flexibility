import ContinuousFlexibility.Analysis.SmoothDirectionsLocalAngularJets
import ContinuousFlexibility.Analysis.ScalarPlaneJetRegularity
import ContinuousFlexibility.Analysis.MixedDerivativeLocality

/-!
# Spatial smoothness and mixed derivatives of actual parameter jets

The input concerns only the actual spatial derivative hierarchy of the
scalar functions and local uniform seminorm estimates for their genuine
parameter towers. Local FTC proves both coordinate derivatives of every
parameter jet. The resulting hierarchy gives joint spatial smoothness
and identifies the ordinary mixed spatial derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}
  {F : ℕ → ℕ → PolarPoint → E → ℝ}

section Hierarchy

variable (J : ∀ a b p, p ∈ V → SmoothDirections U (F a b p))
  (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
  (hcont : ∀ a b x, x ∈ U → ContinuousOn (fun p => F a b p x) V)
  (hbound : ∀ a b, LocalUniformScalarJetSeminormBounds (J a b))
  (hfirst : ∀ a b p, p ∈ V → ∀ x, x ∈ U →
    HasDerivAt (fun r => F a b (r, p.2) x) (F (a + 1) b p x) p.1)
  (hsecond : ∀ a b p, p ∈ V → ∀ x, x ∈ U →
    HasDerivAt (fun θ => F a b (p.1, θ) x) (F a (b + 1) p x) p.2)

include hU hc hcont hbound hfirst in
theorem localScalarJet_spatial_hasDerivAt_fst
    (a b n : ℕ) {p : PolarPoint} (hp : p ∈ V)
    (x : E) (hx : x ∈ U) (v : Fin n → E) :
    HasDerivAt (fun r => localScalarJet (J a b) n x v (r, p.2))
      (localScalarJet (J (a + 1) b) n x v p) p.1 :=
  localScalarJet_hasDerivAt_along (J a b) (J (a + 1) b) hU hc
    (hcont a b) (hcont (a + 1) b) (hbound a b) (hbound (a + 1) b)
    (fun r => (r, p.2)) (continuous_id.prodMk continuous_const)
    (fun r hr z hz => hfirst a b (r, p.2) hr z hz) n hp x hx v

include hU hc hcont hbound hsecond in
theorem localScalarJet_spatial_hasDerivAt_snd
    (a b n : ℕ) {p : PolarPoint} (hp : p ∈ V)
    (x : E) (hx : x ∈ U) (v : Fin n → E) :
    HasDerivAt (fun θ => localScalarJet (J a b) n x v (p.1, θ))
      (localScalarJet (J a (b + 1)) n x v p) p.2 :=
  localScalarJet_hasDerivAt_along (J a b) (J a (b + 1)) hU hc
    (hcont a b) (hcont a (b + 1)) (hbound a b) (hbound a (b + 1))
    (fun θ => (p.1, θ)) (continuous_const.prodMk continuous_id)
    (fun θ hθ z hz => hsecond a b (p.1, θ) hθ z hz) n hp x hx v

include hU hc hV hcont hbound hfirst hsecond in
theorem localScalarJet_spatial_contDiffOn
    (a b n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    ContDiffOn ℝ ∞ (localScalarJet (J a b) n x v) V := by
  exact scalarPlane_jetHierarchy_contDiffOn (fun i j => localScalarJet (J i j) n x v)
    hV (fun i j => localScalarJet_continuousOn_of_local_uniform_bounds
      (J i j) hU hc (hcont i j) (hbound i j) n x hx v)
    (fun i j p hp => localScalarJet_spatial_hasDerivAt_fst J hU hc hcont hbound hfirst
      i j n hp x hx v)
    (fun i j p hp => localScalarJet_spatial_hasDerivAt_snd J hU hc hcont hbound hsecond
      i j n hp x hx v) a b

end Hierarchy

private theorem iteratedDeriv_eq_of_local_hierarchy
    {W : Set ℝ} (hW : IsOpen W) (G : ℕ → ℝ → ℝ)
    (hD : ∀ n t, t ∈ W → HasDerivAt (G n) (G (n + 1) t) t)
    (n : ℕ) {t : ℝ} (ht : t ∈ W) :
    iteratedDeriv n (G 0) t = G n t := by
  induction n generalizing t with
  | zero => simp only [iteratedDeriv_zero, id_eq]
  | succ n ih =>
      have heq : iteratedDeriv n (G 0) =ᶠ[𝓝 t] G n := by
        filter_upwards [hW.mem_nhds ht] with r hr
        exact ih hr
      rw [iteratedDeriv_succ, heq.deriv_eq]
      exact (hD n t ht).deriv

theorem mixedDerivative_eq_of_coordinate_hierarchy
    (G : ℕ → ℕ → PolarPoint → ℝ) (hV : IsOpen V)
    (hfirst : ∀ a b p, p ∈ V →
      HasDerivAt (fun r => G a b (r, p.2)) (G (a + 1) b p) p.1)
    (hsecond : ∀ a b p, p ∈ V →
      HasDerivAt (fun θ => G a b (p.1, θ)) (G a (b + 1) p) p.2)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    mixedDerivative a b (G 0 0) p = G a b p := by
  have hnear : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  have heq : (fun r => iteratedDeriv b (fun θ => G 0 0 (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => G 0 b (r, p.2)) := by
    filter_upwards [hnear] with r hr
    exact iteratedDeriv_eq_of_local_hierarchy
      (hV.preimage (continuous_const.prodMk continuous_id))
      (fun j θ => G 0 j (r, θ)) (fun j θ hθ => hsecond 0 j (r, θ) hθ) b hr
  unfold mixedDerivative
  rw [heq.iteratedDeriv_eq a]
  exact iteratedDeriv_eq_of_local_hierarchy
    (hV.preimage (continuous_id.prodMk continuous_const))
    (fun i r => G i b (r, p.2)) (fun i r hr => hfirst i b (r, p.2) hr) a hp

theorem localScalarJet_spatial_mixedDerivative
    (J : ∀ a b p, p ∈ V → SmoothDirections U (F a b p))
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hcont : ∀ a b x, x ∈ U → ContinuousOn (fun p => F a b p x) V)
    (hbound : ∀ a b, LocalUniformScalarJetSeminormBounds (J a b))
    (hfirst : ∀ a b p, p ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun r => F a b (r, p.2) x) (F (a + 1) b p x) p.1)
    (hsecond : ∀ a b p, p ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun θ => F a b (p.1, θ) x) (F a (b + 1) p x) p.2)
    (a b n : ℕ) {p : PolarPoint} (hp : p ∈ V)
    (x : E) (hx : x ∈ U) (v : Fin n → E) :
    mixedDerivative a b (localScalarJet (J 0 0) n x v) p = (J a b p hp).D n x v := by
  rw [← localScalarJet_of_mem (J a b) n x v hp]
  exact mixedDerivative_eq_of_coordinate_hierarchy (fun i j => localScalarJet (J i j) n x v)
    hV (fun i j q hq => localScalarJet_spatial_hasDerivAt_fst J hU hc hcont hbound hfirst
      i j n hq x hx v)
    (fun i j q hq => localScalarJet_spatial_hasDerivAt_snd J hU hc hcont hbound hsecond
      i j n hq x hx v) a b hp

theorem localScalarJet_spatial_line_hasDerivAt
    (J : ∀ a b p, p ∈ V → SmoothDirections U (F a b p))
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hcont : ∀ a b x, x ∈ U → ContinuousOn (fun p => F a b p x) V)
    (hbound : ∀ a b, LocalUniformScalarJetSeminormBounds (J a b))
    (hfirst : ∀ a b p, p ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun r => F a b (r, p.2) x) (F (a + 1) b p x) p.1)
    (hsecond : ∀ a b p, p ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun θ => F a b (p.1, θ) x) (F a (b + 1) p x) p.2)
    (a b n : ℕ) {p : PolarPoint} (hp : p ∈ V)
    (x w : E) {t : ℝ} (ht : x + t • w ∈ U) (v : Fin n → E) :
    HasDerivAt (fun s => mixedDerivative a b (localScalarJet (J 0 0) n (x + s • w) v) p)
      (mixedDerivative a b (localScalarJet (J 0 0) (n + 1) (x + t • w) (Fin.cons w v)) p) t := by
  rw [localScalarJet_spatial_mixedDerivative J hU hc hV hcont hbound hfirst hsecond
    a b (n + 1) hp _ ht]
  apply ((J a b p hp).hasDerivAt_line_jet x w n v ht).congr_of_eventuallyEq
  have hline : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.preimage_mem_nhds
      (hU.mem_nhds ht)
  filter_upwards [hline] with s hs
  exact localScalarJet_spatial_mixedDerivative J hU hc hV hcont hbound hfirst hsecond
    a b n hp _ hs v

end ContinuousFlexibility.Analysis
