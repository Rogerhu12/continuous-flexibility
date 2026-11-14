module

public import ContinuousFlexibility.Analysis.ScalarPlaneJetRegularity
public import ContinuousFlexibility.Analysis.SmoothDirectionsAngularJets

/-!
# Joint parameter-line and angular regularity of actual scalar towers

A genuine directional tower with genuine angular derivatives determines
an ordinary smooth function on the plane formed by one parameter line
and the angular coordinate. The parameter source keeps its original
locally convex topology throughout.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : ℕ → ℝ → E → ℝ}

theorem angularTower_affineLine_contDiffOn
    (J : ∀ b θ, SmoothDirections U (f b θ)) (hU : IsOpen U)
    (hjoint : ∀ k b,
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) => (J b p.1).D k p.2.1 p.2.2)
        (univ ×ˢ (U ×ˢ univ)))
    (hangular : ∀ k b θ y, y ∈ U → ∀ v : Fin k → E,
      HasDerivAt (fun ψ => (J b ψ).D k y v) ((J (b + 1) θ).D k y v) θ)
    (x w : E) (b : ℕ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => f b p.2 (x + p.1 • w))
      {p : PolarPoint | x + p.1 • w ∈ U} := by
  let V : Set PolarPoint := {p | x + p.1 • w ∈ U}
  have hV : IsOpen V :=
    hU.preimage (continuous_const.add (continuous_fst.smul continuous_const))
  let F (a b : ℕ) (p : PolarPoint) : ℝ :=
    (J b p.2).D a (x + p.1 • w) (fun _ : Fin a => w)
  have hcont (a b : ℕ) : ContinuousOn (F a b) V := by
    have hmap : Continuous
        (fun p : PolarPoint => (p.2, (x + p.1 • w, fun _ : Fin a => w))) :=
      continuous_snd.prodMk
        ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk continuous_const)
    have h : ContinuousOn
        ((fun p : ℝ × (E × (Fin a → E)) => (J b p.1).D a p.2.1 p.2.2) ∘
          (fun p : PolarPoint => (p.2, (x + p.1 • w, fun _ : Fin a => w)))) V :=
      (hjoint a b).comp hmap.continuousOn
        (fun p hp => ⟨mem_univ _, hp, mem_univ _⟩)
    apply h.congr
    intro p hp
    rfl
  have hfirst (a b : ℕ) (p : PolarPoint) (hp : p ∈ V) :
      HasDerivAt (fun t => F a b (t, p.2)) (F (a + 1) b p) p.1 := by
    have hvec : Fin.cons w (fun _ : Fin a => w) = (fun _ : Fin (a + 1) => w) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simpa only [F, hvec] using
      (J b p.2).hasDerivAt_line_jet x w a (fun _ => w) hp
  have hsecond (a b : ℕ) (p : PolarPoint) (hp : p ∈ V) :
      HasDerivAt (fun t => F a b (p.1, t)) (F a (b + 1) p) p.2 := by
    exact hangular a b p.2 (x + p.1 • w) hp (fun _ => w)
  apply (scalarPlane_jetHierarchy_contDiffOn F hV hcont hfirst hsecond 0 b).congr
  intro p hp
  have hv : (fun _ : Fin 0 => w) = Fin.elim0 := Subsingleton.elim _ _
  dsimp only [F]
  rw [hv]
  exact ((J b p.2).zero (x + p.1 • w) hp).symm

end ContinuousFlexibility.Analysis

