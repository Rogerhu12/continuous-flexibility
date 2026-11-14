module

public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Homogeneous tame bounds with distinct residual, test and output spaces

The ordered second fiber jet of an actual bilinear family recovers its
value at arbitrary inputs. Applying the given smooth tame estimate at
zero fiber inputs retains a factor from each input and chooses the low
order, loss and neighborhood before both inputs.

This is the heterogeneous version of the fiber-jet argument in
ProjectiveNewtonCorrectionBounds. It is needed for Circle × Height
errors taking values in Source; those three spaces are not identified.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section FiberJets

variable {Z E G : Type*}
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [T2Space G]

private theorem heterogeneous_fiber_smul_curve (v : G) :
    HasProjectiveCurveDerivAt (fun t : ℝ => t • v) v 0 := by
  simpa only [HasProjectiveLineDerivAt, ContinuousLinearMap.id_apply, zero_add] using
    hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ G) 0 v

/-- The genuine first fiber derivative evaluates an arbitrary linear
family; continuity of that stored linear map is not an extra input. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.linearFiber_firstJet
    {U : Set Z} {A : Z → E →ₗ[ℝ] G}
    (J : SmoothDirections (U ×ˢ univ) (fun p : Z × E => A p.1 p.2))
    {z : Z} (hz : z ∈ U) (e : E) :
    J.D 1 (z, 0) (Fin.cons (0, e) Fin.elim0) = A z e := by
  have hd := J.derivative 0 (z, 0) ⟨hz, mem_univ _⟩ Fin.elim0 (0, e)
  have he : (fun t : ℝ => J.D 0 ((z, 0) + t • ((0, e) : Z × E)) Fin.elim0) =
      (fun t : ℝ => t • A z e) := by
    funext t
    have hp : (z, 0) + t • ((0, e) : Z × E) = (z, t • e) := by
      change (z + t • (0 : Z), (0 : E) + t • e) = _
      simp only [smul_zero, add_zero, zero_add]
    rw [hp]
    simpa only [map_smul] using J.zero (z, t • e) ⟨hz, mem_univ _⟩
  unfold HasProjectiveLineDerivAt at hd
  rw [he] at hd
  exact hd.unique (heterogeneous_fiber_smul_curve (A z e))

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The ordered second jet has one direction from each actual fiber.
All three fiber/output spaces may be different. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.bilinearFiber_secondJet
    {U : Set Z} {A : Z → E →ₗ[ℝ] F →ₗ[ℝ] G}
    (J : SmoothDirections ((U ×ˢ univ) ×ˢ univ)
      (fun p : (Z × E) × F => A p.1.1 p.1.2 p.2))
    {z : Z} (hz : z ∈ U) (e : E) (f : F) :
    J.D 2 ((z, 0), 0)
      (Fin.cons ((0, e), 0) (Fin.cons (0, f) Fin.elim0)) = A z e f := by
  let v : (Z × E) × F := ((0, e), 0)
  let w : (Z × E) × F := (0, f)
  have hd := J.derivative 1 ((z, 0), 0) ⟨⟨hz, mem_univ _⟩, mem_univ _⟩
    (Fin.cons w Fin.elim0) v
  have he : (fun t : ℝ => J.D 1 (((z, 0), 0) + t • v) (Fin.cons w Fin.elim0)) =
      (fun t : ℝ => t • A z e f) := by
    funext t
    have hp : ((z, 0), 0) + t • v = ((z, t • e), 0) := by
      change ((z + t • (0 : Z), (0 : E) + t • e), (0 : F) + t • (0 : F)) = _
      simp only [smul_zero, add_zero, zero_add]
    rw [hp]
    simpa only [w, LinearMap.map_smul₂] using
      J.linearFiber_firstJet (A := fun q : Z × E => A q.1 q.2)
        (z := (z, t • e)) ⟨hz, mem_univ _⟩ f
  unfold HasProjectiveLineDerivAt at hd
  rw [he] at hd
  exact hd.unique (heterogeneous_fiber_smul_curve (A z e f))

end FiberJets

/-- A single neighborhood and derivative loss control a bilinear error
homogeneously in the residual and test variables. In particular no
additive term independent of the residual is introduced. -/
theorem heterogeneousBilinear_tame_bounds_on_ball_of_smoothTame
    {Z E F G : Type*}
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [T2Space G]
    {a : ℕ → Seminorm ℝ Z} {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set Z} {A : Z → E →ₗ[ℝ] F →ₗ[ℝ] G}
    (hT : SmoothTameOn (pairGrading (pairGrading a p) q) r ((U ×ˢ univ) ×ˢ univ)
      (fun z : (Z × E) × F => A z.1.1 z.1.2 z.2))
    {z₀ : Z} (hz₀ : z₀ ∈ U) :
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ U, a base (z - z₀) < ε → ∀ e : E, ∀ f : F,
          r s (A z e f) ≤ C *
            ((1 + a (s + loss) z) * (p base e * q base f) +
              (p (s + loss) e * q base f + p base e * q (s + loss) f)) := by
  obtain ⟨J, hJ⟩ := hT
  obtain ⟨loss, base, ε, hε, hbound⟩ :=
    hJ 2 ((z₀, 0), 0) ⟨⟨hz₀, mem_univ _⟩, mem_univ _⟩
  refine ⟨loss, base, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hbound s hs
  refine ⟨C, hC, ?_⟩
  intro z hz hlow e f
  have hlow' : pairGrading (pairGrading a p) q base
      (((z, 0), 0) - ((z₀, 0), 0)) < ε := by
    change pairGrading (pairGrading a p) q base ((z - z₀, (0 : E) - 0), (0 : F) - 0) < ε
    simpa only [pairGrading, add_apply, Seminorm.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, sub_zero, map_zero, add_zero] using hlow
  let v : Fin 2 → (Z × E) × F :=
    Fin.cons ((0, e), 0) (Fin.cons (0, f) Fin.elim0)
  have hv₀ : v 0 = ((0, e), 0) := rfl
  have hv₁ : v 1 = (0, f) := rfl
  have hjet : J.D 2 ((z, 0), 0) v = A z e f := J.bilinearFiber_secondJet hz e f
  have hb := hbound ((z, 0), 0) ⟨⟨hz, mem_univ _⟩, mem_univ _⟩ hlow' v
  have he₀ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have he₁ : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simpa only [hjet, Fin.prod_univ_two, Fin.sum_univ_two, he₀, he₁, Finset.prod_singleton,
    hv₀, hv₁, pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Prod.fst_zero, Prod.snd_zero,
    map_zero, zero_add, add_zero,
    mul_comm (q (s + loss) f) (p base e)] using hb

end ContinuousFlexibility.Analysis
