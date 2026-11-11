import ContinuousFlexibility.Analysis.N01cVolterraMultilinear
import ContinuousFlexibility.Analysis.N01cFlowTopologicalContinuity
import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus

/-!
# Recursive continuous multilinear variations driven by a genuine speed tower

Time-indexed state-and-angle speed towers suffice: time itself is never
a direction slot. The graph of a trajectory has the identity state jet
in degree one and only its angular variation in higher degrees. At order n the current
angular jet is set to zero inside the ordered-partition composition.
Consequently the forcing uses strictly lower variations. The current
unknown solves one scalar linear Volterra equation with the actual first
angular speed jet as coefficient.

This file constructs every order as a genuine continuous multilinear map,
proves joint continuity, its zero initial value, its true time ODE and
uniqueness. Identification with state derivatives is a further theorem,
not a premise or a conclusion asserted by this construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Genuine state-and-angle towers indexed by physical time. Time is
not a direction variable. The required continuity is exactly the joint
evaluation continuity used by the Volterra integrals. -/
structure ContinuousTimeSpeedTower (U : Set E) (G : E × PolarPoint → ℝ) where
  jet : ∀ t : ℝ, SmoothDirections (U ×ˢ (univ : Set ℝ))
    (fun p : E × ℝ => G (p.1, (t, p.2)))
  continuous : ∀ n : ℕ, ContinuousOn
    (fun p : (E × PolarPoint) × (Fin n → E × ℝ) =>
      (jet p.1.2.1).D n (p.1.1, p.1.2.2) p.2)
    ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ)

def ContinuousTimeSpeedTower.D {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (n : ℕ) (p : E × PolarPoint) :
    (E × ℝ) [×n]→L[ℝ] ℝ :=
  (J.jet p.2.1).D n (p.1, p.2.2)

/-- One multilinear order with joint parameter/time/direction continuity. -/
structure ContinuousStateVariation (U : Set E) (n : ℕ) where
  value : E × ℝ → E [×n]→L[ℝ] ℝ
  continuous : ContinuousOn
    (fun p : (E × ℝ) × (Fin n → E) => value p.1 p.2)
    ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)

def zeroStateVariation (U : Set E) (n : ℕ) : ContinuousStateVariation U n where
  value := fun _ => 0
  continuous := continuousOn_const

def trajectoryZeroVariation {U : Set E} {Θ : E × ℝ → ℝ}
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) : ContinuousStateVariation U 0 where
  value := fun p => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (Θ p)
  continuous := hΘ.comp continuous_fst.continuousOn (fun p hp => hp.1)

def flowAngleInjection : ℝ →L[ℝ] (E × ℝ) :=
  ContinuousLinearMap.inr ℝ E ℝ

@[simp] theorem flowAngleInjection_apply (r : ℝ) :
    flowAngleInjection (E := E) r = (0, r) := rfl

def flowParameterIdentityJet : (n : ℕ) → E [×n]→L[ℝ] (E × ℝ)
  | 0 => 0
  | 1 => ContinuousMultilinearMap.ofSubsingleton ℝ E (E × ℝ) (0 : Fin 1)
      (ContinuousLinearMap.inl ℝ E ℝ)
  | _ + 2 => 0

def flowGraphVariationSlot (n : ℕ) (B : E [×n]→L[ℝ] ℝ) :
    E [×n]→L[ℝ] (E × ℝ) :=
  flowParameterIdentityJet n + flowAngleInjection.compContinuousMultilinearMap B

@[simp] theorem flowGraphVariationSlot_apply (n : ℕ) (B : E [×n]→L[ℝ] ℝ)
    (v : Fin n → E) :
    flowGraphVariationSlot n B v = flowParameterIdentityJet n v + (0, B v) := rfl

theorem flowGraphVariationSlot_one_zero (v : Fin 1 → E) :
    flowGraphVariationSlot 1 (0 : E [×1]→L[ℝ] ℝ) v = (v 0, 0) := by
  simp only [flowGraphVariationSlot_apply, flowParameterIdentityJet,
    ContinuousMultilinearMap.ofSubsingleton_apply_apply, ContinuousLinearMap.inl_apply,
    ContinuousMultilinearMap.zero_apply, Prod.mk_add_mk, add_zero, zero_add]

theorem flowGraphVariationSlot_succ_succ_zero (n : ℕ) :
    flowGraphVariationSlot (n + 2) (0 : E [×(n + 2)]→L[ℝ] ℝ) = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [flowGraphVariationSlot_apply, flowParameterIdentityJet,
    ContinuousMultilinearMap.zero_apply, zero_add]
  exact Prod.ext rfl rfl

theorem ContinuousStateVariation.continuous_graphSlot {U : Set E} {n : ℕ}
    (B : ContinuousStateVariation U n) :
    ContinuousOn (fun p : (E × ℝ) × (Fin n → E) =>
      flowGraphVariationSlot n (B.value p.1) p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  change ContinuousOn (fun p : (E × ℝ) × (Fin n → E) =>
    flowParameterIdentityJet n p.2 + flowAngleInjection (B.value p.1 p.2)) _
  exact ((flowParameterIdentityJet n).cont.comp continuous_snd).continuousOn.add
    (flowAngleInjection.continuous.comp_continuousOn B.continuous)

private theorem continuousOn_flowGraphVariationSlot_reindex {U : Set E} {n N : ℕ}
    (B : ContinuousStateVariation U n) (σ : Fin n → Fin N) :
    ContinuousOn (fun p : (E × ℝ) × (Fin N → E) =>
      flowGraphVariationSlot n (B.value p.1) (p.2 ∘ σ))
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  let g : ((E × ℝ) × (Fin N → E)) → ((E × ℝ) × (Fin n → E)) :=
    fun p => (p.1, fun j => p.2 (σ j))
  have hg : Continuous g :=
    continuous_fst.prodMk
      (continuous_pi (fun j => (continuous_apply (σ j)).comp continuous_snd))
  exact B.continuous_graphSlot.comp hg.continuousOn
    (fun p hp => ⟨hp.1, mem_univ _⟩)

/-- Extension by zero at the current and all higher orders. -/
def lowerStateVariation {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k) (k : ℕ) :
    ContinuousStateVariation U k :=
  if hk : k < N then B k hk else zeroStateVariation U k

theorem lowerStateVariation_of_lt {U : Set E} {N k : ℕ}
    (B : ∀ j : ℕ, j < N → ContinuousStateVariation U j) (hk : k < N) :
    lowerStateVariation B k = B k hk := by simp only [lowerStateVariation, dif_pos hk]

@[simp] theorem lowerStateVariation_self {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k) :
    lowerStateVariation B N = zeroStateVariation U N := by
  simp only [lowerStateVariation, lt_self_iff_false, dite_false]

def flowTrajectoryGraph (Θ : E × ℝ → ℝ) (p : E × ℝ) : E × PolarPoint :=
  (p.1, (p.2, Θ p))

theorem continuousOn_flowTrajectoryGraph {U : Set E} {Θ : E × ℝ → ℝ}
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) :
    ContinuousOn (flowTrajectoryGraph Θ) (U ×ˢ (univ : Set ℝ)) :=
  continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk hΘ)

def speedAlongFlowAngularJet {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (Θ : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  J.D 1 (flowTrajectoryGraph Θ p) (fun _ : Fin 1 => (0, 1))

theorem continuousOn_speedAlongFlowAngularJet {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) :
    ContinuousOn (speedAlongFlowAngularJet J Θ) (U ×ˢ (univ : Set ℝ)) :=
  (J.continuous 1).comp
    ((continuousOn_flowTrajectoryGraph hΘ).prodMk continuousOn_const)
    (fun p hp => ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩)

/-- The exact ordered-partition forcing with no current unknown among
its inputs. Its type makes the strict lower-order dependence explicit. -/
def truncatedFlowForcing {U : Set E} {G : E × PolarPoint → ℝ} {N : ℕ}
    (J : ContinuousTimeSpeedTower U G)
    (Θ : E × ℝ → ℝ) (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k)
    (p : E × ℝ) : E [×N]→L[ℝ] ℝ :=
  ∑ c : OrderedFinpartition N,
    projectivePartitionMultilinear c (J.D c.length (flowTrajectoryGraph Θ p))
      (fun i => flowGraphVariationSlot (c.partSize i)
        ((lowerStateVariation B (c.partSize i)).value p))

theorem truncatedFlowForcing_apply {U : Set E} {G : E × PolarPoint → ℝ} {N : ℕ}
    (J : ContinuousTimeSpeedTower U G)
    (Θ : E × ℝ → ℝ) (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k)
    (p : E × ℝ) (v : Fin N → E) :
    truncatedFlowForcing J Θ B p v =
      ∑ c : OrderedFinpartition N,
        J.D c.length (flowTrajectoryGraph Θ p)
          (fun i => flowGraphVariationSlot (c.partSize i)
            ((lowerStateVariation B (c.partSize i)).value p) (v ∘ c.emb i)) := by
  simp only [truncatedFlowForcing, ContinuousMultilinearMap.sum_apply,
    projectivePartitionMultilinear_apply]

private theorem continuousOn_flowPartitionTerm {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {N : ℕ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ)))
    (c : OrderedFinpartition N)
    (B : ∀ i : Fin c.length, ContinuousStateVariation U (c.partSize i)) :
    ContinuousOn (fun p : (E × ℝ) × (Fin N → E) =>
      J.D c.length (flowTrajectoryGraph Θ p.1)
        (fun i => flowGraphVariationSlot (c.partSize i) ((B i).value p.1) (p.2 ∘ c.emb i)))
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  have hbase : ContinuousOn
      (fun p : (E × ℝ) × (Fin N → E) => flowTrajectoryGraph Θ p.1)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) :=
    (continuousOn_flowTrajectoryGraph hΘ).comp
      continuous_fst.continuousOn (fun p hp => hp.1)
  have hslots : ContinuousOn
      (fun p : (E × ℝ) × (Fin N → E) =>
        fun i => flowGraphVariationSlot (c.partSize i) ((B i).value p.1) (p.2 ∘ c.emb i))
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) :=
    continuousOn_pi.mpr (fun i => continuousOn_flowGraphVariationSlot_reindex (B i) (c.emb i))
  exact (J.continuous c.length).comp (hbase.prodMk hslots)
    (fun p hp => ⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩)

theorem continuousOn_truncatedFlowForcing {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {N : ℕ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ)))
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k) :
    ContinuousOn (fun p : (E × ℝ) × (Fin N → E) => truncatedFlowForcing J Θ B p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  simp only [truncatedFlowForcing_apply]
  exact continuousOn_finsetSum Finset.univ (fun c _ =>
    continuousOn_flowPartitionTerm J hΘ c (fun i => lowerStateVariation B (c.partSize i)))

theorem truncatedFlowForcing_one {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (Θ : E × ℝ → ℝ) (B : ∀ k : ℕ, k < 1 → ContinuousStateVariation U k)
    (p : E × ℝ) (v : Fin 1 → E) :
    truncatedFlowForcing J Θ B p v =
      J.D 1 (flowTrajectoryGraph Θ p) (fun _ : Fin 1 => (v 0, 0)) := by
  rw [truncatedFlowForcing_apply, Fintype.sum_unique]
  change J.D 1 (flowTrajectoryGraph Θ p)
    (fun i : Fin 1 => flowGraphVariationSlot 1
      ((lowerStateVariation B 1).value p) (fun _ : Fin 1 => v i)) = _
  rw [lowerStateVariation_self]
  congr 1
  funext i
  rw [show i = 0 from Subsingleton.elim _ _]
  exact flowGraphVariationSlot_one_zero (fun _ => v 0)

def nextStateVariation {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (N : ℕ)
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k) :
    ContinuousStateVariation U N where
  value := volterraMultilinearMap (continuousOn_speedAlongFlowAngularJet J hΘ)
    (continuousOn_truncatedFlowForcing J hΘ B)
  continuous := continuousOn_volterraMultilinearMap
    (continuousOn_speedAlongFlowAngularJet J hΘ)
    (continuousOn_truncatedFlowForcing J hΘ B)

/-- Strong recursion constructs every order from strictly lower orders;
no map, continuity or derivative at a higher order is supplied. -/
def volterraStateVariation {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (n : ℕ) :
    ContinuousStateVariation U n :=
  match n with
  | 0 => trajectoryZeroVariation hΘ
  | n + 1 => nextStateVariation J hΘ (n + 1)
      (fun k hk => volterraStateVariation J hΘ k)
termination_by n
decreasing_by exact hk

theorem volterraStateVariation_zero_apply {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (p : E × ℝ) :
    (volterraStateVariation J hΘ 0).value p Fin.elim0 = Θ p := by
  rw [volterraStateVariation]
  rfl

theorem volterraStateVariation_succ_value {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (n : ℕ) :
    (volterraStateVariation J hΘ (n + 1)).value =
      volterraMultilinearMap (continuousOn_speedAlongFlowAngularJet J hΘ)
        (continuousOn_truncatedFlowForcing J hΘ
          (fun k _ => volterraStateVariation J hΘ k)) := by
  rw [volterraStateVariation]
  rfl

theorem volterraStateVariation_succ_initial {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (n : ℕ) {x : E} (hx : x ∈ U) :
    (volterraStateVariation J hΘ (n + 1)).value (x, 0) = 0 := by
  rw [volterraStateVariation_succ_value]
  exact volterraMultilinearMap_zero _ _ hx

theorem volterraStateVariation_hasDerivAt_time {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (n : ℕ) {x : E} (hx : x ∈ U)
    (v : Fin (n + 1) → E) (t : ℝ) :
    HasDerivAt (fun r => (volterraStateVariation J hΘ (n + 1)).value (x, r) v)
      (speedAlongFlowAngularJet J Θ (x, t) *
          (volterraStateVariation J hΘ (n + 1)).value (x, t) v +
        truncatedFlowForcing J Θ
          (fun k (_ : k < n + 1) => volterraStateVariation J hΘ k) (x, t) v) t := by
  rw [volterraStateVariation_succ_value]
  exact hasDerivAt_volterraMultilinearMap_time _ _ hx v t

theorem volterraStateVariation_succ_unique {U : Set E}
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ))) (n : ℕ) {x : E} (hx : x ∈ U)
    (v : Fin (n + 1) → E) {y : ℝ → ℝ} (hy0 : y 0 = 0)
    (hy : ∀ t, HasDerivAt y
      (speedAlongFlowAngularJet J Θ (x, t) * y t +
        truncatedFlowForcing J Θ
          (fun k (_ : k < n + 1) => volterraStateVariation J hΘ k) (x, t) v) t)
    (t : ℝ) :
    y t = (volterraStateVariation J hΘ (n + 1)).value (x, t) v := by
  rw [volterraStateVariation_succ_value]
  exact eq_volterraMultilinearMap_of_timeODE _ _ hx v hy0 hy t

end ContinuousFlexibility.Analysis
