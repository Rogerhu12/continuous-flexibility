import ContinuousFlexibility.Analysis.Graded
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Genuine curve and line derivatives in projective Fréchet spaces

The derivative is a difference-quotient limit in the actual target
topology. For a compatible Banach projective limit, this is equivalent to
the genuine `HasDerivAt` statement in every Banach coordinate. No norm is
imposed on the projective limit.

We prove uniqueness, continuity, elementary closure, continuous linear
pre/post composition, scalar curve reparametrization, and assembly from
genuine Banach-level derivatives. These do not give a general nonlinear
Bastiani chain rule from mere existence of line derivatives. Joint
continuity of the derivative in the base point and direction remains a
separate hypothesis in the eventual nonlinear calculus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section ActualLimits

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The actual difference-quotient limit in the original target topology. -/
def HasProjectiveCurveDerivAt (c : ℝ → F) (dc : F) (t : ℝ) : Prop :=
  Tendsto (fun h : ℝ => h⁻¹ • (c (t + h) - c t)) (𝓝[≠] (0 : ℝ)) (𝓝 dc)

/-- The actual derivative along a real affine line, with its full
topological target rather than a selected Banach completion. -/
def HasProjectiveLineDerivAt {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → F) (df : F) (x v : V) : Prop :=
  HasProjectiveCurveDerivAt (fun t : ℝ => f (x + t • v)) df 0

theorem HasProjectiveCurveDerivAt.unique [T2Space F] {c : ℝ → F} {dc ec : F} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (he : HasProjectiveCurveDerivAt c ec t) : dc = ec :=
  tendsto_nhds_unique hc he

theorem HasProjectiveLineDerivAt.unique {V : Type*} [AddCommGroup V] [Module ℝ V]
    [T2Space F] {f : V → F} {df ef : F} {x v : V}
    (hf : HasProjectiveLineDerivAt f df x v) (he : HasProjectiveLineDerivAt f ef x v) : df = ef :=
  HasProjectiveCurveDerivAt.unique hf he

theorem hasProjectiveCurveDerivAt_const (a : F) (t : ℝ) :
    HasProjectiveCurveDerivAt (fun _ : ℝ => a) 0 t := by
  simpa only [HasProjectiveCurveDerivAt, sub_self, smul_zero] using
    (tendsto_const_nhds (x := (0 : F)) :
      Tendsto (fun _ : ℝ => (0 : F)) (𝓝[≠] (0 : ℝ)) (𝓝 0))

theorem hasProjectiveLineDerivAt_const {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : F) (x v : V) : HasProjectiveLineDerivAt (fun _ : V => a) 0 x v :=
  hasProjectiveCurveDerivAt_const a 0

theorem hasProjectiveLineDerivAt_zero_direction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → F) (x : V) : HasProjectiveLineDerivAt f 0 x 0 := by
  simpa only [HasProjectiveLineDerivAt, smul_zero, add_zero] using
    hasProjectiveCurveDerivAt_const (f x) 0

theorem HasProjectiveCurveDerivAt.add [IsTopologicalAddGroup F]
    {c e : ℝ → F} {dc de : F} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (he : HasProjectiveCurveDerivAt e de t) :
    HasProjectiveCurveDerivAt (fun s => c s + e s) (dc + de) t := by
  unfold HasProjectiveCurveDerivAt at hc he ⊢
  simpa only [add_sub_add_comm, smul_add] using hc.add he

theorem HasProjectiveCurveDerivAt.const_smul [ContinuousSMul ℝ F]
    {c : ℝ → F} {dc : F} {t : ℝ} (hc : HasProjectiveCurveDerivAt c dc t) (a : ℝ) :
    HasProjectiveCurveDerivAt (fun s => a • c s) (a • dc) t := by
  unfold HasProjectiveCurveDerivAt at hc ⊢
  apply (hc.const_smul a).congr'
  exact Eventually.of_forall (fun h => by
    change a • (h⁻¹ • (c (t + h) - c t)) = h⁻¹ • (a • c (t + h) - a • c t)
    rw [← smul_sub, smul_comm])

theorem HasProjectiveLineDerivAt.add {V : Type*} [AddCommGroup V] [Module ℝ V]
    [IsTopologicalAddGroup F] {f g : V → F} {df dg : F} {x v : V}
    (hf : HasProjectiveLineDerivAt f df x v) (hg : HasProjectiveLineDerivAt g dg x v) :
    HasProjectiveLineDerivAt (fun y => f y + g y) (df + dg) x v :=
  HasProjectiveCurveDerivAt.add hf hg

theorem HasProjectiveLineDerivAt.const_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    [ContinuousSMul ℝ F] {f : V → F} {df : F} {x v : V}
    (hf : HasProjectiveLineDerivAt f df x v) (a : ℝ) :
    HasProjectiveLineDerivAt (fun y => a • f y) (a • df) x v :=
  HasProjectiveCurveDerivAt.const_smul hf a

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- Continuous linear post composition transports the actual quotient
limit, without assuming that the target is normable. -/
theorem HasProjectiveCurveDerivAt.clm_comp {c : ℝ → F} {dc : F} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (L : F →L[ℝ] G) :
    HasProjectiveCurveDerivAt (fun s => L (c s)) (L dc) t := by
  unfold HasProjectiveCurveDerivAt at hc ⊢
  simpa only [Function.comp_def, map_smul, map_sub] using (L.continuous.tendsto dc).comp hc

theorem HasProjectiveLineDerivAt.clm_comp {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f : V → F} {df : F} {x v : V}
    (hf : HasProjectiveLineDerivAt f df x v) (L : F →L[ℝ] G) :
    HasProjectiveLineDerivAt (fun y => L (f y)) (L df) x v :=
  HasProjectiveCurveDerivAt.clm_comp hf L

/-- Linear pre composition follows from the exact affine-line identity;
it is a genuine special chain rule rather than a nonlinear assertion. -/
theorem HasProjectiveLineDerivAt.comp_linear {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {f : W → F} (L : V →ₗ[ℝ] W) {df : F} {x v : V}
    (hf : HasProjectiveLineDerivAt f df (L x) (L v)) :
    HasProjectiveLineDerivAt (fun y => f (L y)) df x v := by
  simpa only [HasProjectiveLineDerivAt, map_add, map_smul] using hf

theorem hasProjectiveLineDerivAt_clm {V : Type*} [TopologicalSpace V]
    [AddCommGroup V] [Module ℝ V] (L : V →L[ℝ] F) (x v : V) :
    HasProjectiveLineDerivAt L (L v) x v := by
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := L v) :
    Tendsto (fun _ : ℝ => L v) (𝓝[≠] (0 : ℝ)) (𝓝 (L v))).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  simp only [map_add, map_smul, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- For a genuine continuous linear map, the actual directional
derivative is jointly continuous in base point and direction. -/
theorem continuous_clm_projective_direction {V : Type*} [TopologicalSpace V]
    [AddCommGroup V] [Module ℝ V] (L : V →L[ℝ] F) :
    Continuous (fun p : V × V => L p.2) := L.continuous.comp continuous_snd

end ActualLimits

section ProjectiveLevels

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
variable {bond : ∀ n, E (n + 1) →L[ℝ] E n}

/-- The real quotient limit in the Fréchet target is equivalent to actual
one-dimensional Banach derivatives at every level. -/
theorem hasProjectiveCurveDerivAt_iff_levels (c : ℝ → ProjectiveLimit E bond)
    (dc : ProjectiveLimit E bond) (t : ℝ) :
    HasProjectiveCurveDerivAt c dc t ↔
      ∀ n, HasDerivAt (fun s => (c s).1 n) (dc.1 n) t := by
  unfold HasProjectiveCurveDerivAt
  rw [tendsto_projectiveLimit_iff]
  constructor
  · intro h n
    exact hasDerivAt_iff_tendsto_slope_zero.mpr (h n)
  · intro h n
    exact hasDerivAt_iff_tendsto_slope_zero.mp (h n)

theorem hasProjectiveLineDerivAt_iff_levels {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → ProjectiveLimit E bond) (df : ProjectiveLimit E bond) (x v : V) :
    HasProjectiveLineDerivAt f df x v ↔
      ∀ n, HasDerivAt (fun t : ℝ => (f (x + t • v)).1 n) (df.1 n) 0 :=
  hasProjectiveCurveDerivAt_iff_levels _ _ _

/-- The actual real derivative of each Banach projection of the affine
line in the nonnormable projective space. -/
theorem hasDerivAt_projectiveAffineLine (x v : ProjectiveLimit E bond) (n : ℕ) :
    HasDerivAt (fun t : ℝ => (x + t • v).1 n) (v.1 n) 0 :=
  ((hasProjectiveLineDerivAt_iff_levels (ContinuousLinearMap.id ℝ (ProjectiveLimit E bond))
    v x v).mp (hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ (ProjectiveLimit E bond))
      x v)) n

/-- Real curve differentiability in the projective topology implies real
curve continuity in that same topology. -/
theorem HasProjectiveCurveDerivAt.continuousAt {c : ℝ → ProjectiveLimit E bond}
    {dc : ProjectiveLimit E bond} {t : ℝ} (hc : HasProjectiveCurveDerivAt c dc t) :
    ContinuousAt c t := by
  rw [ContinuousAt, tendsto_projectiveLimit_iff]
  exact fun n => ((hasProjectiveCurveDerivAt_iff_levels c dc t).mp hc n).continuousAt

/-- Joint continuity of a derivative map is checked in all actual Banach
coordinates, with both variables kept together in the source topology. -/
theorem continuous_projective_map_iff_levels {V : Type*} [TopologicalSpace V]
    (f : V → ProjectiveLimit E bond) :
    Continuous f ↔ ∀ n, Continuous (fun x => (f x).1 n) := by
  constructor
  · intro hf n
    exact (projectiveCoordinate E bond n).continuous.comp hf
  · intro hf
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [ContinuousAt, tendsto_projectiveLimit_iff]
    exact fun n => (hf n).continuousAt

theorem continuous_projective_direction_iff_levels {V : Type*} [TopologicalSpace V]
    (D : V → V → ProjectiveLimit E bond) :
    Continuous (fun p : V × V => D p.1 p.2) ↔
      ∀ n, Continuous (fun p : V × V => (D p.1 p.2).1 n) :=
  continuous_projective_map_iff_levels _

/-- Candidate Banach derivatives are forced to satisfy the actual
bonding equations: differentiate the known compatibility identities. -/
theorem projectiveCurveDerivatives_compatible (c : ℝ → ProjectiveLimit E bond)
    (dc : ∀ n, E n) (t : ℝ) (hc : ∀ n, HasDerivAt (fun s => (c s).1 n) (dc n) t) :
    ∀ n, bond n (dc (n + 1)) = dc n := by
  intro n
  have h := (bond n).hasFDerivAt.comp_hasDerivAt t (hc (n + 1))
  have heq : (fun s => bond n ((c s).1 (n + 1))) = (fun s => (c s).1 n) :=
    funext (fun s => (c s).2 n)
  change HasDerivAt (fun s => bond n ((c s).1 (n + 1))) (bond n (dc (n + 1))) t at h
  rw [heq] at h
  exact h.unique (hc n)

/-- Assemble a genuine projective derivative; compatibility is proved
from the given actual level derivatives, rather than assumed. -/
theorem exists_projectiveCurveDerivAt_of_levels (c : ℝ → ProjectiveLimit E bond)
    (dc : ∀ n, E n) (t : ℝ) (hc : ∀ n, HasDerivAt (fun s => (c s).1 n) (dc n) t) :
    ∃ v : ProjectiveLimit E bond, (∀ n, v.1 n = dc n) ∧ HasProjectiveCurveDerivAt c v t := by
  let v : ProjectiveLimit E bond := ⟨dc, projectiveCurveDerivatives_compatible c dc t hc⟩
  exact ⟨v, fun _ => rfl, (hasProjectiveCurveDerivAt_iff_levels c v t).mpr hc⟩

theorem exists_projectiveLineDerivAt_of_levels {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → ProjectiveLimit E bond) (df : ∀ n, E n) (x v : V)
    (hf : ∀ n, HasDerivAt (fun t : ℝ => (f (x + t • v)).1 n) (df n) 0) :
    ∃ d : ProjectiveLimit E bond, (∀ n, d.1 n = df n) ∧ HasProjectiveLineDerivAt f d x v :=
  exists_projectiveCurveDerivAt_of_levels _ _ _ hf

/-- Scaling the input direction scales the actual derivative. This uses
the true real-parameter derivative rule at every Banach level. -/
theorem HasProjectiveLineDerivAt.smul_direction {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f : V → ProjectiveLimit E bond} {df : ProjectiveLimit E bond} {x v : V}
    (hf : HasProjectiveLineDerivAt f df x v) (a : ℝ) :
    HasProjectiveLineDerivAt f (a • df) x (a • v) := by
  apply (hasProjectiveLineDerivAt_iff_levels _ _ _ _).mpr
  intro n
  have hn : HasLineDerivAt ℝ (fun y => (f y).1 n) (df.1 n) x v :=
    (hasProjectiveLineDerivAt_iff_levels f df x v).mp hf n
  exact hn.smul a

/-- A true scalar reparametrization chain rule with Fréchet-valued output. -/
theorem HasProjectiveCurveDerivAt.scomp {c : ℝ → ProjectiveLimit E bond}
    {dc : ProjectiveLimit E bond} {g : ℝ → ℝ} {dg t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc (g t)) (hg : HasDerivAt g dg t) :
    HasProjectiveCurveDerivAt (fun s => c (g s)) (dg • dc) t := by
  apply (hasProjectiveCurveDerivAt_iff_levels _ _ _).mpr
  intro n
  exact ((hasProjectiveCurveDerivAt_iff_levels c dc (g t)).mp hc n).scomp t hg

end ProjectiveLevels

section BanachLevelAssembly

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
variable {X E : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
variable {bond : ∀ n, E (n + 1) →L[ℝ] E n}

/-- A usable bridge for maps with genuine Banach-level formulas. The
domain can be a nonnormable projective Fréchet space. The chosen input
projections may include a fixed derivative loss. Actual compatibility of
the resulting derivative vector is derived automatically.

This is a special factorization theorem, not a general nonlinear
Bastiani chain rule. -/
theorem exists_projectiveLineDerivAt_of_banach_factors
    (f : V → ProjectiveLimit E bond) (P : ∀ n, V →L[ℝ] X n)
    (φ : ∀ n, X n → E n) (hf : ∀ n y, (f y).1 n = φ n (P n y))
    (x v : V) (Dφ : ∀ n, X n →L[ℝ] E n)
    (hφ : ∀ n, HasFDerivAt (φ n) (Dφ n) (P n x)) :
    ∃ df : ProjectiveLimit E bond,
      (∀ n, df.1 n = Dφ n (P n v)) ∧ HasProjectiveLineDerivAt f df x v := by
  apply exists_projectiveLineDerivAt_of_levels f (fun n => Dφ n (P n v)) x v
  intro n
  have hp : HasDerivAt (fun t : ℝ => P n x + t • P n v) (P n v) 0 := by
    convert
      (hasDerivAt_const (0 : ℝ) (P n x)).add ((hasDerivAt_id (0 : ℝ)).smul_const (P n v))
        using 1
    · funext t
      rfl
    · simp
  have hφ' : HasFDerivAt (φ n) (Dφ n) (P n x + (0 : ℝ) • P n v) := by
    simpa only [zero_smul, add_zero] using hφ n
  have h := hφ'.comp_hasDerivAt 0 hp
  simp_rw [hf n, map_add, map_smul]
  exact h

end BanachLevelAssembly

end ContinuousFlexibility.Analysis
