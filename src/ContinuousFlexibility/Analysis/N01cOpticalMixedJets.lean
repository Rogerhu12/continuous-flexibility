import ContinuousFlexibility.Analysis.N01cOpticalSquareBounds
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Actual mixed spatial and parameter jets of an affine optical root

The mixed-coordinate theorem is local on the genuine positive domain.
No global smoothness of the totalized square root is used. The scalar
parameter is then the original continuous linear control mean.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Affine rescaling of total ordinary scalar derivatives. -/
theorem iteratedDeriv_affine_comp (f : ℝ → ℝ) (a c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => f (a + c * t)) =
      fun t => c ^ n * iteratedDeriv n f (a + c * t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [deriv_const_mul_field]
      have hd := deriv_comp_mul_left c (fun y => iteratedDeriv n f (a + y)) t
      rw [deriv_comp_const_add] at hd
      rw [hd, ← iteratedDeriv_succ, pow_succ]
      simp only [smul_eq_mul]
      ring

private theorem contDiffOn_radialIterate {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (k : ℕ) :
    ContDiffOn ℝ ∞ (radialPartial^[k] f) Ω := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro p hp
      exact (contDiffAt_radialPartial (ih.contDiffAt (hΩ.mem_nhds hp))
        (by simp)).contDiffWithinAt

private theorem mixedDerivative_radialIterate {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (k : ℕ) :
    ∀ a b : ℕ, ∀ p ∈ Ω,
      mixedDerivative a b (radialPartial^[k] f) p = mixedDerivative (a + k) b f p := by
  induction k with
  | zero => intro a b p hp; simp only [Function.iterate_zero_apply, Nat.add_zero]
  | succ k ih =>
      intro a b p hp
      rw [Function.iterate_succ_apply',
        mixedDerivative_radialPartial hΩ (contDiffOn_radialIterate hΩ hf k) a b hp,
        ih (a + 1) b p hp]
      congr 1
      omega

/-- The two scalar differentiations commute at every finite order on
their actual open smooth domain. -/
theorem iteratedDeriv_swap_of_contDiffOn
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (k n : ℕ) {t r : ℝ} (hp : (t, r) ∈ Ω) :
    iteratedDeriv k (fun u => iteratedDeriv n (fun s => f (u, s)) r) t =
      iteratedDeriv n (fun s => iteratedDeriv k (fun u => f (u, s)) t) r := by
  have hnear : ∀ᶠ s in 𝓝 r, (t, s) ∈ Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
  have he : (fun s => (radialPartial^[k] f) (t, s)) =ᶠ[𝓝 r]
      (fun s => iteratedDeriv k (fun u => f (u, s)) t) := by
    filter_upwards [hnear] with s hs
    simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using
      mixedDerivative_radialIterate hΩ hf k 0 0 (t, s) hs
  have hcomm := mixedDerivative_radialIterate hΩ hf k 0 n (t, r) hp
  have hcomm' : iteratedDeriv n (fun s => (radialPartial^[k] f) (t, s)) r =
      iteratedDeriv k (fun u => iteratedDeriv n (fun s => f (u, s)) r) t := by
    simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using hcomm
  exact hcomm'.symm.trans (he.iteratedDeriv_eq n)

def affineOpticalRoot (q₀ g : ℝ → ℝ) (p : PolarPoint) : ℝ :=
  Real.sqrt (q₀ p.2 + p.1 * g p.2)

def affineOpticalDomain (I : Set ℝ) (q₀ g : ℝ → ℝ) : Set PolarPoint :=
  {p | p.2 ∈ I ∧ 0 < q₀ p.2 + p.1 * g p.2}

theorem affineOpticalDomain_isOpen {I : Set ℝ} (hI : IsOpen I)
    {q₀ g : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I) :
    IsOpen (affineOpticalDomain I q₀ g) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hbase := (hI.preimage continuous_snd).mem_nhds hp.1
  have hfun : ContinuousAt (fun z : PolarPoint => q₀ z.2 + z.1 * g z.2) p :=
    ((hq.contDiffAt (hI.mem_nhds hp.1)).continuousAt.comp continuousAt_snd).add
      (continuousAt_fst.mul ((hg.contDiffAt (hI.mem_nhds hp.1)).continuousAt.comp continuousAt_snd))
  exact inter_mem hbase (hfun.preimage_mem_nhds (Ioi_mem_nhds hp.2))

theorem affineOpticalRoot_contDiffOn {I : Set ℝ} (hI : IsOpen I)
    {q₀ g : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I) :
    ContDiffOn ℝ ∞ (affineOpticalRoot q₀ g) (affineOpticalDomain I q₀ g) := by
  intro p hp
  exact ((((hq.contDiffAt (hI.mem_nhds hp.1)).comp p contDiffAt_snd).add
    (contDiffAt_fst.mul ((hg.contDiffAt (hI.mem_nhds hp.1)).comp p contDiffAt_snd))).sqrt
      hp.2.ne').contDiffWithinAt

def affineOpticalParameterDomain (q₀ g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {t | 0 < q₀ r + t * g r}

theorem affineOpticalParameterDomain_isOpen (q₀ g : ℝ → ℝ) (r : ℝ) :
    IsOpen (affineOpticalParameterDomain q₀ g r) :=
  isOpen_lt continuous_const (continuous_const.add (continuous_id.mul continuous_const))

theorem affineOpticalRadialJet_contDiffOn {I : Set ℝ} (hI : IsOpen I)
    {q₀ g : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I)
    (n : ℕ) (r : ℝ) (hr : r ∈ I) :
    ContDiffOn ℝ ∞ (fun t => iteratedDeriv n (fun s => affineOpticalRoot q₀ g (t, s)) r)
      (affineOpticalParameterDomain q₀ g r) := by
  have hΩ := affineOpticalDomain_isOpen hI hq hg
  have hF := affineOpticalRoot_contDiffOn hI hq hg
  intro t ht
  have hjet := (contDiffOn_mixedDerivative hΩ hF 0 n).contDiffAt
    (hΩ.mem_nhds (show (t, r) ∈ affineOpticalDomain I q₀ g from ⟨hr, ht⟩))
  have hs := hjet.comp t (contDiffAt_id.prodMk contDiffAt_const)
  simpa only [mixedDerivative, iteratedDeriv_zero] using hs.contDiffWithinAt

/-- An exact formula before multiplication by the control-mean directions. -/
theorem affineOpticalRoot_mixedDerivative
    {I : Set ℝ} (hI : IsOpen I) {q₀ g : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I)
    (k n : ℕ) {t r : ℝ} (hr : r ∈ I) (hpos : 0 < q₀ r + t * g r) :
    iteratedDeriv k (fun u => iteratedDeriv n (fun s => affineOpticalRoot q₀ g (u, s)) r) t =
      rpowJetCoefficient (1 / 2) k *
        iteratedDeriv n (fun s => (q₀ s + t * g s) ^ ((1 / 2 : ℝ) - (k : ℝ)) * g s ^ k) r := by
  rw [iteratedDeriv_swap_of_contDiffOn (affineOpticalDomain_isOpen hI hq hg)
    (affineOpticalRoot_contDiffOn hI hq hg) k n (show (t, r) ∈ _ from ⟨hr, hpos⟩)]
  have hf : (fun s => iteratedDeriv k (fun u => affineOpticalRoot q₀ g (u, s)) t) =
      (fun s => rpowJetCoefficient (1 / 2) k *
        ((q₀ s + t * g s) ^ ((1 / 2 : ℝ) - (k : ℝ)) * g s ^ k)) := by
    funext s
    have he : (fun u => affineOpticalRoot q₀ g (u, s)) =
        fun u => Real.sqrt (q₀ s + g s * u) := by funext u; simp only [affineOpticalRoot, mul_comm]
    rw [he, iteratedDeriv_affine_comp, iteratedDeriv_sqrt_eq]
    rw [mul_comm (g s) t]
    ring
  rw [hf, iteratedDeriv_const_mul_field]

section LinearMean

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The genuine tower of every radial optical-root jet after the actual
linear control evaluation. The parameter set is fixed for all orders. -/
def affineOpticalRadialJetSmoothDirections
    (L : E →L[ℝ] ℝ) {I : Set ℝ} (hI : IsOpen I) {q₀ g : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I)
    (n : ℕ) (r : ℝ) (hr : r ∈ I) {U : Set E} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < q₀ r + L x * g r) :
    SmoothDirections U (fun x => iteratedDeriv n (fun s => Real.sqrt (q₀ s + L x * g s)) r) := by
  let V := affineOpticalParameterDomain q₀ g r
  let f : ℝ → ℝ := fun t => iteratedDeriv n (fun s => affineOpticalRoot q₀ g (t, s)) r
  let J := smoothDirectionsOfJets (affineOpticalParameterDomain_isOpen q₀ g r)
    (fun k => iteratedFDeriv ℝ k f)
    (hasProjectiveJetsOn_of_contDiffOn (affineOpticalParameterDomain_isOpen q₀ g r)
      (affineOpticalRadialJet_contDiffOn hI hq hg n r hr))
  exact (smoothDirections_precompCLM J L).restrict hU (fun x hx => hpos x hx)

theorem affineOpticalRadialJetSmoothDirections_D_apply
    (L : E →L[ℝ] ℝ) {I : Set ℝ} (hI : IsOpen I) {q₀ g : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q₀ I) (hg : ContDiffOn ℝ ∞ g I)
    (n k : ℕ) (r : ℝ) (hr : r ∈ I) {U : Set E} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < q₀ r + L x * g r)
    {x : E} (hx : x ∈ U) (v : Fin k → E) :
    (affineOpticalRadialJetSmoothDirections L hI hq hg n r hr hU hpos).D k x v =
      rpowJetCoefficient (1 / 2) k *
        iteratedDeriv n (fun s => (q₀ s + L x * g s) ^ ((1 / 2 : ℝ) - (k : ℝ)) *
          ∏ i, L (v i) * g s) r := by
  change iteratedFDeriv ℝ k
    (fun t => iteratedDeriv n (fun s => affineOpticalRoot q₀ g (t, s)) r)
      (L x) (fun i => L (v i)) = _
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
    affineOpticalRoot_mixedDerivative hI hq hg k n hr (hpos x hx)]
  have he : (fun s => (q₀ s + L x * g s) ^ ((1 / 2 : ℝ) - (k : ℝ)) *
      ∏ i, L (v i) * g s) =
      (fun s => (∏ i, L (v i)) *
        ((q₀ s + L x * g s) ^ ((1 / 2 : ℝ) - (k : ℝ)) * g s ^ k)) := by
    funext s
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [he, iteratedDeriv_const_mul_field]
  ring

end LinearMean

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev opticalMixedStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] opticalMixedStateTopology
private abbrev opticalMixedStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] opticalMixedStateGroup
private abbrev opticalMixedStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] opticalMixedStateModule
private abbrev opticalMixedStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (opticalMixedStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] opticalMixedStateSMul

def stateJointKappaCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) : (AnnularState S × ℝ) →L[ℝ] ℝ :=
  (stateKappaCLM hS hT hRef m).comp (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ)

theorem stateJointKappaCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) (z : AnnularState S × ℝ) :
    stateJointKappaCLM hS hT hRef m z = stateKappa S z.1 m := rfl

private theorem opticalAffine_value_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) (z : AnnularState S × ℝ) :
    referenceOpticalSquare D r + stateJointKappaCLM hS hT hA.1.1 m z *
        (-controlOpticalFactor C m r) =
      -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r) := by
  rw [stateJointKappaCLM_apply, n01_stateProfile_opticalSquare_eq hA z.1 m hr]
  simp only [referenceOpticalSquare, controlOpticalFactor]
  ring

/-- Every genuine radial optical-root jet has a parameter tower on the
same positive state neighbourhood, with no change of control or state. -/
def stateOpticalRadialJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (m n : ℕ) (r : ℝ)
    (hr : r ∈ Ioo (C.left m) (C.right m))
    {U : Set (AnnularState S × ℝ)} (hU : IsOpen U)
    (hpos : ∀ z ∈ U, 0 < -deriv (stateProfile D S C z.1) r /
      (r * stateProfile D S C z.1 r)) :
    SmoothDirections U (fun z => iteratedDeriv n
      (fun s => Real.sqrt (-deriv (stateProfile D S C z.1) s /
        (s * stateProfile D S C z.1 s))) r) := by
  have hD := hA.1.1.choose_spec.1
  have hC := hA.2.2.1
  have hq : ContDiffOn ℝ ∞ (referenceOpticalSquare D) (Ioo (C.left m) (C.right m)) :=
    fun s hs => (referenceOpticalSquare_contDiffAt hD
      ⟨(hC.1 m).1.trans hs.1, hs.2.trans (hC.1 m).2.2⟩).contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ (fun s => -controlOpticalFactor C m s)
      (Ioo (C.left m) (C.right m)) :=
    fun s hs => (controlOpticalFactor_contDiffAt hD hC m hs).neg.contDiffWithinAt
  let J := affineOpticalRadialJetSmoothDirections (stateJointKappaCLM hS hT hA.1.1 m)
    isOpen_Ioo hq hg n r hr hU
    (fun z hz => (opticalAffine_value_eq hS hT hA m hr z).symm ▸ hpos z hz)
  refine J.congr (fun z _ => ?_)
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  exact congrArg Real.sqrt (opticalAffine_value_eq hS hT hA m hs z)

theorem stateOpticalRadialJetSmoothDirections_D_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (m n k : ℕ) (r : ℝ)
    (hr : r ∈ Ioo (C.left m) (C.right m))
    {U : Set (AnnularState S × ℝ)} (hU : IsOpen U)
    (hpos : ∀ z ∈ U, 0 < -deriv (stateProfile D S C z.1) r /
      (r * stateProfile D S C z.1 r))
    {z : AnnularState S × ℝ} (hz : z ∈ U) (v : Fin k → AnnularState S × ℝ) :
    (stateOpticalRadialJetSmoothDirections hS hT hA m n r hr hU hpos).D k z v =
      rpowJetCoefficient (1 / 2) k *
        iteratedDeriv n (fun s =>
          (referenceOpticalSquare D s - stateKappa S z.1 m * controlOpticalFactor C m s) ^
              ((1 / 2 : ℝ) - (k : ℝ)) *
            ∏ i, -stateKappa S (v i).1 m * controlOpticalFactor C m s) r := by
  change (affineOpticalRadialJetSmoothDirections
    (stateJointKappaCLM hS hT hA.1.1 m) isOpen_Ioo _ _ n r hr hU _).D k z v = _
  rw [affineOpticalRadialJetSmoothDirections_D_apply _ _ _ _ n k r hr hU _ hz v]
  simp only [stateJointKappaCLM_apply, mul_neg, add_neg_eq_sub, neg_mul]

end ContinuousFlexibility.Statements
