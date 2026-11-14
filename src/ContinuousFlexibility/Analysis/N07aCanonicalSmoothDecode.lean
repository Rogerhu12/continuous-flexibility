module

public import ContinuousFlexibility.Analysis.N07aCanonicalPieceReconstruction
public import ContinuousFlexibility.Analysis.N07aAngularEven

/-!
# Linear decoding of the actual smooth canonical weak classes

The representative is unique on the open piece and is set to zero
outside it. Consequently the reconstruction is linear and preserves
the actual angular reflection condition of the frozen volume graph.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def n07aCanonicalSmoothSpace (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    Submodule ℝ (CanonicalL2 S K m) where
  carrier := {u | ∀ n, N07aCanonicalNormalRegular S K m u n}
  zero_mem' := n07aCanonicalNormalRegular_zero
  add_mem' := fun hu hv n => (hu n).add (hv n)
  smul_mem' := by
    intro c u hu n a ha b
    obtain ⟨v, hv⟩ := hu n a ha b
    exact ⟨c • v, hv.smul c⟩

def n07aCanonicalSmoothRepresentative (hm : K.left m < K.right m)
    (u : n07aCanonicalSmoothSpace S K m) : PolarPoint → ℝ :=
  (n07a_exists_smooth_canonicalRepresentative hm u.val u.property).choose

theorem n07aCanonicalSmoothRepresentative_properties (hm : K.left m < K.right m)
    (u : n07aCanonicalSmoothSpace S K m) :
    ContDiffOn ℝ ∞ (n07aCanonicalSmoothRepresentative hm u) (canonicalOpen S K m) ∧
      Function.Periodic (n07aCanonicalSmoothRepresentative hm u) (0, Real.pi) ∧
      n07aCanonicalSmoothRepresentative hm u =ᵐ[canonicalMeasure S K m] u.val ∧
      ∀ p, p ∉ canonicalOpen S K m → n07aCanonicalSmoothRepresentative hm u p = 0 :=
  (n07a_exists_smooth_canonicalRepresentative hm u.val u.property).choose_spec

theorem n07a_canonicalRepresentative_unique {f g : PolarPoint → ℝ}
    (hf : ContinuousOn f (canonicalOpen S K m))
    (hg : ContinuousOn g (canonicalOpen S K m))
    (hfp : Function.Periodic f (0, Real.pi)) (hgp : Function.Periodic g (0, Real.pi))
    (he : f =ᵐ[canonicalMeasure S K m] g)
    (hf0 : ∀ p, p ∉ canonicalOpen S K m → f p = 0)
    (hg0 : ∀ p, p ∉ canonicalOpen S K m → g p = 0) : f = g := by
  classical
  funext p
  by_cases hp : p ∈ canonicalOpen S K m
  · exact n07a_canonical_periodic_eqOn_of_ae_eq hf hg hfp hgp he hp
  · exact (hf0 p hp).trans (hg0 p hp).symm

/-- The smooth reconstruction is an actual linear map on the original
L² subspace with all canonical weak derivatives. -/
def n07aCanonicalSmoothDecode (hm : K.left m < K.right m) :
    n07aCanonicalSmoothSpace S K m →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := n07aCanonicalSmoothRepresentative hm
  map_add' := by
    intro u v
    have hu := n07aCanonicalSmoothRepresentative_properties hm u
    have hv := n07aCanonicalSmoothRepresentative_properties hm v
    have hs := n07aCanonicalSmoothRepresentative_properties hm (u + v)
    apply n07a_canonicalRepresentative_unique hs.1.continuousOn
      (hu.1.continuousOn.add hv.1.continuousOn) hs.2.1 (hu.2.1.add hv.2.1)
    · filter_upwards [hs.2.2.1, hu.2.2.1, hv.2.2.1, Lp.coeFn_add u.val v.val]
        with p hp hpu hpv hpa
      exact hp.trans (hpa.trans (congrArg₂ (· + ·) hpu.symm hpv.symm))
    · exact hs.2.2.2
    · intro p hp
      simp only [Pi.add_apply, hu.2.2.2 p hp, hv.2.2.2 p hp, add_zero]
  map_smul' := by
    intro c u
    have hu := n07aCanonicalSmoothRepresentative_properties hm u
    have hs := n07aCanonicalSmoothRepresentative_properties hm (c • u)
    have hcp : Function.Periodic (fun p => c * n07aCanonicalSmoothRepresentative hm u p)
        (0, Real.pi) := fun p => congrArg (c * ·) (hu.2.1 p)
    apply n07a_canonicalRepresentative_unique hs.1.continuousOn
      (continuousOn_const.mul hu.1.continuousOn) hs.2.1 hcp
    · filter_upwards [hs.2.2.1, hu.2.2.1, Lp.coeFn_smul c u.val] with p hp hpu hpc
      exact hp.trans (hpc.trans (congrArg (c * ·) hpu.symm))
    · exact hs.2.2.2
    · intro p hp
      exact (congrArg (c * ·) (hu.2.2.2 p hp)).trans (mul_zero c)

theorem n07aCanonicalSmoothRepresentative_even (hm : K.left m < K.right m)
    (u : n07aCanonicalSmoothSpace S K m)
    (heven : (fun p : PolarPoint => u.val (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] u.val) (p : PolarPoint) :
    n07aCanonicalSmoothRepresentative hm u (p.1, -p.2) =
      n07aCanonicalSmoothRepresentative hm u p := by
  let v := n07aCanonicalSmoothRepresentative hm u
  have hv := n07aCanonicalSmoothRepresentative_properties hm u
  have hrefp : Function.Periodic (fun q : PolarPoint => v (q.1, Real.pi - q.2))
      (0, Real.pi) := by
    intro q
    have h := hv.2.1 (q.1, -q.2)
    simp only [Prod.mk_add_mk, add_zero] at h
    change v (q.1 + 0, Real.pi - (q.2 + Real.pi)) = v (q.1, Real.pi - q.2)
    rw [add_zero, show Real.pi - (q.2 + Real.pi) = -q.2 by ring,
      show Real.pi - q.2 = -q.2 + Real.pi by ring]
    exact h.symm
  have hvr := (n07aAngularReflection_preserving (S := S) (K := K) m).quasiMeasurePreserving.ae_eq_comp
    hv.2.2.1
  have he : (fun q : PolarPoint => v (q.1, Real.pi - q.2)) = v := by
    apply n07a_canonicalRepresentative_unique
      (hv.1.continuousOn.comp
        (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn
        (fun _ hq => ⟨hq.1, mem_univ _⟩)) hv.1.continuousOn hrefp hv.2.1
      (hvr.trans (heven.trans hv.2.2.1.symm))
    · intro q hq
      exact hv.2.2.2 _ (fun hqr => hq ⟨hqr.1, mem_univ _⟩)
    · exact hv.2.2.2
  have h := congrFun he p
  have hp := hv.2.1 (p.1, -p.2)
  simp only [Prod.mk_add_mk, add_zero] at hp
  change v (p.1, -p.2 + Real.pi) = v (p.1, -p.2) at hp
  change v (p.1, Real.pi - p.2) = v p at h
  rw [show Real.pi - p.2 = -p.2 + Real.pi by ring, hp] at h
  exact h

end ContinuousFlexibility.Analysis
