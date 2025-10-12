/-
Copyright (c) 2025 Colby Brown. All rights reserved.
Released under pache 2.0 license as described in the file LICENSE.
Author: Colby Brown
-/
import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Closed.Cartesian

/-!

## Main definitions
-/

universe u v

namespace CategoryTheory

open CategoryTheory Category Limits HasClassifier
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

section
variable (ε : Type u) [Category.{v} ε] [HasPullbacks ε] [HasClassifier ε]

/-- Categories with pullbacks, a terminal object, and a classifier.
We make this a separate class to help put a `CartesianMonoidalCategory` instance
on topoi with nice definitional equality properties between the terminal objects
given by the `HasPullbacks` and `HasClassifier` instances, and also the monoidal unit. -/
class HasPullbacksTerminalClassifier (ε: Type u) [Category.{v} ε] [HasPullbacks ε] [HasClassifier ε]

/-- Every category with pullbacks, a terminal object, and a classifier is cartesian monoidal. -/
instance : CartesianMonoidalCategory ε :=
  have := (HasClassifier.isTerminalΩ₀ ε).hasTerminal
  have := hasBinaryProducts_of_hasTerminal_and_pullbacks ε
  .ofChosenFiniteProducts
    (𝒯 := {
      cone := { pt := HasClassifier.Ω₀ ε, π := { app X := X.as.elim } }
      isLimit := .mkConeMorphism
        (lift := fun _ ↦ { hom := HasClassifier.χ₀ _ })
        (uniq := fun _ _ ↦ by ext; apply (HasClassifier.isTerminalΩ₀ ε).hom_ext)
    })
    (ℬ := fun _ _ ↦ Limits.getLimitCone _)

/-- A topos `ε` is a category with pullbacks, a terminal object, and a classifier, along with an
object map `P` and, to each arrow `f: B × A ⟶ Ω`, an arrow `∈ B: B × BP ⟶ Ω`, such that there is
a unique arrow `g: A ⟶ PB` making the following diagram commute.
```
    B × A --------f---------> Ω 
      |                         
    1 × g                    | |
      |                      | |
      v                       
    B × PB ------∈ B--------> Ω
```
-/
class Topos extends HasPullbacksTerminalClassifier ε where
  /-- The object map `P`. Later, we will show that this map gives a contravariant
  endofunctor `P`. -/
  P' (B : ε) : ε
  /-- The membership arrow. -/
  mem (B: ε): (B ⊗ P' B) ⟶ HasClassifier.Ω ε
  /-- The membership arrow induces a unique arrow making the diagram commute. -/
  exists_transpose {A B: ε} (f: B ⊗ A ⟶ Ω ε):
    ∃! (g: A ⟶ P' B), (B ◁ g) ≫ mem B = f

end
variable {ε : Type u} [Category.{v} ε] [HasPullbacks ε] [HasClassifier ε] [Topos ε] {A : ε}

namespace Topos

section
variable {B C : ε}

/-- The transpose of an arrow `f: B ⊗ A ⟶ Ω` is the unique arrow `g: A ⟶ P' B` making the following
diagram commute:
```
    B × A --------f---------> Ω 
      |                         
    1 × g                    | |
      |                      | |
      v                       
    B × PB ------∈ B--------> Ω
```
Furthermore, each `g: A ⟶ P' B` is the transpose of a unique `f: B ⊗ A ⟶ Ω`.
-/
def transpose {A B : ε} : (B ⊗ A ⟶ Ω ε) ≃ (A ⟶ P' B) where
  toFun f := (exists_transpose f).choose
  invFun g := B ◁ g ≫ mem B
  left_inv f := (exists_transpose f).choose_spec.left
  right_inv g := by
    have := (exists_transpose (B ◁ g ≫ mem B)).choose_spec.right g
    simp at this
    exact this.symm

@[reassoc (attr := simp)]
theorem whiskerLeft_transpose_comp_mem {f : B ⊗ A ⟶ Ω ε} :
    B ◁ transpose f ≫ mem B = f := by
  simp [transpose, (exists_transpose f).choose_spec.left]

@[simp]
theorem transpose_whiskerLeft_comp_eq_comp_transpose (f : A ⟶ P' (C ⊗ B))
    (g : B ⊗ P' (C ⊗ B) ⟶ Ω ε) : transpose (B ◁ f ≫ g) = f ≫ transpose g := by
  dsimp [transpose]
  apply (exists_transpose _).unique
  · erw [whiskerLeft_transpose_comp_mem]
  · simp [(exists_transpose _).choose_spec.left]

/-- The diagonal map, whose composition with either projection is `𝟙 B`. -/
abbrev diag (B : ε) : B ⟶ B ⊗ B := lift (𝟙 B) (𝟙 B)

/-- The equaility predicate, as in the diagram
```
      B   ------------------> ⊤ 
      |                       | 
    diag B                    | true 
      |                       | 
      v                       v
    B × B --equality_pred---> Ω.
```
Also called the "Kronecker delta". -/
def equality_pred (B : ε) : B ⊗ B ⟶ Ω ε :=
  HasClassifier.χ (lift (𝟙 B) (𝟙 B))

scoped notation "δ" => equality_pred

abbrev singleton (B : ε) := transpose (δ B)

/-- The singleton arrow is monic. ([MM92], Lemma IV.2.1) -/
@[instance]
lemma singleton.Mono (B : ε) : Mono (singleton B) where
  right_cancellation {Z} b₁ b₂ h := by
    replace h: B ◁ b₁ ≫ δ B = (B ◁ b₂) ≫ δ B := by
      apply transpose.symm.apply_eq_iff_eq.mpr at h
      simp [transpose] at h
      exact h
    let pb (b : Z ⟶ B) := PullbackCone.mk (f := diag B) (g := B ◁ b)
      (fst := b) (snd := lift b (𝟙 Z))
      (eq := by simp)
    have (b : Z ⟶ B) := IsPullback.of_isLimit <| (pb b).isLimitAux
      (lift := fun s ↦ s.snd ≫ snd _ _)
      (fac_left := fun s ↦ by simp [pb, <-whiskerLeft_snd, <-PullbackCone.condition_assoc])
      (fac_right := fun s ↦ by
        simp [pb]
        apply hom_ext
        · simp; rw [<-whiskerLeft_fst, <-whiskerLeft_snd]
          repeat rw [<-PullbackCone.condition_assoc]
          simp
        · simp)
      (uniq := fun s m h ↦ by
        rw [(by aesop: m = m ≫ lift b (𝟙 Z) ≫ snd B Z)]
        erw [<-Category.assoc, h .right])
    simp (contextual := true) at this
    replace (b: Z ⟶ B) := IsPullback.paste_horiz (this b) (isPullback_χ (diag B)).flip 
    have ⟨p, q⟩ := CartesianMonoidalCategory.hom_ext_iff.mp 
      <| IsPullback.isoIsPullback_hom_snd (Ω₀ ε) (Y := B ⊗ Z)
        (snd := lift b₁ (𝟙 Z)) (snd' := lift b₂ (𝟙 Z)) (h.subst <| this b₁) (this b₂)
    simp at q
    simpa [q] using p.symm

/-- The singelton predicate is the characteristic function of the singleton arrow.
This is also denoted as `σ_c`. -/
@[simp]
def singleton_predicate (B : ε) : P' B ⟶ Ω ε :=
  HasClassifier.χ (singleton B)

/-- The "truth of `B`" arrow is the transpose of the arrow `truth ∘ !_B`. -/
@[reducible]
def truth_of (B : ε) : Ω₀ ε ⟶ P' B :=
  transpose (fst _ _ ≫ χ₀ _ ≫ truth _)

@[instance]
def truth_of.Mono (B : ε) : Mono (truth_of B) :=
  (isTerminalΩ₀ ε).mono_from _

@[simp]
lemma singleton_comp_predicate_eq (B : ε) :
    singleton B ≫ singleton_predicate B = χ₀ B ≫ truth ε := by
  simp [HasClassifier.comm]; rfl

/-- In a topos, every mono is an equalizer [MM92]. -/
def fork_of_mono (f : A ⟶ B) [isMono : Mono f] :
    Limits.Fork (HasClassifier.χ f) (χ₀ B ≫ truth ε) :=
  Limits.Fork.ofι f (by simpa using HasClassifier.comm f)

omit [HasPullbacks ε] in
@[simp]
lemma fork_of_mono_ι (f : A ⟶ B) [Mono f] :
    (fork_of_mono f).ι = f := by simp [fork_of_mono]

/-- The arrow given by `fork_of_mono` is, in fact, an equalizer. ([MM92], Proposition IV.1.2) -/
def fork_of_mono.IsLimit (f : A ⟶ B) [Mono f] : IsLimit (fork_of_mono f) := {
  lift (s: Fork _ _) :=
    (isPullback_χ f).lift
      (h := s.π.app .zero)
      (k := χ₀ _)
      (w := by simp[s.condition])
  fac (s: Fork _ _) j := by cases j <;> simp
  uniq (s: Fork _ _) m h := by
    simp
    have := (isPullback_χ f).isLimit.existsUnique { s with
      π := {
        app
          | .left => m ≫ f
          | .right => HasClassifier.χ₀ _
          | .one => χ₀ _ ≫ truth _
        naturality j₁ j₂ f' := by
          rcases j₁ with _ | _ | _
            <;> rcases j₂ with _ | _ | _
          all_goals try simp [(by subsingleton: f' = 𝟙 _)]
          case some.left.none =>
            specialize h .one; simp at h
            simp [(by subsingleton: f' = WalkingCospan.Hom.inl), h, s.condition]
          case some.right.none =>
            simp [(by subsingleton: f' = WalkingCospan.Hom.inr)]
          all_goals nomatch f'
      }
    }
    apply this.unique <;> clear this
    all_goals
      intro j
      rcases j with _ | _ | _
      · specialize h .one; simp_all [s.condition]
      · specialize h .zero; simp_all
      · apply (HasClassifier.isTerminalΩ₀ ε).hom_ext
}

omit [HasPullbacks ε] [Topos ε] in
/-- In a topos, arrows which are both mono and epi are isomorphisms. ([MM92], Proposition IV.1.2) -/
lemma iso_of_mono_of_epi {A B : ε} (f : A ⟶ B) [is_mono : Mono f] [is_epi : Epi f] : IsIso f := by
  rw [<-fork_of_mono_ι f]
  have : Epi (fork_of_mono f).ι := by assumption
  apply Limits.isIso_limit_cone_parallelPair_of_epi (fork_of_mono.IsLimit f)

variable (B C : ε)

/-
  # The construction of exponentials
  We follow the construction in [MM92].
  The exponential is defined as the pullback of the bottom rectangle in the following diagram,
  where `v` is the `P`-transpose of `∈ (C × B)` and `u` is the `P`-transpose of `v ≫ σ_C`.
  ([MM92], IV.2.(1))
```
                  ∈_(C × B)
  C × B × P(C × B) -------> Ω
    
                 v        σ_C
  B × P(C × B) -----> PC ----> Ω

  P(C × B) -------u---------> PB 
      ^                       ^ 
      |                       |
      | m                     | truth_of
      |                       |
     C^B -------------------> ⊤.
```
-/

@[reducible]
def v : B ⊗ P' (C ⊗ B) ⟶ P' C :=
  transpose ((α_ _ _ _).inv ≫ mem (C ⊗ B))

@[reducible]
def u : P' (C ⊗ B) ⟶ P' B :=
  Topos.transpose (v B C ≫ singleton_predicate C)

@[simp]
def exp : ε := pullback (truth_of B) (u B C)

/-- The exponentiation of B on some object C, C^B. -/
def m : exp B C ⟶ P' (C ⊗ B) := pullback.snd (truth_of B) (u B C)

/- Since `m` is the pullback of a mono, it is also mono. -/
lemma m_mono : Mono (m B C) := pullback.snd_of_mono

/-!
We construct the following diagram, where the desired evaluation map is the
lift of the pullback on the far right.
```
      --------------------evaluation map, e-------------------|
      |     1 × m                    v        singleton_pred  v
  B × C^B ---------> B × P(C × B) -------> PC <-------------- C
      |                   |                |                  |
      | 1×!               | 1 × u          | σ_C              |
      |                   |                |                  |
      v                   v                v                  v
    B × ⊤ --------------> ⊤ -------------> Ω <--------------- ⊤
      |   1 × truth_of B          ∈_B              true       ^
      --------------------------------------------------------|
```
-/

@[reducible]
protected def e_defining_pullback_cone_middle : PullbackCone (mem B) (singleton_predicate C) := .mk
  (W := B ⊗ P' (C ⊗ B))
  (fst := B ◁ (u B C))
  (snd := v B C)
  (eq := by erw [whiskerLeft_transpose_comp_mem])

@[reducible]
protected def e_defining_pullback_cone_left :
    PullbackCone (B ◁ (truth_of B)) (B ◁ (u B C)) := .mk
  (W := B ⊗ exp B C)
  (fst := B ◁ (HasClassifier.χ₀ _))
  (snd := B ◁ (pullback.snd (truth_of B) (u B C)))
  (eq := by
    apply Limits.prod.hom_ext
    all_goals
      repeat rw [<-whiskerLeft_comp]
      rw [<-pullback.condition]
      simp; apply congrArg (· ≫ _)
      apply hom_ext
      · simp
      · apply (isTerminalΩ₀ _).hom_ext)

@[reducible]
protected def e_defining_pullback_cone : PullbackCone (χ (singleton C)) (truth ε) := .mk
  (W := B ⊗ exp B C)
  (fst := _ ◁ (pullback.snd _ _) ≫ v B C)
  (snd := HasClassifier.χ₀ _) <| by
    erw [Category.assoc, <-(Topos.e_defining_pullback_cone_middle B C).condition]
    erw [<-Category.assoc, <-(Topos.e_defining_pullback_cone_left B C).condition]
    simp

/-- The evaluation map `B × B^C ⟶ C`. -/
def e : B ⊗ exp B C ⟶ C :=
  (isPullback_χ (singleton C)).lift
    (Topos.e_defining_pullback_cone B C).fst
    (Topos.e_defining_pullback_cone B C).snd
    (Topos.e_defining_pullback_cone B C).condition

protected lemma e_comp_singleton_eq_defining_fst :
    e B C ≫ singleton C = (Topos.e_defining_pullback_cone B C).fst := by simp [e]

end
variable {B C : ε} (f : B ⊗ A ⟶ C)

/-- The exponential transposition map. -/
def exp_transposition : A ⟶ P' (C ⊗ B) := transpose ((α_ _ _ _).hom ≫ (C ◁ f) ≫ δ C)

lemma exp_trans_comp_eq_χ₀_comp_truth_of :
    χ₀ A ≫ truth_of B = exp_transposition f ≫ u B C := by
  let a := (α_ _ _ _).hom ≫ C ◁ f ≫ δ C
  have : a = transpose.symm (transpose a) := by simp
  dsimp [transpose] at this; subst a
  apply congrArg ((α_ _ _ _).inv ≫ ·) at this
  rw [Iso.inv_hom_id_assoc] at this
  apply congrArg transpose at this

  erw [(?_: transpose (C ◁ f ≫ δ C) = f ≫ singleton C)] at this
  swap; · apply (exists_transpose _).choose_eq_iff.mpr; simp

  erw [(?_: transpose _ = B ◁ (exp_transposition f) ≫ v B C)] at this
  · apply congrArg (· ≫ singleton_predicate C) at this
    simp only [Category.assoc, singleton_comp_predicate_eq] at this
    conv_lhs at this => calc _
      _ = χ₀ _ ≫ truth ε := by simp
    apply congrArg transpose at this
    convert this
    · apply transpose.symm_apply_eq.mp
      simp [transpose]
    · simp [u]
  · erw [whiskerLeft_transpose_comp_mem, Iso.inv_hom_id_assoc]
    apply (ExistsUnique.choose_eq_iff _).mpr
    conv_lhs =>
      conv => calc _
        _ = C ◁ (B ◁ (exp_transposition f)) ≫ (C ◁ (v B C) ≫ mem C) := by simp
      erw [whiskerLeft_transpose_comp_mem]
      rw [associator_inv_naturality_right_assoc]
      erw [whiskerLeft_transpose_comp_mem]; simp

protected abbrev exp_adjunction : A ⟶ exp B C :=
  pullback.lift (χ₀ _) (exp_transposition f) (exp_trans_comp_eq_χ₀_comp_truth_of f)

protected theorem exp_adjunction_natural : B ◁ (Topos.exp_adjunction f) ≫ (e B C) = f := by
  apply (singleton.Mono C).right_cancellation
  erw [Category.assoc, Topos.e_comp_singleton_eq_defining_fst]

  apply (exists_transpose <| _ ◁ f ≫ δ C).unique
  swap; · simp

  simp [Topos.exp_adjunction, exp_transposition]
  repeat rw [associator_inv_naturality_right_assoc]
  rw [<-whiskerLeft_comp_assoc, pullback.lift_snd, whiskerLeft_transpose_comp_mem]
  simp

protected theorem exp_adjunction_unique (g : A ⟶ exp B C) (h : f = _ ◁ g ≫ (e B C)) :
    Topos.exp_adjunction f = g := by
  apply congrArg (· ≫ singleton C) at h
  simp [e] at h
  apply congrArg transpose.symm at h
  simp[transpose] at h

  apply pullback.hom_ext
  · apply (isTerminalΩ₀ ε).hom_ext
  erw [pullback.lift_snd]
  apply (ExistsUnique.choose_eq_iff _).mpr
  simp [h]

/-- The exponential functor. -/
def exponential (B : ε) : ε ⥤ ε where
  obj C := exp B C
  map {A C} f := Topos.exp_adjunction (e B A ≫ f)
  map_id C := by
    apply pullback.hom_ext
    · apply (isTerminalΩ₀ ε).hom_ext
    simp [Topos.exp_adjunction, exp_transposition]
    apply (ExistsUnique.choose_eq_iff _).mpr
    erw [(by simp [singleton]: δ C = C ◁ (singleton C) ≫ mem C)]
    rw [<-whiskerLeft_comp_assoc, Topos.e_comp_singleton_eq_defining_fst]
    simp
  map_comp {A C D} f₁ f₂ := by
    apply pullback.hom_ext
    · apply (isTerminalΩ₀ ε).hom_ext
    simp [Topos.exp_adjunction, exp_transposition]
    apply (ExistsUnique.choose_eq_iff _).mpr
    rw [whiskerLeft_comp]
    repeat rw [Category.assoc]
    rw [whiskerLeft_transpose_comp_mem]

    have := Topos.exp_adjunction_natural (e B A ≫ f₁)

    rw [tensor_whiskerLeft]
    conv_lhs =>
      rw [Category.assoc]
      rhs; rw [Category.assoc, Iso.inv_hom_id_assoc]
      rw [<-Category.assoc]
      conv in _ ◁ _ ≫ _ ≫ _ => rw [<-whiskerLeft_comp_assoc C]
      erw [<-whiskerLeft_comp, this]
    simp

/-- The hom-set equivalence between `B ⊗ A ⟶ C` and `A ⟶ exp B C`. -/
@[simp]
def adjunction_hom_equiv (A B C : ε) : (B ⊗ A ⟶ C) ≃ (A ⟶ exp B C) where
  toFun f := Topos.exp_adjunction f
  invFun g := _ ◁ g ≫ e B C
  left_inv f := Topos.exp_adjunction_natural f
  right_inv g := Topos.exp_adjunction_unique (B ◁ g ≫ e B C) g (by simp)

/-- The adjunction of the left monoidal tensor with exponentials. -/
def exponential_right_adjunction (B : ε) : tensorLeft B ⊣ exponential B := .mkOfHomEquiv {
  homEquiv A C := adjunction_hom_equiv A B C
  homEquiv_naturality_right {A C D} f g := by
    simp
    change Topos.exp_adjunction (f ≫ g) = Topos.exp_adjunction f ≫ (exponential B).map g
    dsimp [Topos.exp_adjunction, exponential]

    apply Limits.pullback.hom_ext
    · apply (isTerminalΩ₀ _).hom_ext
    simp
    apply (ExistsUnique.choose_eq_iff _).mpr
    simp; rw [<-whiskerLeft_comp_assoc, <-Category.assoc, <-whiskerLeft_comp]
    rw [associator_inv_naturality_right]
    repeat rw [Category.assoc]
    rw [whiskerLeft_comp]
    repeat rw [Category.assoc]
    erw [whiskerLeft_transpose_comp_mem]
    simp
    rw [<-Category.assoc]; apply congrArg (· ≫ _)
    rw [<-whiskerLeft_comp]; apply congrArg (_ ◁ ·)
    change (adjunction_hom_equiv A B C).symm ((adjunction_hom_equiv A B C) f) = f
    rw [Equiv.symm_apply_apply]
}

/-- All topos are cartesian closed. -/
instance : CartesianClosed ε where
  closed B := {
    rightAdj := exponential B
    adj := exponential_right_adjunction B
  }

end Topos
end
end CategoryTheory
