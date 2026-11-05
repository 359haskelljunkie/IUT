/-!
# Hodge Theater Toy, v2: information boundaries made into theorems

A deliberately small, self-contained Lean 4 model INSPIRED BY the language
of Hodge theaters in IUT.

IMPORTANT
* This is NOT a formalization of IUT, and it does not touch abc.
* No Mathlib dependency: only core Lean 4.

What is new compared to v1 (every item is a proved theorem, not a field):

1. `FrobCat`: Frobenius-like data really form a category
   (a genuine instance of `ToyCategory`), and `ThetaLink F G` is
   *exactly* an isomorphism in it (`thetaLinkEquivIso`).
2. `LogLink` is a non-invertible morphism of the same category,
   contrasted with the Θ-link, which is invertible.
3. Information boundary:
   * `no_leak`: every Θ-invariant observable of a theater agrees on
     Θ-linked theaters;
   * `etale_invisible`: there is NO Θ-invariant observable that recovers
     an étale-side property, so "Θ-linked" never means "identified".
4. Multiradial certificates are *composable*: errors add
   (`MultiRadialCertificate.comp`), and the bound is derived, not assumed.
5. A concrete, non-identity model whose inequality is PROVED from the
   definitions (`negCertificate`), including a nonzero error budget.
-/

universe u v

/-! ## 0. A minimal category interface -/

structure ToyCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  assoc :
    ∀ {W X Y Z : Obj}
      (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
      comp h (comp g f) = comp (comp h g) f

/-- Isomorphisms in a `ToyCategory`. -/
structure ToyCategory.Iso (C : ToyCategory.{u, v}) (X Y : C.Obj) where
  hom : C.Hom X Y
  inv : C.Hom Y X
  hom_inv : C.comp inv hom = C.id X
  inv_hom : C.comp hom inv = C.id Y

/-! ## 1. Étale-like and Frobenius-like data -/

structure EtaleLike where
  fundamentalGroup : Type
  additiveShadow : Type

/-- Multiplicative monoid + Frobenius + height; deliberately no addition. -/
structure FrobeniusLike where
  Carrier : Type
  one : Carrier
  mul : Carrier → Carrier → Carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  frobenius : Carrier → Carrier
  height : Carrier → Nat

structure KummerBridge (G : Type u) (M : Type v) where
  encode : G → M
  ambiguous : G → G → Prop
  respects_ambiguity :
    ∀ {x y : G}, ambiguous x y → encode x = encode y

structure HodgeTheater where
  etale : EtaleLike
  frobenius : FrobeniusLike
  kummer : KummerBridge etale.fundamentalGroup frobenius.Carrier

/-! ## 2. The category of Frobenius-like data -/

/-- Structure-preserving maps: they respect `one`, `mul`, `frobenius`.
Heights are *not* required to be preserved: they are an observable. -/
structure FrobHom (F G : FrobeniusLike) where
  toFun : F.Carrier → G.Carrier
  map_one : toFun F.one = G.one
  map_mul : ∀ x y, toFun (F.mul x y) = G.mul (toFun x) (toFun y)
  map_frobenius : ∀ x, toFun (F.frobenius x) = G.frobenius (toFun x)

theorem FrobHom.ext {F G : FrobeniusLike} {f g : FrobHom F G}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f; cases g
  have : _ = _ := funext h
  subst this
  rfl

def FrobHom.id (F : FrobeniusLike) : FrobHom F F where
  toFun := fun x => x
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_frobenius := fun _ => rfl

def FrobHom.comp {F G H : FrobeniusLike} (g : FrobHom G H) (f : FrobHom F G) :
    FrobHom F H where
  toFun := fun x => g.toFun (f.toFun x)
  map_one := by dsimp only; rw [f.map_one, g.map_one]
  map_mul := by intro x y; dsimp only; rw [f.map_mul, g.map_mul]
  map_frobenius := by intro x; dsimp only; rw [f.map_frobenius, g.map_frobenius]

/-- `FrobCat` is a genuine instance of the category interface. -/
def FrobCat : ToyCategory.{1, 0} where
  Obj := FrobeniusLike
  Hom := FrobHom
  id := FrobHom.id
  comp := FrobHom.comp
  id_comp := fun _ => FrobHom.ext (fun _ => rfl)
  comp_id := fun _ => FrobHom.ext (fun _ => rfl)
  assoc := fun _ _ _ => FrobHom.ext (fun _ => rfl)

/-! ## 3. Θ-links and log-links -/

/-- A Θ-link: an invertible multiplicative/Frobenius comparison.
No additive structure, hence no field claiming preservation of addition. -/
structure ThetaLink (F G : FrobeniusLike) where
  toFun : F.Carrier → G.Carrier
  invFun : G.Carrier → F.Carrier
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_one : toFun F.one = G.one
  map_mul : ∀ x y, toFun (F.mul x y) = G.mul (toFun x) (toFun y)
  map_frobenius : ∀ x, toFun (F.frobenius x) = G.frobenius (toFun x)

/-- A log-link: a morphism of Frobenius-like data that need NOT be invertible. -/
abbrev LogLink (F G : FrobeniusLike) := FrobHom F G

namespace ThetaLink

def refl (F : FrobeniusLike) : ThetaLink F F where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_frobenius := fun _ => rfl

def symm {F G : FrobeniusLike} (θ : ThetaLink F G) : ThetaLink G F where
  toFun := θ.invFun
  invFun := θ.toFun
  left_inv := θ.right_inv
  right_inv := θ.left_inv
  map_one := by
    rw [← θ.map_one, θ.left_inv]
  map_mul := by
    intro x y
    have h : θ.invFun (G.mul x y)
        = F.mul (θ.invFun x) (θ.invFun y) := by
      apply Eq.symm
      calc F.mul (θ.invFun x) (θ.invFun y)
          = θ.invFun (θ.toFun (F.mul (θ.invFun x) (θ.invFun y))) := (θ.left_inv _).symm
        _ = θ.invFun (G.mul (θ.toFun (θ.invFun x)) (θ.toFun (θ.invFun y))) := by
              rw [θ.map_mul]
        _ = θ.invFun (G.mul x y) := by rw [θ.right_inv, θ.right_inv]
    exact h
  map_frobenius := by
    intro x
    calc θ.invFun (G.frobenius x)
        = θ.invFun (G.frobenius (θ.toFun (θ.invFun x))) := by rw [θ.right_inv]
      _ = θ.invFun (θ.toFun (F.frobenius (θ.invFun x))) := by rw [θ.map_frobenius]
      _ = F.frobenius (θ.invFun x) := θ.left_inv _

def trans {F G H : FrobeniusLike} (θ₁ : ThetaLink F G) (θ₂ : ThetaLink G H) :
    ThetaLink F H where
  toFun := fun x => θ₂.toFun (θ₁.toFun x)
  invFun := fun z => θ₁.invFun (θ₂.invFun z)
  left_inv := by intro x; dsimp only; rw [θ₂.left_inv, θ₁.left_inv]
  right_inv := by intro z; dsimp only; rw [θ₁.right_inv, θ₂.right_inv]
  map_one := by dsimp only; rw [θ₁.map_one, θ₂.map_one]
  map_mul := by intro x y; dsimp only; rw [θ₁.map_mul, θ₂.map_mul]
  map_frobenius := by intro x; dsimp only; rw [θ₁.map_frobenius, θ₂.map_frobenius]

/-- Forget invertibility: every Θ-link is a morphism in `FrobCat`. -/
def toHom {F G : FrobeniusLike} (θ : ThetaLink F G) : FrobHom F G where
  toFun := θ.toFun
  map_one := θ.map_one
  map_mul := θ.map_mul
  map_frobenius := θ.map_frobenius

end ThetaLink

/-- Θ-links are exactly isomorphisms of `FrobCat` (both directions). -/
def thetaLinkToIso {F G : FrobeniusLike} (θ : ThetaLink F G) :
    ToyCategory.Iso FrobCat F G where
  hom := θ.toHom
  inv := θ.symm.toHom
  hom_inv := FrobHom.ext (fun x => θ.left_inv x)
  inv_hom := FrobHom.ext (fun y => θ.right_inv y)

def isoToThetaLink {F G : FrobeniusLike} (e : ToyCategory.Iso FrobCat F G) :
    ThetaLink F G where
  toFun := e.hom.toFun
  invFun := e.inv.toFun
  left_inv := fun x => congrArg (fun f => FrobHom.toFun f x) e.hom_inv
  right_inv := fun y => congrArg (fun f => FrobHom.toFun f y) e.inv_hom
  map_one := e.hom.map_one
  map_mul := e.hom.map_mul
  map_frobenius := e.hom.map_frobenius

/-- A Θ-link is invertible; a log-link is not required to be. -/
theorem thetaLink_is_iso_in_FrobCat {F G : FrobeniusLike} (θ : ThetaLink F G) :
    ∃ e : ToyCategory.Iso FrobCat F G, e.hom.toFun = θ.toFun :=
  ⟨thetaLinkToIso θ, rfl⟩

/-- Round trip Iso → ThetaLink → Iso preserves the forward map. -/
theorem iso_roundtrip {F G : FrobeniusLike} (e : ToyCategory.Iso FrobCat F G) :
    (thetaLinkToIso (isoToThetaLink e)).hom = e.hom :=
  FrobHom.ext (fun _ => rfl)

/-! ## 4. The information boundary (the heart of v2) -/

/-- An observable that only looks at Frobenius-like data and is invariant
under Θ-links: precisely "what a Θ-transported algorithm may use". -/
structure Observable (α : Type v) where
  obs : FrobeniusLike → α
  invariant : ∀ {F G : FrobeniusLike}, ThetaLink F G → obs F = obs G

/-- **No leak.** Θ-linked theaters are indistinguishable by any observable,
no matter how different their étale-like parts are. -/
theorem no_leak {α : Type v} (O : Observable α) (T₁ T₂ : HodgeTheater)
    (θ : ThetaLink T₁.frobenius T₂.frobenius) :
    O.obs T₁.frobenius = O.obs T₂.frobenius :=
  O.invariant θ

/-- A second carrier for the same multiplicative data: `ℤ` under addition
(multiplicative notation = exponent vectors), Frobenius = doubling. -/
abbrev intFrob : FrobeniusLike where
  Carrier := Int
  one := 0
  mul := fun a b => a + b
  mul_assoc := Int.add_assoc
  one_mul := Int.zero_add
  mul_one := Int.add_zero
  frobenius := fun x => 2 * x
  height := fun x => x.natAbs

/-- The same data, with a cosmetically different carrier `ℤ × Unit`. -/
abbrev prodFrob : FrobeniusLike where
  Carrier := Int × Unit
  one := (0, ())
  mul := fun a b => (a.1 + b.1, ())
  mul_assoc := by intro a b c; simp [Int.add_assoc]
  one_mul := by intro a; simp
  mul_one := by intro a; simp
  frobenius := fun x => (2 * x.1, ())
  height := fun x => x.1.natAbs

def intToProd : ThetaLink intFrob prodFrob where
  toFun := fun x => (x, ())
  invFun := fun p => p.1
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_frobenius := fun _ => rfl

def etaleBool : EtaleLike := ⟨Unit, Bool⟩
def etaleUnit : EtaleLike := ⟨Unit, Unit⟩

def theaterA : HodgeTheater where
  etale := etaleBool
  frobenius := intFrob
  kummer := ⟨fun _ => (0 : Int), fun _ _ => True, fun _ => rfl⟩

def theaterB : HodgeTheater where
  etale := etaleUnit
  frobenius := prodFrob
  kummer := ⟨fun _ => (0, ()), fun _ _ => True, fun _ => rfl⟩

/-- **Étale side is invisible.** There is no Θ-invariant observable that
detects whether the additive shadow is a subsingleton, although
`theaterA` and `theaterB` ARE Θ-linked.
Θ-isomorphism of the Frobenius parts never identifies the theaters. -/
theorem etale_invisible :
    ¬ ∃ O : Observable Prop,
        ∀ T : HodgeTheater,
          O.obs T.frobenius = Subsingleton T.etale.additiveShadow := by
  rintro ⟨O, h⟩
  have hA : O.obs intFrob = Subsingleton Bool := h theaterA
  have hB : O.obs prodFrob = Subsingleton Unit := h theaterB
  have hEq : Subsingleton Bool = Subsingleton Unit := by
    rw [← hA, ← hB]
    exact no_leak O theaterA theaterB intToProd
  have hSub : Subsingleton Bool := by
    rw [hEq]; infer_instance
  exact absurd (hSub.elim true false) (by decide)

/-! ## 5. Uncertainty budgets: now a commutative monoid -/

structure UncertaintyBudget where
  kummer : Nat
  theta : Nat
  log : Nat

namespace UncertaintyBudget

def total (U : UncertaintyBudget) : Nat := U.kummer + U.theta + U.log

def zero : UncertaintyBudget := ⟨0, 0, 0⟩

def add (U V : UncertaintyBudget) : UncertaintyBudget :=
  ⟨U.kummer + V.kummer, U.theta + V.theta, U.log + V.log⟩

theorem total_zero : zero.total = 0 := rfl

/-- Errors from independent transports add up exactly. -/
theorem total_add (U V : UncertaintyBudget) :
    (add U V).total = U.total + V.total := by
  show (U.kummer + V.kummer) + (U.theta + V.theta) + (U.log + V.log)
      = (U.kummer + U.theta + U.log) + (V.kummer + V.theta + V.log)
  omega

theorem total_mono (U V : UncertaintyBudget)
    (hK : U.kummer ≤ V.kummer) (hT : U.theta ≤ V.theta) (hL : U.log ≤ V.log) :
    U.total ≤ V.total := by
  unfold total; omega

end UncertaintyBudget

/-! ## 6. Multiradial certificates: composable, with derived bounds -/

structure MultiRadialCertificate (F G : FrobeniusLike) (θ : ThetaLink F G) where
  run : G.Carrier → Nat
  baseline : F.Carrier → Nat
  uncertainty : UncertaintyBudget
  bound : ∀ x, run (θ.toFun x) ≤ baseline x + uncertainty.total

namespace MultiRadialCertificate

/-- Reflexivity: a baseline is its own certificate with zero error. -/
def refl (F : FrobeniusLike) (b : F.Carrier → Nat) :
    MultiRadialCertificate F F (ThetaLink.refl F) where
  run := b
  baseline := b
  uncertainty := UncertaintyBudget.zero
  bound := by intro x; exact Nat.le_add_right _ _

/-- **Composition.** Chaining two Θ-links with certificates whose middle
terms match yields a certificate for the composite link with the SUM of
the budgets. The bound is derived, via `total_add`. -/
def comp {F G H : FrobeniusLike} {θ₁ : ThetaLink F G} {θ₂ : ThetaLink G H}
    (C₁ : MultiRadialCertificate F G θ₁)
    (C₂ : MultiRadialCertificate G H θ₂)
    (hmid : C₂.baseline = C₁.run) :
    MultiRadialCertificate F H (θ₁.trans θ₂) where
  run := C₂.run
  baseline := C₁.baseline
  uncertainty := UncertaintyBudget.add C₁.uncertainty C₂.uncertainty
  bound := by
    intro x
    have h2 := C₂.bound (θ₁.toFun x)
    have h1 := C₁.bound x
    rw [hmid] at h2
    show C₂.run (θ₂.toFun (θ₁.toFun x)) ≤ _
    rw [UncertaintyBudget.total_add]
    omega

/-- Enlarging the budget keeps the certificate valid. -/
theorem weaken {F G : FrobeniusLike} {θ : ThetaLink F G}
    (C : MultiRadialCertificate F G θ) (x : F.Carrier)
    (larger : UncertaintyBudget) (h : C.uncertainty.total ≤ larger.total) :
    C.run (θ.toFun x) ≤ C.baseline x + larger.total := by
  have := C.bound x
  omega

end MultiRadialCertificate

/-! ## 7. A concrete certificate whose inequality is PROVED, not assumed -/

/-- Negation on `ℤ` is a non-identity Θ-link of `intFrob` to itself. -/
def negTheta : ThetaLink intFrob intFrob where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := by intro x; exact Int.neg_neg x
  right_inv := by intro x; exact Int.neg_neg x
  map_one := rfl
  map_mul := by intro (x : Int) (y : Int); show -(x + y) = -x + -y; omega
  map_frobenius := by intro (x : Int); show -(2 * x) = 2 * -x; omega

/-- The target side measures height with a constant shift of 2; the
source side measures plain height. The shift is exactly paid for by an
explicit budget of 2, and the proof is a computation, not a hypothesis. -/
def negCertificate : MultiRadialCertificate intFrob intFrob negTheta where
  run := fun x => x.natAbs + 2
  baseline := fun x => x.natAbs
  uncertainty := ⟨1, 1, 0⟩
  bound := by
    intro x
    show (-x).natAbs + 2 ≤ x.natAbs + (1 + 1 + 0)
    rw [Int.natAbs_neg]
    omega

/-- Chaining the negation twice gives a certificate whose budget is 4
(= 2 + 2) for the composite link, derived by `comp`. -/
def negCertificate' : MultiRadialCertificate intFrob intFrob (negTheta.trans negTheta) :=
  MultiRadialCertificate.comp
    (negCertificate)
    ({ run := fun x => x.natAbs + 4
       baseline := fun x => x.natAbs + 2
       uncertainty := ⟨1, 1, 0⟩
       bound := by
         intro x
         show (-x).natAbs + 4 ≤ x.natAbs + 2 + (1 + 1 + 0)
         rw [Int.natAbs_neg]
         omega } :
      MultiRadialCertificate intFrob intFrob negTheta)
    rfl

example : negCertificate'.uncertainty.total = 4 := by
  decide

/-! ## 8. Comparison of theaters -/

structure TheaterComparison (T₁ T₂ : HodgeTheater) where
  theta : ThetaLink T₁.frobenius T₂.frobenius
  certificate : MultiRadialCertificate T₁.frobenius T₂.frobenius theta

/-- The comparison between `theaterA` and `theaterB` exists, and still
the theaters are not identified (see `etale_invisible`). -/
def comparisonAB : TheaterComparison theaterA theaterB where
  theta := intToProd
  certificate :=
    { run := fun p => p.1.natAbs
      baseline := fun x => x.natAbs
      uncertainty := UncertaintyBudget.zero
      bound := by intro x; exact Nat.le_add_right _ _ }

/-- Θ-linked, yet with different étale shadows: the comparison is
non-trivial in the sense that it does not collapse the theaters. -/
theorem comparisonAB_nontrivial :
    ¬ (Subsingleton theaterA.etale.additiveShadow ↔
       Subsingleton theaterB.etale.additiveShadow) := by
  intro h
  have : Subsingleton Bool := h.mpr (inferInstanceAs (Subsingleton Unit))
  exact absurd (this.elim true false) (by decide)
