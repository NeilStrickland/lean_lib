import data.fintype group_theory.group_action 
 algebra.group_power algebra.big_operators data.zmod.basic
import tactic.ring

namespace group_theory
section burnside_count

variables {G : Type*} [group G] [fintype G] [decidable_eq G]
variables {X : Type*} [fintype X] [decidable_eq X] [mul_action G X]

instance : decidable_rel (mul_action.orbit_rel G X).r := 
 begin
  dsimp[mul_action.orbit_rel],
  intros x y,
  apply_instance,
 end 

variables (G X)
def orbits := quotient (mul_action.orbit_rel G X)
variables {G X}

def orbit (x : X) : (orbits G X) :=
 @quotient.mk X (mul_action.orbit_rel G X) x

lemma orbit_act : ∀ (g : G) (x : X), orbit (g • x) = @orbit G _ _ _ X _ _ _ x := 
 λ g x, (@quotient.eq X (mul_action.orbit_rel G X) (g • x) x).mpr ⟨g,rfl⟩ 

instance : fintype (orbits G X) :=
 by { dsimp[orbits], apply_instance, }

instance : decidable_eq (orbits G X) :=
 by { dsimp[orbits], apply_instance, }

variables (G X)
structure transversal := 
(rep : (orbits G X) → X)
(actor : X → G)
(actor_prop : ∀ x, (actor x) • x = rep (orbit x))
variables {G X}

lemma orbit_rep (t : transversal G X) (y : orbits G X) :  
  orbit (t.rep y) = y := 
begin
 letI s := (mul_action.orbit_rel G X),
 rcases quotient.exists_rep y with ⟨x,e⟩,
 rw[← e],
 exact calc
  orbit (t.rep (orbit x)) = orbit ((t.actor x) • x)
   : by rw[← t.actor_prop]
  ... = orbit x : orbit_act (t.actor x) x,
end

variables (G X)
lemma transversal_exists : nonempty (transversal G X) := 
begin
 letI s := (mul_action.orbit_rel G X),
 let rep : (orbits G X) → X := quotient.out,
 have exists_actor : 
  ∀ x, ∃ g, g • x = rep (orbit x) := 
   λ x,quotient.eq.mp (quotient.out_eq (orbit x)),
 rcases (classical.skolem.mp exists_actor) with ⟨actor,actor_prop⟩,
 exact ⟨⟨rep,actor,actor_prop⟩⟩
end
variables {G X}

variable (X)
def el_fixed_points (g : G) : finset X := 
 finset.univ.filter (λ x,g • x = x)
variable {X}

lemma burnside_count :
 (fintype.card G) * (fintype.card (orbits G X)) = 
  (@finset.univ G _).sum (λ g, finset.card (el_fixed_points X g)) := 
begin 
 rcases (transversal_exists G X) with t,
 let V : G → Type* := λ g, { x : X // g • x = x },
 have V_mem : ∀ (g : G) (x : X), (x ∈ el_fixed_points X g) ↔ g • x = x := 
  λ g x,by {simp[el_fixed_points]},
 have V_card : ∀ (g : G), fintype.card (V g) = finset.card (el_fixed_points X g) := 
  λ g, by {apply fintype.subtype_card,},
 let U := Σ g, (V g),
 have U_eq : ∀ u₀ u₁ : U, u₀.fst = u₁.fst → u₀.snd.val = u₁.snd.val → u₀ = u₁ := 
  λ ⟨h₀,⟨x₀,e₀⟩⟩ ⟨h₁,⟨x₁,e₁⟩⟩ hh hx, 
   begin 
    replace hh : h₀ = h₁ := hh,
    replace hx : x₀ = x₁ := hx,
    rcases hh, congr, assumption,
   end,
 let p : G × (orbits G X) → U := 
  λ ⟨g,y⟩,⟨g * (t.actor (g • (t.rep y))),⟨g • (t.rep y),begin
   change (g * (t.actor (g • (t.rep y)))) • (g • (t.rep y)) = g • (t.rep y),
   rw[mul_smul g _ (g • (t.rep y))],
   rw[t.actor_prop,orbit_act,orbit_rep t],
  end⟩⟩,
 let q : U → G × (orbits G X) := 
  λ ⟨h,⟨x,e⟩⟩,⟨h * (t.actor x)⁻¹,orbit x⟩,
 have pq : ∀ u, p (q u) = u := 
   λ ⟨h,⟨x,e⟩⟩, begin
   let a := t.actor x,
   let g := h * a⁻¹,
   let y := orbit x,
   let x' := g • (t.rep y),
   have ex : x' = x := calc
    x' = (h * a⁻¹) • (t.rep (orbit x)) : rfl
     ... = (h * a⁻¹) • (a • x) : by rw[← t.actor_prop x]
     ... = h • x : by rw[← mul_smul,mul_assoc,mul_left_inv,mul_one]
     ... = x : e, 
   have eh : g * (t.actor x') = h := 
    by {rw[ex,mul_assoc,mul_left_inv a,mul_one],},
   apply U_eq,exact eh,exact ex,
  end,
 have qp : ∀ v : G × (orbits G X), q (p v) = v :=
   λ ⟨g,y⟩, begin
    let x := t.rep y,
    let x' := g • x,
    let a := t.actor x',
    change (prod.mk ((g * a) * a⁻¹) (orbit x')) = (prod.mk g y),
    have : orbit x' = y := by { rw[orbit_act,orbit_rep],},
    rw[this,mul_assoc,mul_right_inv,mul_one],
   end,
 exact calc
  (fintype.card G) * (fintype.card (orbits G X)) 
   = fintype.card (G × (orbits G X)) : (fintype.card_prod _ _).symm
   ... = fintype.card U : fintype.card_congr ⟨p,q,qp,pq⟩
   ... = (@finset.univ G _).sum (λ g, fintype.card (V g)) : 
          fintype.card_sigma V
   ... = (@finset.univ G _).sum (λ g, finset.card (el_fixed_points X g)) : 
          finset.sum_congr rfl (λ g _, V_card g),
end

end burnside_count
end group_theory
